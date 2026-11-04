/* The runner of process stages (DESIGN.md, "The stage store", measurement):
 * it runs a stage's program and reports the CPU time of the processes the
 * stage ran and their peak memory, which Node's spawnSync does not report.
 *
 *   stage-runner <limit ms> <memory bytes> <program> [argument…]
 *     runs <program> with the arguments, the environment, the working
 *     directory and the standard streams it was given, in a process group
 *     of its own, led by a watchdog that kills the group when the runner
 *     ends in any way. The program's memory, its current physical footprint
 *     (on macOS, compressed and swapped pages included; on Linux, its
 *     resident set and swap), is read every POLL_MS. At the time limit,
 *     when that memory exceeds the memory limit, or on SIGTERM, SIGINT,
 *     SIGHUP or SIGQUIT, the program, by its process id, and the group are
 *     continued and signalled (SIGTERM at a limit), and killed 250 ms later. A
 *     descendant that left the group (setsid) is not signalled, nor is the
 *     program once the runner itself has died. When the program ends, what remains of its
 *     group is killed, and the runner writes to file descriptor 3, which the
 *     program does not inherit, `deadline` where the time limit expired,
 *     `memory <bytes>` where the memory limit was exceeded, with the memory
 *     read, and
 *     `cpu <user µs> <system µs> <peak bytes>`: the CPU time of the program
 *     and of every descendant it waited for, and the largest peak resident
 *     set among them (RUSAGE_CHILDREN). It then ends as the program did:
 *     the same exit status, or the same signal. A program that cannot be
 *     executed is reported as `exec <errno>`, and the runner exits with 127;
 *     a failure of the runner's own as `runner <call> <errno>`, its group
 *     killed, and the runner exits with 125.
 *   stage-runner --cpu <pid>
 *     prints `cpu <user µs> <system µs> <peak bytes>`: the CPU time process
 *     <pid> has used so far and its peak memory (on macOS its lifetime
 *     maximum physical footprint; on Linux, with its descendants, which a
 *     sandbox runs its program as, their peak resident sets summed), or
 *     exits with 1 where it is not read.
 */
#include <errno.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <time.h>
#ifdef __APPLE__
#include <libproc.h>
#include <mach/mach_time.h>
#endif

static long long micros(struct timeval t) { return (long long)t.tv_sec * 1000000 + t.tv_usec; }

#ifdef __linux__
#include <dirent.h>
/* Process `pid`'s parent; its user and system times with its waited-for
 * children's, in clock ticks; and its peak resident set (VmHWM), in kB.
 * Each output may be NULL. Returns 0, or -1 where the process is not read. */
static int proc_stat(long pid, long *parent, unsigned long long times[2], unsigned long long *hwm) {
  char path[64], line[4096];
  snprintf(path, sizeof path, "/proc/%ld/stat", pid);
  FILE *f = fopen(path, "r");
  if (!f) return -1;
  size_t n = fread(line, 1, sizeof line - 1, f);
  fclose(f);
  line[n] = '\0';
  /* The fields after the command's closing parenthesis: state, ppid, ...;
   * utime, stime, cutime and cstime are the 14th to 17th fields. */
  char *rest = strrchr(line, ')');
  long ppid;
  unsigned long long utime, stime;
  long long cutime, cstime;
  if (!rest || sscanf(rest + 1, " %*c %ld %*d %*d %*d %*d %*u %*u %*u %*u %*u %llu %llu %lld %lld",
                      &ppid, &utime, &stime, &cutime, &cstime) != 5)
    return -1;
  if (parent) *parent = ppid;
  if (times) {
    times[0] = utime + (unsigned long long)(cutime > 0 ? cutime : 0);
    times[1] = stime + (unsigned long long)(cstime > 0 ? cstime : 0);
  }
  if (hwm) {
    snprintf(path, sizeof path, "/proc/%ld/status", pid);
    f = fopen(path, "r");
    if (f) {
      while (fgets(line, sizeof line, f))
        if (sscanf(line, "VmHWM: %llu kB", hwm) == 1) break;
      fclose(f);
    }
  }
  return 0;
}
#endif

static int cpu_of(const char *text) {
  char *end;
  long pid = strtol(text, &end, 10);
  if (*text == '\0' || *end != '\0' || pid <= 0) return 2;
#ifdef __APPLE__
  struct rusage_info_v4 info;
  if (proc_pid_rusage((int)pid, RUSAGE_INFO_V4, (rusage_info_t *)&info) != 0) return 1;
  /* The times are in Mach absolute time units. */
  mach_timebase_info_data_t base;
  if (mach_timebase_info(&base) != KERN_SUCCESS) return 1;
  unsigned long long user = info.ri_user_time * base.numer / base.denom / 1000;
  unsigned long long system = info.ri_system_time * base.numer / base.denom / 1000;
  printf("cpu %llu %llu %llu\n", user, system, (unsigned long long)info.ri_lifetime_max_phys_footprint);
  return 0;
#elif defined(__linux__)
  /* The process and its descendants: a sandbox (bubblewrap) runs the
   * program it confines as a descendant. Each live process counts its own
   * times and its waited-for children's (cutime, cstime), so an ended
   * descendant counts once, through the process that waited for it. */
  unsigned long long user = 0, system = 0, peak = 0;
  long pids[4096], parents[4096];
  int count = 0;
  DIR *proc = opendir("/proc");
  if (!proc) return 1;
  struct dirent *entry;
  while ((entry = readdir(proc)) != NULL && count < 4096) {
    char *tail;
    long id = strtol(entry->d_name, &tail, 10);
    if (*entry->d_name == '\0' || *tail != '\0' || id <= 0) continue;
    long parent;
    if (proc_stat(id, &parent, NULL, NULL) == 0) {
      pids[count] = id;
      parents[count++] = parent;
    }
  }
  closedir(proc);
  long tree[4096];
  int members = 0;
  tree[members++] = pid;
  for (int i = 0; i < members; i++)
    for (int j = 0; j < count && members < 4096; j++)
      if (parents[j] == tree[i]) tree[members++] = pids[j];
  int read = 0;
  for (int i = 0; i < members; i++) {
    unsigned long long times[2], hwm = 0;
    if (proc_stat(tree[i], NULL, times, &hwm) != 0) continue;
    user += times[0];
    system += times[1];
    peak += hwm;
    read++;
  }
  if (read == 0) return 1;
  long ticks = sysconf(_SC_CLK_TCK);
  printf("cpu %llu %llu %llu\n", user * 1000000 / ticks, system * 1000000 / ticks, peak * 1024);
  return 0;
#else
  return 1;
#endif
}

/* The program's current physical footprint in bytes, or -1 where it is
 * not read (the program has ended). */
static long long footprint(pid_t pid) {
#ifdef __APPLE__
  struct rusage_info_v4 info;
  if (proc_pid_rusage((int)pid, RUSAGE_INFO_V4, (rusage_info_t *)&info) != 0) return -1;
  return (long long)info.ri_phys_footprint;
#elif defined(__linux__)
  char path[64], line[256];
  snprintf(path, sizeof path, "/proc/%ld/status", (long)pid);
  FILE *f = fopen(path, "r");
  if (!f) return -1;
  unsigned long long kb, total = 0;
  while (fgets(line, sizeof line, f))
    if (sscanf(line, "VmRSS: %llu kB", &kb) == 1 || sscanf(line, "VmSwap: %llu kB", &kb) == 1) total += kb;
  fclose(f);
  return (long long)total * 1024;
#else
  (void)pid;
  return -1;
#endif
}

/* Milliseconds since an arbitrary fixed point. */
static long long now_ms(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (long long)t.tv_sec * 1000 + t.tv_nsec / 1000000;
}

static void wake(int sig) { (void)sig; }

/* How long a program may run past SIGTERM before it and its group are
 * killed. */
#define GRACE_MS 250
/* How often the program's memory is read. */
#define POLL_MS 200

/* The stage's process group (the watchdog's process id once it exists), the
 * program's process id, and whether the program has been reaped, with its
 * status. */
static pid_t group = 0, child = 0;
static int reaped = 0, status = 0;
/* Whether the watchdog, and so the group under its id, still exists. */
static int watching = 0;

/* A failure of the runner itself: the program and its group killed, the
 * failure reported, the runner's exit status 125. */
static void fail(const char *what) {
  int e = errno;
  if (child > 0 && !reaped) kill(child, SIGKILL);
  if (group > 0 && watching) kill(-group, SIGKILL);
  dprintf(3, "runner %s %d\n", what, e);
  _exit(125);
}

/* waitpid, retried on EINTR; a failure is the runner's. */
static pid_t wait_for(pid_t pid, int *into, int options) {
  pid_t r;
  while ((r = waitpid(pid, into, options)) < 0 && errno == EINTR) {}
  if (r < 0) fail("waitpid");
  return r;
}

/* Reap the program if it has ended. */
static void reap(void) {
  if (!reaped && wait_for(child, &status, WNOHANG) == child) reaped = 1;
}

/* SIGALRM after `ms` milliseconds, or none for 0. */
static void arm(long ms) {
  struct itimerval t;
  memset(&t, 0, sizeof t);
  t.it_value.tv_sec = ms / 1000;
  t.it_value.tv_usec = (ms % 1000) * 1000;
  if (setitimer(ITIMER_REAL, &t, NULL) != 0) fail("setitimer");
}

/* Signal every member of the group, which exists while the watchdog does.
 * macOS refuses a group signal with EPERM where the group holds a zombie,
 * having signalled the others. */
static void kill_group(int sig) {
  if (watching && kill(-group, sig) != 0 && errno != EPERM) fail("kill");
}
/* Signal the program by its process id too, which reaches it after it left
 * the group (setsid). A refusal (ESRCH, or EPERM for a zombie on macOS)
 * stands only where the program has ended, which reaping it shows. */
static void kill_child(int sig) {
  if (reaped || kill(child, sig) == 0) return;
  if (errno != ESRCH && errno != EPERM) fail("kill");
  reap();
  if (!reaped) fail("kill");
}
/* Signal the program and the whole group, stopped processes continued
 * first. */
static void signal_stage(int sig) {
  kill_child(SIGCONT);
  kill_group(SIGCONT);
  kill_child(sig);
  kill_group(sig);
}

int main(int argc, char **argv) {
  if (argc == 3 && strcmp(argv[1], "--cpu") == 0) return cpu_of(argv[2]);
  char *end = NULL, *mend = NULL;
  long limit = argc >= 4 ? strtol(argv[1], &end, 10) : 0;
  long long memory = argc >= 4 ? strtoll(argv[2], &mend, 10) : 0;
  if (argc < 4 || *argv[1] == '\0' || *end != '\0' || limit <= 0 || *argv[2] == '\0' || *mend != '\0' ||
      memory <= 0 || fcntl(3, F_GETFD) < 0) {
    fprintf(stderr, "usage: stage-runner <limit ms> <memory bytes> <program> [argument…], with file descriptor 3 open "
      "for the report\n");
    return 125;
  }
  if (fcntl(3, F_SETFD, FD_CLOEXEC) != 0) fail("fcntl");
  /* Signals are taken by sigwait; SIGCHLD and SIGALRM have a handler so
   * that, blocked, they stay pending. */
  struct sigaction woken;
  memset(&woken, 0, sizeof woken);
  woken.sa_handler = wake;
  sigemptyset(&woken.sa_mask);
  if (sigaction(SIGCHLD, &woken, NULL) != 0 || sigaction(SIGALRM, &woken, NULL) != 0) fail("sigaction");
  sigset_t taken, previous;
  sigemptyset(&taken);
  int forwarded[] = {SIGTERM, SIGINT, SIGHUP, SIGQUIT};
  for (size_t i = 0; i < sizeof forwarded / sizeof *forwarded; i++) sigaddset(&taken, forwarded[i]);
  sigaddset(&taken, SIGCHLD);
  sigaddset(&taken, SIGALRM);
  if (sigprocmask(SIG_BLOCK, &taken, &previous) != 0) fail("sigprocmask");

  /* The watchdog leads the stage's process group, so the group exists, under
   * its id, as long as the watchdog does. It holds the read end of a pipe
   * whose write end only the runner holds: when the runner ends in any way,
   * the watchdog reads end of file and kills the group, itself included. It
   * reports its setup complete by a byte on a second pipe; the runner
   * starts the program only then. The runner kills the group, the watchdog
   * with it, when the program ends. */
  int watch[2], ready[2];
  if (pipe(watch) != 0 || pipe(ready) != 0) fail("pipe");
  for (int i = 0; i < 2; i++)
    if (fcntl(watch[i], F_SETFD, FD_CLOEXEC) != 0 || fcntl(ready[i], F_SETFD, FD_CLOEXEC) != 0) fail("fcntl");
  pid_t watchdog = fork();
  if (watchdog < 0) fail("fork");
  if (watchdog == 0) {
    int ok = setpgid(0, 0) == 0 && close(watch[1]) == 0 && close(ready[0]) == 0 &&
      sigprocmask(SIG_SETMASK, &previous, NULL) == 0;
    for (size_t i = 0; ok && i < sizeof forwarded / sizeof *forwarded; i++) ok = signal(forwarded[i], SIG_IGN) != SIG_ERR;
    for (int fd = 0; ok && fd <= 3; fd++) ok = close(fd) == 0 || errno == EBADF;
    char c = 1;
    if (!ok || write(ready[1], &c, 1) != 1) _exit(125);
    close(ready[1]);
    while (read(watch[0], &c, 1) < 0 && errno == EINTR) {}
    kill(-getpid(), SIGKILL);
    _exit(125);
  }
  /* The watchdog makes its group itself before it reports ready: only one
   * process changes a group, since concurrent changes may be refused (EPERM
   * on macOS). */
  group = watchdog;
  watching = 1;
  if (close(watch[0]) != 0 || close(ready[1]) != 0) fail("close");
  char byte;
  ssize_t got;
  while ((got = read(ready[0], &byte, 1)) < 0 && errno == EINTR) {}
  if (got != 1) {
    errno = got < 0 ? errno : ECHILD;
    fail("watchdog-setup");
  }
  if (close(ready[0]) != 0) fail("close");
  if (getpgid(watchdog) != watchdog) fail("getpgid");

  child = fork();
  if (child < 0) fail("fork");
  if (child == 0) {
    if (setpgid(0, group) != 0 || signal(SIGCHLD, SIG_DFL) == SIG_ERR || signal(SIGALRM, SIG_DFL) == SIG_ERR ||
        sigprocmask(SIG_SETMASK, &previous, NULL) != 0) {
      dprintf(3, "runner child %d\n", errno);
      _exit(125);
    }
    execvp(argv[3], argv + 3);
    dprintf(3, "exec %d\n", errno);
    _exit(127);
  }
  /* The child joins the group itself before it executes the program, or
   * exits with 125. Before it has joined, the program is reached by its
   * process id, which every signal of the stage also goes to. */

  /* At a limit, or on a forwarded signal, the program and its group are
   * signalled; GRACE_MS later they are killed. The timer wakes the runner
   * every POLL_MS to read the program's memory, and at the time limit. */
  long long started = now_ms(), exceeded = -1;
  arm(limit < POLL_MS ? limit : POLL_MS);
  int terminating = 0, expired = 0, killed = 0;
  while (!reaped) {
    /* macOS's sigwait returns 0 on an interrupted wait (EINTR) and leaves
     * its signal unset: a wait that names no signal is waited again. */
    int sig = 0;
    int e = sigwait(&taken, &sig);
    if (e != 0) {
      errno = e;
      fail("sigwait");
    }
    if (sig == 0) continue;
    if (sig == SIGCHLD) {
      // The watchdog ends early only where the runner has killed the group.
      if (watching && wait_for(watchdog, NULL, WNOHANG) == watchdog) {
        if (!killed) {
          errno = ECHILD;
          fail("watchdog");
        }
        watching = 0;
      }
      reap();
      continue;
    }
    if (sig == SIGALRM && terminating) {
      killed = 1;
      kill_child(SIGKILL);
      kill_group(SIGKILL);
      continue;
    }
    if (sig == SIGALRM) {
      long long elapsed = now_ms() - started, used = footprint(child);
      if (elapsed >= limit) expired = 1;
      else if (used > memory) exceeded = used;
      else {
        long long left = limit - elapsed;
        arm(left < POLL_MS ? (long)left : POLL_MS);
        continue;
      }
    }
    signal_stage(sig == SIGALRM ? SIGTERM : sig);
    if (!terminating) {
      terminating = 1;
      arm(GRACE_MS);
    }
  }
  arm(0);
  /* The program has ended: what remains of its group, which the watchdog
   * keeps under its id, is killed, the watchdog with it. */
  if (watching) {
    kill_group(SIGKILL);
    if (wait_for(watchdog, NULL, 0) != watchdog) fail("waitpid");
  }
  struct rusage used;
  if (getrusage(RUSAGE_CHILDREN, &used) != 0) fail("getrusage");
#ifdef __APPLE__
  long long peak = used.ru_maxrss; /* bytes */
#else
  long long peak = (long long)used.ru_maxrss * 1024; /* kB */
#endif
  /* The runner ends as the program did: its exit status, or its signal,
   * raised with no core file once the report is written. */
  int sig = WIFSIGNALED(status) ? WTERMSIG(status) : 0;
  if (sig) {
    struct rlimit none = {0, 0};
    if (setrlimit(RLIMIT_CORE, &none) != 0) fail("setrlimit");
    if (sig != SIGKILL && signal(sig, SIG_DFL) == SIG_ERR) fail("signal");
  }
  if ((expired && dprintf(3, "deadline\n") < 0) || (exceeded >= 0 && dprintf(3, "memory %lld\n", exceeded) < 0) ||
      dprintf(3, "cpu %lld %lld %lld\n", micros(used.ru_utime), micros(used.ru_stime), peak) < 0)
    fail("dprintf");
  if (close(3) != 0) fail("close");
  if (!sig) return WIFEXITED(status) ? WEXITSTATUS(status) : 125;
  sigset_t only;
  sigemptyset(&only);
  sigaddset(&only, sig);
  if (sigprocmask(SIG_UNBLOCK, &only, NULL) != 0 || kill(getpid(), sig) != 0) _exit(125);
  _exit(125);
}
