/* The runner of process stages (DESIGN.md, "The stage store", measurement):
 * it runs a stage's program and reports the CPU time of the processes the
 * stage ran and their peak memory, which Node's spawnSync does not report.
 *
 *   stage-runner <limit ms> <program> [argument…]
 *     runs <program> with the arguments, the environment, the working
 *     directory and the standard streams it was given, in a process group
 *     of its own, led by a watchdog that kills the group when the runner
 *     ends in any way. At the limit, or on SIGTERM, SIGINT, SIGHUP or
 *     SIGQUIT, the group is continued and signalled (SIGTERM at the limit),
 *     and killed 250 ms later. When the program ends, what remains of its
 *     group is killed, and the runner writes to file descriptor 3, which the
 *     program does not inherit, `deadline` where the limit expired and
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
 *     maximum physical footprint, on Linux its peak resident set), or exits
 *     with 1 where it is not read.
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
#ifdef __APPLE__
#include <libproc.h>
#include <mach/mach_time.h>
#endif

static long long micros(struct timeval t) { return (long long)t.tv_sec * 1000000 + t.tv_usec; }

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
  char path[64];
  snprintf(path, sizeof path, "/proc/%ld/stat", pid);
  FILE *f = fopen(path, "r");
  if (!f) return 1;
  char line[4096];
  size_t n = fread(line, 1, sizeof line - 1, f);
  fclose(f);
  line[n] = '\0';
  /* The fields after the command's closing parenthesis: state is the 3rd
   * field, utime and stime the 14th and 15th, in clock ticks. */
  char *rest = strrchr(line, ')');
  unsigned long long user, system, peak = 0;
  if (!rest || sscanf(rest + 1, " %*c %*d %*d %*d %*d %*d %*u %*u %*u %*u %*u %llu %llu", &user, &system) != 2)
    return 1;
  /* The peak resident set, VmHWM of its status, in kB. */
  snprintf(path, sizeof path, "/proc/%ld/status", pid);
  f = fopen(path, "r");
  if (!f) return 1;
  while (fgets(line, sizeof line, f))
    if (sscanf(line, "VmHWM: %llu kB", &peak) == 1) break;
  fclose(f);
  long ticks = sysconf(_SC_CLK_TCK);
  printf("cpu %llu %llu %llu\n", user * 1000000 / ticks, system * 1000000 / ticks, peak * 1024);
  return 0;
#else
  return 1;
#endif
}

static void wake(int sig) { (void)sig; }

/* How long a program may run past SIGTERM before its group is killed. */
#define GRACE_MS 250

/* The stage's process group: the watchdog's process id once it exists. */
static pid_t group = 0;

/* A failure of the runner itself: the stage's group killed, the failure
 * reported, the runner's exit status 125. */
static void fail(const char *what) {
  int e = errno;
  if (group > 0) kill(-group, SIGKILL);
  dprintf(3, "runner %s %d\n", what, e);
  _exit(125);
}

/* SIGALRM after `ms` milliseconds, or none for 0. */
static void arm(long ms) {
  struct itimerval t;
  memset(&t, 0, sizeof t);
  t.it_value.tv_sec = ms / 1000;
  t.it_value.tv_usec = (ms % 1000) * 1000;
  if (setitimer(ITIMER_REAL, &t, NULL) != 0) fail("setitimer");
}

/* Signal every member of the group. macOS refuses a group signal with EPERM
 * where the group holds a zombie, having signalled the others. */
static void kill_group(int sig) {
  if (kill(-group, sig) != 0 && errno != EPERM) fail("kill");
}
/* Signal the whole group, a stopped member continued first. */
static void signal_group(int sig) {
  kill_group(SIGCONT);
  kill_group(sig);
}

int main(int argc, char **argv) {
  if (argc == 3 && strcmp(argv[1], "--cpu") == 0) return cpu_of(argv[2]);
  char *end = NULL;
  long limit = argc >= 3 ? strtol(argv[1], &end, 10) : 0;
  if (argc < 3 || *argv[1] == '\0' || *end != '\0' || limit <= 0 || fcntl(3, F_GETFD) < 0) {
    fprintf(stderr, "usage: stage-runner <limit ms> <program> [argument…], with file descriptor 3 open for the report\n");
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
   * the watchdog reads end of file and kills the group, itself included.
   * The runner kills the group, the watchdog with it, when the program ends. */
  int watch[2];
  if (pipe(watch) != 0) fail("pipe");
  if (fcntl(watch[0], F_SETFD, FD_CLOEXEC) != 0 || fcntl(watch[1], F_SETFD, FD_CLOEXEC) != 0) fail("fcntl");
  pid_t watchdog = fork();
  if (watchdog < 0) fail("fork");
  if (watchdog == 0) {
    setpgid(0, 0);
    for (size_t i = 0; i < sizeof forwarded / sizeof *forwarded; i++) signal(forwarded[i], SIG_IGN);
    sigprocmask(SIG_SETMASK, &previous, NULL);
    close(watch[1]);
    for (int fd = 0; fd <= 3; fd++) close(fd);
    char c;
    while (read(watch[0], &c, 1) < 0 && errno == EINTR) {}
    kill(-getpid(), SIGKILL);
    _exit(0);
  }
  /* Both the watchdog and the runner make the watchdog's group; whichever
   * comes second may be refused (EPERM on macOS), so the group is checked. */
  if (setpgid(watchdog, watchdog) != 0 && getpgid(watchdog) != watchdog) fail("setpgid");
  group = watchdog;
  if (close(watch[0]) != 0) fail("close");

  pid_t child = fork();
  if (child < 0) fail("fork");
  if (child == 0) {
    if (setpgid(0, group) != 0) {
      dprintf(3, "runner setpgid %d\n", errno);
      _exit(125);
    }
    signal(SIGCHLD, SIG_DFL);
    signal(SIGALRM, SIG_DFL);
    sigprocmask(SIG_SETMASK, &previous, NULL);
    execvp(argv[2], argv + 2);
    dprintf(3, "exec %d\n", errno);
    _exit(127);
  }
  /* The child joins the group itself before it executes the program, or
   * exits with 125; joining it here too only narrows the window in which a
   * group signal misses it. It fails where the child has executed the
   * program (EACCES) or ended (ESRCH, or EPERM on macOS), which is no
   * failure. */
  (void)setpgid(child, group);

  /* At the limit, or on a forwarded signal, the group is signalled; GRACE_MS
   * later it is killed. */
  arm(limit);
  int terminating = 0, expired = 0, status = 0;
  for (;;) {
    int sig;
    int e = sigwait(&taken, &sig);
    if (e != 0) {
      errno = e;
      fail("sigwait");
    }
    if (sig == SIGCHLD) {
      pid_t reaped = waitpid(child, &status, WNOHANG);
      if (reaped < 0 && errno != EINTR) fail("waitpid");
      if (reaped == child) break;
      continue;
    }
    if (sig == SIGALRM && terminating) {
      kill_group(SIGKILL);
      continue;
    }
    if (sig == SIGALRM) expired = 1;
    signal_group(sig == SIGALRM ? SIGTERM : sig);
    if (!terminating) {
      terminating = 1;
      arm(GRACE_MS);
    }
  }
  arm(0);
  /* The program has ended: what remains of its group, which the watchdog
   * keeps under its id, is killed, the watchdog with it. */
  kill_group(SIGKILL);
  pid_t reaped;
  while ((reaped = waitpid(watchdog, NULL, 0)) < 0 && errno == EINTR) {}
  if (reaped != watchdog) fail("waitpid");
  struct rusage used;
  if (getrusage(RUSAGE_CHILDREN, &used) != 0) fail("getrusage");
#ifdef __APPLE__
  long long peak = used.ru_maxrss; /* bytes */
#else
  long long peak = (long long)used.ru_maxrss * 1024; /* kB */
#endif
  if ((expired && dprintf(3, "deadline\n") < 0) ||
      dprintf(3, "cpu %lld %lld %lld\n", micros(used.ru_utime), micros(used.ru_stime), peak) < 0)
    fail("dprintf");
  close(3);

  if (WIFEXITED(status)) return WEXITSTATUS(status);
  int sig = WTERMSIG(status);
  struct rlimit none = {0, 0};
  setrlimit(RLIMIT_CORE, &none);
  signal(sig, SIG_DFL);
  sigset_t only;
  sigemptyset(&only);
  sigaddset(&only, sig);
  sigprocmask(SIG_UNBLOCK, &only, NULL);
  kill(getpid(), sig);
  return 128 + sig;
}
