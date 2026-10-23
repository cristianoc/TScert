/* The runner of process stages (DESIGN.md, "The stage store", measurement):
 * it runs a stage's program and reports the CPU time of the processes the
 * stage ran and their peak memory, which Node's spawnSync does not report.
 *
 *   stage-runner <program> [argument…]
 *     runs <program> with the arguments, the environment, the working
 *     directory and the standard streams it was given, in a process group
 *     of its own. SIGTERM, SIGINT, SIGHUP and SIGQUIT are forwarded to that
 *     group. When the program ends, what remains of its group is killed,
 *     and the runner writes to file descriptor 3, which the program does not
 *     inherit, the line `cpu <user µs> <system µs> <peak bytes>`: the CPU
 *     time of the program and of every descendant it waited for, and the
 *     largest peak resident set among them (RUSAGE_CHILDREN). It then ends
 *     as the program did: the same exit status, or the same signal. A
 *     program that cannot be executed is reported as `exec <errno>`, and the
 *     runner exits with 127.
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

int main(int argc, char **argv) {
  if (argc == 3 && strcmp(argv[1], "--cpu") == 0) return cpu_of(argv[2]);
  if (argc < 2 || fcntl(3, F_GETFD) < 0) {
    fprintf(stderr, "usage: stage-runner <program> [argument…], with file descriptor 3 open for the report\n");
    return 125;
  }
  fcntl(3, F_SETFD, FD_CLOEXEC);
  /* Signals are taken by sigwait; SIGCHLD has a handler so that, blocked,
   * it stays pending. */
  struct sigaction chld;
  memset(&chld, 0, sizeof chld);
  chld.sa_handler = wake;
  sigemptyset(&chld.sa_mask);
  sigaction(SIGCHLD, &chld, NULL);
  sigset_t taken, previous;
  sigemptyset(&taken);
  int forwarded[] = {SIGTERM, SIGINT, SIGHUP, SIGQUIT};
  for (size_t i = 0; i < sizeof forwarded / sizeof *forwarded; i++) sigaddset(&taken, forwarded[i]);
  sigaddset(&taken, SIGCHLD);
  sigprocmask(SIG_BLOCK, &taken, &previous);

  pid_t child = fork();
  if (child < 0) {
    dprintf(3, "exec %d\n", errno);
    return 127;
  }
  if (child == 0) {
    setpgid(0, 0);
    signal(SIGCHLD, SIG_DFL);
    sigprocmask(SIG_SETMASK, &previous, NULL);
    execvp(argv[1], argv + 1);
    dprintf(3, "exec %d\n", errno);
    _exit(127);
  }
  setpgid(child, child);

  for (;;) {
    int sig;
    if (sigwait(&taken, &sig) != 0) continue;
    if (sig != SIGCHLD) {
      kill(-child, sig);
      continue;
    }
    siginfo_t info;
    memset(&info, 0, sizeof info);
    if (waitid(P_PID, (id_t)child, &info, WEXITED | WNOHANG | WNOWAIT) == 0 && info.si_pid == child) break;
  }
  /* The program has ended and is not yet reaped, so its group still exists
   * under its own id: what remains of it is killed. */
  kill(-child, SIGKILL);
  int status;
  while (waitpid(child, &status, 0) < 0 && errno == EINTR) {}
  struct rusage used;
  getrusage(RUSAGE_CHILDREN, &used);
#ifdef __APPLE__
  long long peak = used.ru_maxrss; /* bytes */
#else
  long long peak = (long long)used.ru_maxrss * 1024; /* kB */
#endif
  dprintf(3, "cpu %lld %lld %lld\n", micros(used.ru_utime), micros(used.ru_stime), peak);
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
