/*
 * COMP 321 Project 4: Shell
 *
 * This program implements a tiny shell with job control.
 *
 * Madison Roy and Rose Whitt; mmr11 and rew9
 */

#define _GNU_SOURCE
#include <sys/types.h>
#include <sys/wait.h>

#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <signal.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

// You may assume that these constants are large enough.
#define MAXLINE 1024	 // max line size
#define MAXARGS 128		 // max args on a command line
#define MAXJOBS 16		 // max jobs at any point in time
#define MAXJID (1 << 16) // max job ID

// The job states are:
#define UNDEF 0 // undefined
#define FG 1	// running in foreground
#define BG 2	// running in background
#define ST 3	// stopped

/*
 * The job state transitions and enabling actions are:
 *     FG -> ST  : ctrl-z
 *     ST -> FG  : fg command
 *     ST -> BG  : bg command
 *     BG -> FG  : fg command
 * At most one job can be in the FG state.
 */

struct Job
{
	pid_t pid;			   // job PID
	int jid;			   // job ID [1, 2, ...]
	int state;			   // UNDEF, FG, BG, or ST
	char cmdline[MAXLINE]; // command line
};
typedef volatile struct Job *JobP;

/*
 * Define the jobs list using the "volatile" qualifier because it is accessed
 * by a signal handler (as well as the main program).
 */
static volatile struct Job jobs[MAXJOBS];
static int nextjid = 1; // next job ID to allocate

extern char **environ; // defined by libc

static char prompt[] = "tsh> "; // command line prompt (DO NOT CHANGE)
static bool verbose = false;	// If true, print additional output.

/**
 * Student made variables.
 * 
 */
const char *search_path;

/**
 * Linked List structure for directory list.
 * 
 */
struct ptrNode
{
	char *ptr;
	struct ptrNode *next;
};

static char **dir_list; // stores directories from search path
static int num_dirs;	// number of directories found in the search path

/*
 * The following array can be used to map a signal number to its name.
 * This mapping is valid for x86(-64)/Linux systems, such as CLEAR.
 * The mapping for other versions of Unix, such as FreeBSD, Mac OS X, or
 * Solaris, differ!
 */
static const char *const signame[NSIG] = {
	"Signal 0",
	"HUP",	  /* SIGHUP */
	"INT",	  /* SIGINT */
	"QUIT",	  /* SIGQUIT */
	"ILL",	  /* SIGILL */
	"TRAP",	  /* SIGTRAP */
	"ABRT",	  /* SIGABRT */
	"BUS",	  /* SIGBUS */
	"FPE",	  /* SIGFPE */
	"KILL",	  /* SIGKILL */
	"USR1",	  /* SIGUSR1 */
	"SEGV",	  /* SIGSEGV */
	"USR2",	  /* SIGUSR2 */
	"PIPE",	  /* SIGPIPE */
	"ALRM",	  /* SIGALRM */
	"TERM",	  /* SIGTERM */
	"STKFLT", /* SIGSTKFLT */
	"CHLD",	  /* SIGCHLD */
	"CONT",	  /* SIGCONT */
	"STOP",	  /* SIGSTOP */
	"TSTP",	  /* SIGTSTP */
	"TTIN",	  /* SIGTTIN */
	"TTOU",	  /* SIGTTOU */
	"URG",	  /* SIGURG */
	"XCPU",	  /* SIGXCPU */
	"XFSZ",	  /* SIGXFSZ */
	"VTALRM", /* SIGVTALRM */
	"PROF",	  /* SIGPROF */
	"WINCH",  /* SIGWINCH */
	"IO",	  /* SIGIO */
	"PWR",	  /* SIGPWR */
	"Signal 31"};

// You must implement the following functions:

static int builtin_cmd(char **argv);
static void do_bgfg(char **argv);
static void eval(const char *cmdline);
static void initpath(const char *pathstr);
static void waitfg(pid_t pid);

static void sigchld_handler(int signum);
static void sigint_handler(int signum);
static void sigtstp_handler(int signum);

// We are providing the following functions to you:

static int parseline(const char *cmdline, char **argv);

static void sigquit_handler(int signum);

static int addjob(JobP jobs, pid_t pid, int state, const char *cmdline);
static void clearjob(JobP job);
static int deletejob(JobP jobs, pid_t pid);
static pid_t fgpid(JobP jobs);
static JobP getjobjid(JobP jobs, int jid);
static JobP getjobpid(JobP jobs, pid_t pid);
static void initjobs(JobP jobs);
static void listjobs(JobP jobs);
static int maxjid(JobP jobs);
static int pid2jid(pid_t pid);

static void app_error(const char *msg);
static void unix_error(const char *msg);
static void usage(void);

static void Sio_error(const char s[]);
static ssize_t Sio_putl(long v);
static ssize_t Sio_puts(const char s[]);
static void sio_error(const char s[]);
static void sio_ltoa(long v, char s[], int b);
static ssize_t sio_putl(long v);
static ssize_t sio_puts(const char s[]);
static void sio_reverse(char s[]);
static size_t sio_strlen(const char s[]);

/*
 * Requires:
 *   Valid argc and argv.
 *
 * Effects:
 *   Runs the shell
 */
int main(int argc, char **argv)
{
	struct sigaction action;
	int c;
	char cmdline[MAXLINE];
	char *path = NULL;
	bool emit_prompt = true; // Emit a prompt by default.

	/*
	 * Redirect stderr to stdout (so that driver will get all output
	 * on the pipe connected to stdout).
	 */
	dup2(1, 2);

	// Parse the command line.
	while ((c = getopt(argc, argv, "hvp")) != -1)
	{
		switch (c)
		{
		case 'h': // Print a help message.
			usage();
			break;
		case 'v': // Emit additional diagnostic info.
			verbose = true;
			break;
		case 'p': // Don't print a prompt.
			// This is handy for automatic testing.
			emit_prompt = false;
			break;
		default:
			usage();
		}
	}

	/*
	 * Install sigint_handler() as the handler for SIGINT (ctrl-c).  SET
	 * action.sa_mask TO REFLECT THE SYNCHRONIZATION REQUIRED BY YOUR
	 * IMPLEMENTATION OF sigint_handler().
	 */
	action.sa_handler = sigint_handler;
	action.sa_flags = SA_RESTART;
	sigemptyset(&action.sa_mask);
	sigaddset(&action.sa_mask, SIGCHLD);
	sigaddset(&action.sa_mask, SIGTSTP);
	if (sigaction(SIGINT, &action, NULL) < 0)
		unix_error("sigaction error");

	/*
	 * Install sigtstp_handler() as the handler for SIGTSTP (ctrl-z).  SET
	 * action.sa_mask TO REFLECT THE SYNCHRONIZATION REQUIRED BY YOUR
	 * IMPLEMENTATION OF sigtstp_handler().
	 */
	action.sa_handler = sigtstp_handler;
	action.sa_flags = SA_RESTART;
	sigemptyset(&action.sa_mask);
	sigaddset(&action.sa_mask, SIGCHLD);
	sigaddset(&action.sa_mask, SIGINT);
	if (sigaction(SIGTSTP, &action, NULL) < 0)
		unix_error("sigaction error");

	/*
	 * Install sigchld_handler() as the handler for SIGCHLD (terminated or
	 * stopped child).  SET action.sa_mask TO REFLECT THE SYNCHRONIZATION
	 * REQUIRED BY YOUR IMPLEMENTATION OF sigchld_handler().
	 */
	action.sa_handler = sigchld_handler;
	action.sa_flags = SA_RESTART;
	sigemptyset(&action.sa_mask);
	sigaddset(&action.sa_mask, SIGINT);
	sigaddset(&action.sa_mask, SIGTSTP);
	if (sigaction(SIGCHLD, &action, NULL) < 0)
		unix_error("sigaction error");

	/*
	 * Install sigquit_handler() as the handler for SIGQUIT.  This handler
	 * provides a clean way for the test harness to terminate the shell.
	 * Preemption of the processor by the other signal handlers during
	 * sigquit_handler() does no harm, so action.sa_mask is set to empty.
	 */
	action.sa_handler = sigquit_handler;
	action.sa_flags = SA_RESTART;
	sigemptyset(&action.sa_mask);
	if (sigaction(SIGQUIT, &action, NULL) < 0)
		unix_error("sigaction error");

	// Initialize the search path.
	path = getenv("PATH");
	initpath(path);

	// Initialize the jobs list.
	initjobs(jobs);

	// Execute the shell's read/eval loop.
	while (true)
	{

		// Read the command line.
		if (emit_prompt)
		{
			printf("%s", prompt);
			fflush(stdout);
		}
		if (fgets(cmdline, MAXLINE, stdin) == NULL && ferror(stdin))
			app_error("fgets error");
		if (feof(stdin)) // End of file (ctrl-d)
			exit(0);

		// Evaluate the command line.
		eval(cmdline);
		fflush(stdout);
	}

	// Control never reaches here.
	assert(false);
}

/* 
 *
 * Requires:
 *   A valid command line.
 *
 * Effects:
 *   If the user has requested a built-in command, executes the job
 * 		immediately.
 * 	Otherwise, fork the child process and run the job.
 * 		If the job is in the foreground, eval waits for the job
 * 		to terminate and then returns.
 * 		
 */
static void
eval(const char *cmdline)
{
	/**
	 * Initialization.
	 * 
	 */
	char *argv[MAXARGS];
	char buf[MAXLINE];
	int bg, i;
	pid_t pid;
	sigset_t mask, prev_mask;

	/**
	 * Parses command line and checks if its
	 * 		 a background or foreground job.
	 * 
	 */
	strcpy(buf, cmdline);
	bg = parseline(buf, argv);

	if (argv[0] == NULL)
	{
		return;
	}

	// Checks if input is a built in command, executes if it is
	if (builtin_cmd(argv) == 1)
	{
		return;
	}

	/**
	 * Fork and execute child process if not a built in command.
	 * 
	 */
	if (!builtin_cmd(argv))
	{

		// Blocks all incoming SIGCHLD signals.
		sigemptyset(&mask);
		sigaddset(&mask, SIGCHLD);
		sigprocmask(SIG_BLOCK, &mask, &prev_mask);

		if ((pid = fork()) == 0)
		{ // now in the child process
			sigprocmask(SIG_SETMASK, &prev_mask, NULL);

			if (verbose)
				printf("in pid == 0");

			/**
			 * 'name' is not a directory and the search path
			 * 		is not NULL.
			 */
			if ((strchr(argv[0], '/') == NULL && dir_list != NULL))
			{
				if (verbose)
					printf("not a directory");
				setpgid(0, 0);

				for (i = 0; i < num_dirs; i++)
				{

					/**
					 * Process the path for execution.
					 * 
					 */
					char cur_path[strlen(dir_list[i]) + 1 + sizeof(argv[0])];

					strcpy(cur_path, dir_list[i]);
					strcat(cur_path, "/");
					strcat(cur_path, argv[0]);

					/**
					 * Try to execute, if it doesn't work,
					 * 		 it'll go on to next iteration of loop.
					 * 
					 */
					execve(cur_path, argv, environ);
				}
				printf("%s: Command not found!\n", argv[0]);
				exit(0);
			}
			/**
			 * 'name' is a directory.
			 * 
			 */
			if (strchr(argv[0], '/') != NULL || dir_list == NULL)
			{
				setpgid(0, 0);

				/**
				 * Handles case when execution fails
				 * 		 (directory is not executable).
				 * 
				 */
				if (execve(argv[0], argv, environ) < 0)
				{
					printf("%s: Command not found!\n", argv[0]);
					exit(0);
				}
			}
		}

		/**
		 * Parent process waits for child process and reaps.
		 * 
		 */
		if (!bg)
		{
			if (verbose)
				printf("Inside !bg.\n");
			/**
			 * Foreground job.
			 * 
			 */
			addjob(jobs, pid, FG, cmdline);				// Add the job.
			sigprocmask(SIG_SETMASK, &prev_mask, NULL); // Set mask.

			waitfg(pid); // Wait for foreground job to finish execution.
			if (verbose)
				printf("Exit !bg.\n");
		}
		else
		{
			if (verbose)
				printf("Inside !fg.\n");

			/**
			 * Background job.
			 * 
			 */
			addjob(jobs, pid, BG, cmdline);				// Add the job.
			sigprocmask(SIG_SETMASK, &prev_mask, NULL); // Set mask.
			// Print job immediately.
			printf("[%d] (%d) %s", pid2jid(pid), pid, cmdline);

			if (verbose)
				printf("Exit !fg.\n");
		}
	}
}

/* 
 *
 * Requires:
 *   "cmdline" is a NUL ('\0') terminated string with a trailing
 *   '\n' character.  "cmdline" must contain less than MAXARGS
 *   arguments.
 *
 * Effects:
 *   Builds "argv" array from space delimited arguments on the command line.
 *   The final element of "argv" is set to NULL.  Characters enclosed in
 *   single quotes are treated as a single argument.  Returns true if
 *   the user has requested a BG job and false if the user has requested
 *   a FG job.
 */
static int
parseline(const char *cmdline, char **argv)
{
	int argc;					// number of args
	int bg;						// background job?
	static char array[MAXLINE]; // local copy of command line
	char *buf = array;			// ptr that traverses command line
	char *delim;				// points to first space delimiter

	strcpy(buf, cmdline);

	// Replace trailing '\n' with space.
	buf[strlen(buf) - 1] = ' ';

	// Ignore leading spaces.
	while (*buf != '\0' && *buf == ' ')
		buf++;

	// Build the argv list.
	argc = 0;
	if (*buf == '\'')
	{
		buf++;
		delim = strchr(buf, '\'');
	}
	else
		delim = strchr(buf, ' ');
	while (delim != NULL)
	{
		argv[argc++] = buf;
		*delim = '\0';
		buf = delim + 1;
		while (*buf != '\0' && *buf == ' ') // Ignore spaces.
			buf++;
		if (*buf == '\'')
		{
			buf++;
			delim = strchr(buf, '\'');
		}
		else
			delim = strchr(buf, ' ');
	}
	argv[argc] = NULL;

	// Ignore blank line.
	if (argc == 0)
		return (1);

	// Should the job run in the background?
	if ((bg = (*argv[argc - 1] == '&')) != 0)
		argv[--argc] = NULL;

	return (bg);
}

/* 
 *
 * Requires:
 *   argv from parseline.
 *
 * Effects:
 *   Executes immediately if user typed a built-in command.
 */
static int
builtin_cmd(char **argv)
{
	if (!strcmp(argv[0], "quit"))
	{
		exit(0);
	}
	if (!strcmp(argv[0], "jobs"))
	{
		listjobs(jobs);
		return (1);
	}
	if (!strcmp(argv[0], "fg"))
	{
		do_bgfg(argv);
		return (1);
	}
	if (!strcmp(argv[0], "bg"))
	{
		do_bgfg(argv);
		return (1);
	}
	return (0); // This is not a built-in command.
}

/* 
 *
 * Requires:
 *   argv from parseline.
 *
 * Effects:
 *   Execute the built-in bg and fg commands.
 */
static void
do_bgfg(char **argv)
{
	if (verbose)
		printf("\nEnter Function: do_bgfg.\n");
	if (verbose)
		printf("----\n");

	/**
	 * Initialization.
	 * 
	 */
	pid_t pid;
	char *temp_jid; // Used to temporarily store string after '%'.
	int jid;
	JobP job; // declare job structure

	/*
	 * STEP ZERO: Verify valid conditions.
	 */

	/**
	 * 1) Non-NULL.
	 * 
	 */
	if (argv[1] == NULL)
	{
		printf("%s command requires second non-NULL argument.\n", argv[0]);
		return;
	}

	/**
	 * 2) If doesn't start with a digit (PID)
	 *  	and doesnt start with a % (jid).
	 */
	if (!(isdigit(argv[1][0])) && (argv[1][0] != '%'))
	{
		printf("%s command requires a valid PID or a JID.\n", argv[0]);
	}

	/*
	 * STEP ONE: Get PID or JID from argv.
	 * 
	 */

	/**
	 * If a JID (ex: '%5').
	 * 
	 */
	if (argv[1][0] == '%')
	{
		temp_jid = strchr(argv[1], '%'); // Get chars after '%'.
		jid = atoi(temp_jid + 1);
		job = getjobjid(jobs, jid); // Parse JID, get job.

		if (job == NULL)
		{
			Sio_puts("(");
			Sio_puts(argv[1]);
			Sio_puts("): No such job\n");
			return;
		}
	}
	/**
	 * If a PID (ex: '5').
	 */
	else
	{
		// Get PID and JID.
		pid = (pid_t)atoi(argv[1]);
		job = getjobpid(jobs, pid);

		if (job == NULL)
		{
			Sio_puts("(");
			Sio_puts(argv[1]);
			Sio_puts("): No such process\n");
			return;
		}
	}

	/*
	 * STEP TWO: Change the job.
	 * 
	 */

	/**
	 * Change foreground or stopped job to background job.
	 * 
	 */
	if (!(strcmp(argv[0], "bg")))
	{
		job->state = BG; // Change state to background job
		printf("[%d] (%d) %s", job->jid, job->pid, job->cmdline);
		kill(-job->pid, SIGCONT); // Kill and send SIGCONT signal.
	}
	/**
	 * Change to a foreground job (only one allowed at a time).
	 * 
	 */
	else
	{
		job->state = FG;		  // Change BG -> FG or ST -> FG.
		kill(-job->pid, SIGCONT); // Kill and send SIGCONT signal.
		/**
		 * Wait on job to finish since only one
		 * foreground job allowed at a time.
		 */
		waitfg(job->pid);
	}

	if (verbose)
		printf("End of do_bgfg.\n");
	if (verbose)
		printf("----\n\n");
	return;
}

/* 
 *
 * Requires:
 *   A valid foreground PID.
 *
 * Effects:
 *   Blocks until process pid is no longer the foreground process.
 */
static void
waitfg(pid_t pid)
{

	if (verbose)
		printf("\nEnter Function: waitfg.\n");
	if (verbose)
		printf("----\n");

	/**
	 * Initialization.
	 * 
	 */
	sigset_t mask;
	sigemptyset(&mask);

	/**
	 * Wait for foreground job.
	 * 
	 */
	while (fgpid(jobs) == pid)
	{
		if (verbose)
			printf("In while loop.....\n");
		sigsuspend(&mask);
	}

	return;
}

/* 
 * initpath - Perform all necessary initialization of the search path,
 *  which may be simply saving the path.
 *
 * Requires:
 *   "pathstr" is a valid search path.
 *
 * Effects:
 *   Perform all necessary initialization of the search path.
 */
static void
initpath(const char *pathstr)
{
	if (verbose)
		printf("\nEnter Function: initpath.\n");
	if (verbose)
		printf("----\n");
	if (verbose)
		printf("The Original Path: %s\n", pathstr);

	int path_length = 0; // number of paths

	// Mallocate a directory list using linked list structure.
	struct ptrNode *temp_dir_list = malloc(sizeof(struct ptrNode));
	struct ptrNode *node = temp_dir_list; // Create node.

	// each directory is separated by ':' character
	if ((strlen(pathstr) == 0) || (pathstr[0] == ':') || (pathstr[strlen(pathstr) - 1] == ':'))
	{
		path_length++; // Update path count.

		// Add to Linked List.
		// Unix Comman (man 3)
		node->ptr = get_current_dir_name();
		node->next = malloc(sizeof(struct ptrNode));
		node = node->next;
	}

	// Set global directory list.
	dir_list = malloc(sizeof(char *) * path_length);
	num_dirs = path_length;
	struct ptrNode *prev;

	// Copy to global list.
	for (int i = 0; i < path_length; i++)
	{
		dir_list[i] = temp_dir_list->ptr;
		prev = temp_dir_list;
		temp_dir_list = temp_dir_list->next;
		free(prev);
	}

	// Set global search path.
	search_path = pathstr;

	if (verbose)
		printf("End of initpath.\n");
	if (verbose)
		printf("----\n\n");
}

/*
 * The signal handlers follow.
 */

/* 
 *
 * Requires:
 *   A valid signal.
 *
 * Effects:
 *   Reaps all available zombie children, but doesn't wait for
 * 		any other currently running children to terminate.
 */
static void
sigchld_handler(int signum)
{

	if (verbose)
		printf("\nEnter Function: sigchld_handler.\n");
	if (verbose)
		printf("----\n");

	// Prevent an "unused parameter" warning.
	(void)signum;

	/*
	 * Initialization.
	 */
	pid_t pid;
	int status;
	int orig_errno;

	orig_errno = errno;

	/**
	 * Reap all available zombie children until none left.
	 */
	while ((pid = waitpid(-1, &status, WNOHANG | WUNTRACED)) > 0)
	{

		if (WIFEXITED(status))
		{
			if (verbose)
				printf("Penetrated WIFEXITED.\n");

			deletejob(jobs, pid);
		}
		else if (WIFSIGNALED(status))
		{
			if (verbose)
				printf("Penetrated WIFSIGNALED.\n");

			int num = WTERMSIG(status);

			Sio_puts("Job [");
			Sio_putl(pid2jid(pid));
			Sio_puts("] (");
			Sio_putl(pid);
			Sio_puts(") terminated by signal SIG");
			Sio_puts(signame[num]);
			Sio_puts("\n");
			deletejob(jobs, pid);
		}
		else if (WIFSTOPPED(status))
		{
			if (verbose)
				printf("Penetrated WIFSTOPPED.\n");
			Sio_puts("Job [");
			Sio_putl(pid2jid(pid));
			Sio_puts("] (");
			Sio_putl(pid);
			Sio_puts(") stopped by signal SIG");
			Sio_puts(signame[WSTOPSIG(status)]);
			Sio_puts("\n");
			// Change job status to ST (stopped).
			getjobpid(jobs, pid)->state = ST;
		}
	}

	// Not all child processes were terminated.
	if (pid == -1 && errno != ECHILD)
	{
		unix_error("waitpid error");
		return;
	}

	errno = orig_errno;

	return;
}

/* 
 *
 * Requires:
 *   A valid SIGINT signal.
 *
 * Effects:
 *   Catch SIGINT and send it to the foreground job.
 */
static void
sigint_handler(int signum)
{

	(void)signum;

	/**
	 * Initialization.
	 * 
	 */
	pid_t fg;
	int orig_errno;

	orig_errno = errno;

	/**
	 * Catch and send signal.
	 * Kill the job if there is one.
	 */
	if ((fg = fgpid(jobs)) != 0)
	{
		// Kill foreground SIGINT.
		kill(-fg, SIGINT);
		// Delete the foreground job.
		deletejob(jobs, fg);
	}

	errno = orig_errno;
}

/*
 *
 * Requires:
 *   A valid SIGTSTP signal.
 *
 * Effects:
 *   Catch SIGTSTP and send it to the foreground job.
 */
static void
sigtstp_handler(int signum)
{

	(void)signum;

	/**
	 * Initalization.
	 * 
	 */
	pid_t fg;
	int orig_errno;

	orig_errno = errno; // Initialize.

	/**
	 * 
	 * Catch and send signal.
	 * Kill the job if there is one.
	 */
	if ((fg = fgpid(jobs)) != 0)
	{
		kill(-fg, SIGTSTP);				 // Sends SIGSTP signal.
		getjobpid(jobs, fg)->state = ST; // Delete jobs.
	}
	else
	{
		sio_error("No foreground job found.");
		return;
	}

	if (verbose)
		printf("End of sigint_handler.\n");
	if (verbose)
		printf("----\n\n");

	errno = orig_errno; // update

	// Return if no current foreground job.
	return;
}

/*
 *
 * Requires:
 *   "signum" is SIGQUIT.
 *
 * Effects:
 *   Terminates the program.
 */
static void
sigquit_handler(int signum)
{

	// Prevent an "unused parameter" warning.
	(void)signum;
	Sio_puts("Terminating after receipt of SIGQUIT signal\n");
	_exit(1);
}

/*
 * This comment marks the end of the signal handlers.
 */

/*
 * The following helper routines manipulate the jobs list.
 */

/*
 * Requires:
 *   "job" points to a job structure.
 *
 * Effects:
 *   Clears the fields in the referenced job structure.
 */
static void
clearjob(JobP job)
{

	job->pid = 0;
	job->jid = 0;
	job->state = UNDEF;
	job->cmdline[0] = '\0';
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures.
 *
 * Effects:
 *   Initializes the jobs list to an empty state.
 */
static void
initjobs(JobP jobs)
{
	int i;

	for (i = 0; i < MAXJOBS; i++)
		clearjob(&jobs[i]);
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures.
 *
 * Effects:
 *   Returns the largest allocated job ID.
 */
static int
maxjid(JobP jobs)
{
	int i, max = 0;

	for (i = 0; i < MAXJOBS; i++)
		if (jobs[i].jid > max)
			max = jobs[i].jid;
	return (max);
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures, and "cmdline" is
 *   a properly terminated string.
 *
 * Effects: 
 *   Adds a job to the jobs list. 
 */
static int
addjob(JobP jobs, pid_t pid, int state, const char *cmdline)
{
	int i;

	if (pid < 1)
		return (0);
	for (i = 0; i < MAXJOBS; i++)
	{
		if (jobs[i].pid == 0)
		{
			jobs[i].pid = pid;
			jobs[i].state = state;
			jobs[i].jid = nextjid++;
			if (nextjid > MAXJOBS)
				nextjid = 1;
			// Remove the "volatile" qualifier using a cast.
			strcpy((char *)jobs[i].cmdline, cmdline);
			if (verbose)
			{
				printf("Added job [%d] %d %s\n", jobs[i].jid,
					   (int)jobs[i].pid, jobs[i].cmdline);
			}
			return (1);
		}
	}
	printf("Tried to create too many jobs\n");
	return (0);
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures.
 *
 * Effects:
 *   Deletes a job from the jobs list whose PID equals "pid".
 */
static int
deletejob(JobP jobs, pid_t pid)
{
	int i;

	if (pid < 1)
		return (0);
	for (i = 0; i < MAXJOBS; i++)
	{
		if (jobs[i].pid == pid)
		{
			clearjob(&jobs[i]);
			nextjid = maxjid(jobs) + 1;
			return (1);
		}
	}
	return (0);
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures.
 *
 * Effects:
 *   Returns the PID of the current foreground job or 0 if no foreground
 *   job exists.
 */
static pid_t
fgpid(JobP jobs)
{
	int i;

	for (i = 0; i < MAXJOBS; i++)
		if (jobs[i].state == FG)
			return (jobs[i].pid);
	return (0);
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures.
 *
 * Effects:
 *   Returns a pointer to the job structure with process ID "pid" or NULL if
 *   no such job exists.
 */
static JobP
getjobpid(JobP jobs, pid_t pid)
{
	int i;

	if (pid < 1)
		return (NULL);
	for (i = 0; i < MAXJOBS; i++)
		if (jobs[i].pid == pid)
			return (&jobs[i]);
	return (NULL);
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures.
 *
 * Effects:
 *   Returns a pointer to the job structure with job ID "jid" or NULL if no
 *   such job exists.
 */
static JobP
getjobjid(JobP jobs, int jid)
{
	int i;

	if (jid < 1)
		return (NULL);
	for (i = 0; i < MAXJOBS; i++)
		if (jobs[i].jid == jid)
			return (&jobs[i]);
	return (NULL);
}

/*
 * Requires:
 *   Nothing.
 *
 * Effects:
 *   Returns the job ID for the job with process ID "pid" or 0 if no such
 *   job exists.
 */
static int
pid2jid(pid_t pid)
{
	int i;

	if (pid < 1)
		return (0);
	for (i = 0; i < MAXJOBS; i++)
		if (jobs[i].pid == pid)
			return (jobs[i].jid);
	return (0);
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures.
 *
 * Effects:
 *   Prints the jobs list.
 */
static void
listjobs(JobP jobs)
{
	int i;

	for (i = 0; i < MAXJOBS; i++)
	{
		if (jobs[i].pid != 0)
		{
			printf("[%d] (%d) ", jobs[i].jid, (int)jobs[i].pid);
			switch (jobs[i].state)
			{
			case BG:
				printf("Running ");
				break;
			case FG:
				printf("Foreground ");
				break;
			case ST:
				printf("Stopped ");
				break;
			default:
				printf("listjobs: Internal error: "
					   "job[%d].state=%d ",
					   i, jobs[i].state);
			}
			printf("%s", jobs[i].cmdline);
		}
	}
}

/*
 * This comment marks the end of the jobs list helper routines.
 */

/*
 * Other helper routines follow.
 */

/*
 * Requires:
 *   Nothing.
 *
 * Effects:
 *   Prints a help message.
 */
static void
usage(void)
{

	printf("Usage: shell [-hvp]\n");
	printf("   -h   print this message\n");
	printf("   -v   print additional diagnostic information\n");
	printf("   -p   do not emit a command prompt\n");
	exit(1);
}

/*
 * Requires:
 *   "msg" is a properly terminated string.
 *
 * Effects:
 *   Prints a Unix-style error message and terminates the program.
 */
static void
unix_error(const char *msg)
{

	fprintf(stdout, "%s: %s\n", msg, strerror(errno));
	exit(1);
}

/*
 * Requires:
 *   "msg" is a properly terminated string.
 *
 * Effects:
 *   Prints "msg" and terminates the program.
 */
static void
app_error(const char *msg)
{

	fprintf(stdout, "%s\n", msg);
	exit(1);
}

/*
 * Requires:
 *   The character array "s" is sufficiently large to store the ASCII
 *   representation of the long "v" in base "b".
 *
 * Effects:
 *   Converts a long "v" to a base "b" string, storing that string in the
 *   character array "s" (from K&R).  This function can be safely called by
 *   a signal handler.
 */
static void
sio_ltoa(long v, char s[], int b)
{
	int c, i = 0;

	do
		s[i++] = (c = v % b) < 10 ? c + '0' : c - 10 + 'a';
	while ((v /= b) > 0);
	s[i] = '\0';
	sio_reverse(s);
}

/*
 * Requires:
 *   "s" is a properly terminated string.
 *
 * Effects:
 *   Reverses a string (from K&R).  This function can be safely called by a
 *   signal handler.
 */
static void
sio_reverse(char s[])
{
	int c, i, j;

	for (i = 0, j = sio_strlen(s) - 1; i < j; i++, j--)
	{
		c = s[i];
		s[i] = s[j];
		s[j] = c;
	}
}

/*
 * Requires:
 *   "s" is a properly terminated string.
 *
 * Effects:
 *   Computes and returns the length of the string "s".  This function can be
 *   safely called by a signal handler.
 */
static size_t
sio_strlen(const char s[])
{
	size_t i = 0;

	while (s[i] != '\0')
		i++;
	return (i);
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Prints the long "v" to stdout using only functions that can be safely
 *   called by a signal handler, and returns either the number of characters
 *   printed or -1 if the long could not be printed.
 */
static ssize_t
sio_putl(long v)
{
	char s[128];

	sio_ltoa(v, s, 10);
	return (sio_puts(s));
}

/*
 * Requires:
 *   "s" is a properly terminated string.
 *
 * Effects:
 *   Prints the string "s" to stdout using only functions that can be safely
 *   called by a signal handler, and returns either the number of characters
 *   printed or -1 if the string could not be printed.
 */
static ssize_t
sio_puts(const char s[])
{

	return (write(STDOUT_FILENO, s, sio_strlen(s)));
}

/*
 * Requires:
 *   "s" is a properly terminated string.
 *
 * Effects:
 *   Prints the string "s" to stdout using only functions that can be safely
 *   called by a signal handler, and exits the program.
 */
static void
sio_error(const char s[])
{

	sio_puts(s);
	_exit(1);
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Prints the long "v" to stdout using only functions that can be safely
 *   called by a signal handler.  Either returns the number of characters
 *   printed or exits if the long could not be printed.
 */
static ssize_t
Sio_putl(long v)
{
	ssize_t n;

	if ((n = sio_putl(v)) < 0)
		sio_error("Sio_putl error");
	return (n);
}

/*
 * Requires:
 *   "s" is a properly terminated string.
 *
 * Effects:
 *   Prints the string "s" to stdout using only functions that can be safely
 *   called by a signal handler.  Either returns the number of characters
 *   printed or exits if the string could not be printed.
 */
static ssize_t
Sio_puts(const char s[])
{
	ssize_t n;

	if ((n = sio_puts(s)) < 0)
		sio_error("Sio_puts error");
	return (n);
}

/*
 * Requires:
 *   "s" is a properly terminated string.
 *
 * Effects:
 *   Prints the string "s" to stdout using only functions that can be safely
 *   called by a signal handler, and exits the program.
 */
static void
Sio_error(const char s[])
{

	sio_error(s);
}

// Prevent "unused function" and "unused variable" warnings.
static const void *dummy_ref[] = {Sio_error, Sio_putl, addjob, builtin_cmd,
								  deletejob, do_bgfg, dummy_ref, fgpid, getjobjid, getjobpid, listjobs,
								  parseline, pid2jid, signame, waitfg};
