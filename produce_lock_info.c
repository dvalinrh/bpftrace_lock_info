/*
 * Using the bpftrace functionality pull various pieces of data surronding the 
 * acquistion of calling mutex_lock.
 *
 * What is gathered (all based on stack back trace).
 *     1) # times the lock is aquired.
 *     2) Average time (ns) to acquire the lock.
 *     3) Maximum time (ns) to the acquirer the lock.
 *     4) # times the lock was released (may not == the number times acquired)
 *     5) Average time the lock is held for.
 *     6) Maximum time the lock is held for.
 *
 * Note: we do not have the actual lock name, we have the entry point it was called from.
 *
 * Once the data is acquired, the program then reduces the data to a summary of information.
 * The data is sorted by total acquistion time.
 *
 * usage:  produce_lock_info
 *   -c <command>: command to be executed.
 *   -f <pathname>: fle where bpftrace data is stored.
 *   -h: help message
 *   -o <pathname>: file to save the results to, if no output goes to stdout.
 *   -s <value>: how much of the stack to show and present data on, default = 1
 *
 * Example output:
 *
 *                   caller        # holds  Hold Max (ns)  Hold Avg (ns)         # ACQs  ACQS Max (ns)  ACQS Avg (ns)
 * kernfs_iop_permission+39          67713        3312432            934       25401012        3312432          66842
 * kernfs_dop_revalidate+55          41630        2992085            644       15676498        2992085          68830
 *    kernfs_iop_getattr+39          46174        1029183            881        3461649        1029183          66873
 *  kernfs_iop_get_link+106          20498         131714            893         592237         131714          78336
 *     kernfs_iop_lookup+34          26708          34432            881         466849          34432          36562
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <ctype.h>
#include <strings.h>
#include <signal.h>
#include <getopt.h>

#define DATA_FILE "/tmp/lock_data.out"
#define BPFTRACE "/tmp/lock_tracker.bt"
#define _SIGRTMAX SIGRTMAX-2 + 1

/*
 * Indexes into the lock data array.
 */
#define ACQ_DATA_HOLD_AVG 0
#define ACQ_DATA_HOLD_MAX 1
#define ACQ_DATA_HOLD_COUNT 2
#define ACQ_DATA_TOTAL_TIME 3
#define HD_DATA_HOLD_AVG 4
#define HD_DATA_HOLD_MAX 5
#define HD_DATA_HOLD_COUNT 6
#define HD_DATA_TOTAL_TIME 7

#define HOLDS 0
#define HOLDS_MAX 1
#define HOLDS_AVG 2
#define ACQS 3
#define ACQS_MAX 4
#define ACQS_AVG 5
#define ACQS_SPENT 6

/*
 * lock information structure.  The contents of called_from is determined by the -s option.
 */
struct lock_info {
	char *stack;
	char *called_from;
	long data[8];
};

/*
 * Data for the entire lock information.  There will be one entry for each unique stack.
 */
static struct lock_info *lock_data;
static size_t number_lock_entries = 0;

/*
 * Data that is consolidated based on called_from.
 */
static struct lock_info *cons_data;
static size_t number_cons_entries = 0;

/*
 * Comparison routines for qsort and bsearch.
 */

static int
locate_caller(const void *caller_ptr, const void *li_ptr)
{
        char *caller = (char *) caller_ptr;
        struct lock_info *li = (struct lock_info *) li_ptr;

        return (strcmp(caller, li->called_from));
}

static int
locate_stack(const void *stack_ptr, const void *li_ptr)
{
        char *stack = (char *) stack_ptr;
        struct lock_info *li = (struct lock_info *) li_ptr;

        return (strcmp(stack, li->stack));
}

static int
sort_func(const void *l1_ptr, const void *l2_ptr)
{
        struct lock_info *l1 = (struct lock_info *) l1_ptr;
        struct lock_info *l2 = (struct lock_info *) l2_ptr;

        return (strcmp(l1->called_from, l2->called_from));
}

static int
sort_stack(const void *l1_ptr, const void *l2_ptr)
{
        struct lock_info *l1 = (struct lock_info *) l1_ptr;
        struct lock_info *l2 = (struct lock_info *) l2_ptr;

        return (strcmp(l1->stack, l2->stack));
}

static int
sort_aq_spin(const void *l1_ptr, const void *l2_ptr)
{
        struct lock_info *l1 = (struct lock_info *) l1_ptr;
        struct lock_info *l2 = (struct lock_info *) l2_ptr;

	if (l1->data[ACQ_DATA_TOTAL_TIME] < l2->data[ACQ_DATA_TOTAL_TIME])
		return(1);
	if (l1->data[ACQ_DATA_TOTAL_TIME] > l2->data[ACQ_DATA_TOTAL_TIME])
		return(-1);
	return(0);
}

static int
sort_aq_average(const void *l1_ptr, const void *l2_ptr)
{
        struct lock_info *l1 = (struct lock_info *) l1_ptr;
        struct lock_info *l2 = (struct lock_info *) l2_ptr;

	if (l1->data[ACQ_DATA_HOLD_AVG] < l2->data[ACQ_DATA_HOLD_AVG])
		return(1);
	if (l1->data[ACQ_DATA_HOLD_AVG] > l2->data[ACQ_DATA_HOLD_AVG])
		return(-1);
	return(0);
}

static int
sort_aq_count(const void *l1_ptr, const void *l2_ptr)
{
        struct lock_info *l1 = (struct lock_info *) l1_ptr;
        struct lock_info *l2 = (struct lock_info *) l2_ptr;

	if (l1->data[ACQ_DATA_HOLD_COUNT] < l2->data[ACQ_DATA_HOLD_COUNT])
		return(1);
	if (l1->data[ACQ_DATA_HOLD_COUNT] > l2->data[ACQ_DATA_HOLD_COUNT])
		return(-1);
	return(0);
}

static int
sort_aq_max(const void *l1_ptr, const void *l2_ptr)
{
        struct lock_info *l1 = (struct lock_info *) l1_ptr;
        struct lock_info *l2 = (struct lock_info *) l2_ptr;

	if (l1->data[ACQ_DATA_HOLD_MAX] < l2->data[ACQ_DATA_HOLD_MAX])
		return(1);
	if (l1->data[ACQ_DATA_HOLD_MAX] > l2->data[ACQ_DATA_HOLD_MAX])
		return(-1);
	return(0);
}

static int
sort_hold_avg(const void *l1_ptr, const void *l2_ptr)
{
        struct lock_info *l1 = (struct lock_info *) l1_ptr;
        struct lock_info *l2 = (struct lock_info *) l2_ptr;

	if (l1->data[HD_DATA_HOLD_AVG] < l2->data[HD_DATA_HOLD_AVG])
		return(1);
	if (l1->data[HD_DATA_HOLD_AVG] > l2->data[HD_DATA_HOLD_AVG])
		return(-1);
	return(0);
}

static int
sort_hold_count(const void *l1_ptr, const void *l2_ptr)
{
        struct lock_info *l1 = (struct lock_info *) l1_ptr;
        struct lock_info *l2 = (struct lock_info *) l2_ptr;

	if (l1->data[HD_DATA_HOLD_COUNT] < l2->data[HD_DATA_HOLD_COUNT])
		return(1);
	if (l1->data[HD_DATA_HOLD_COUNT] > l2->data[HD_DATA_HOLD_COUNT])
		return(-1);
	return(0);
}

static int
sort_hold_max(const void *l1_ptr, const void *l2_ptr)
{
        struct lock_info *l1 = (struct lock_info *) l1_ptr;
        struct lock_info *l2 = (struct lock_info *) l2_ptr;

	if (l1->data[HD_DATA_HOLD_MAX] < l2->data[HD_DATA_HOLD_MAX])
		return(1);
	if (l1->data[HD_DATA_HOLD_MAX] > l2->data[HD_DATA_HOLD_MAX])
		return(-1);
	return(0);
}

static int
sort_hold_total(const void *l1_ptr, const void *l2_ptr)
{
        struct lock_info *l1 = (struct lock_info *) l1_ptr;
        struct lock_info *l2 = (struct lock_info *) l2_ptr;

	if (l1->data[HD_DATA_TOTAL_TIME] < l2->data[HD_DATA_TOTAL_TIME])
		return(1);
	if (l1->data[HD_DATA_TOTAL_TIME] > l2->data[HD_DATA_TOTAL_TIME])
		return(-1);
	return(0);
}

/*
 *  Simply remove the new line at the end of the stirng.
 */
static void
remove_new_line(char *buffer)
{
	char *ptr;

	ptr = strchr(buffer, '\n');
	if (ptr) {
		ptr[0] = ' ';
		ptr[1] = '\0';
	} else {
		fprintf(stderr, "malformed line: %s\n", buffer);
		exit(EXIT_FAILURE);
	}
}

/*
 * Read in the data from the bpftrace data file.  
 * fd: file reading from
 * index: index of the data field being read.
 * sdepth: how much of the stack to show.
 *
 *  Reads in the data from the file until '=' is seen as the first character.  When found,
 *  indicates that the section of this particular data is complete.
 */
static void
read_data(FILE *fd, int index, int sdepth)
{
	char *ptr;
	struct lock_info *data_ptr;
	long value;
	char buffer[1024];
	char func_called[1024];
	char stack_in[8192];
	int depth = 0;
	int need_add_stack = 0;
	int have_function = 0;

	for (;;) {
		(void) fgets(buffer, 1024, fd);
		/* Keep reading until end of section is hit */
		if (buffer[0] == '=')
			break;
		/* Check to make sure it is not an empty piece of data */
		if (strstr(buffer, "[]"))
			continue;
		/* Start of a new function stack? */
		if (buffer[0] == '@') {
			have_function = 0;
			continue;
		}
		/* Grab the functon? */
		remove_new_line(buffer);
		if (have_function == 0) {
			stack_in[0] = '\0';
			strcpy(stack_in, buffer);
			/* Line we have now, is mutex_lock */
			(void) fgets(buffer, 1024, fd);
			/* We now have the function */
			have_function = 1;
			remove_new_line(buffer);
			ptr = strrchr(buffer, ' ');
			ptr[0] = ':';
			ptr[1] = '\0';
			strcpy(func_called, buffer);
			strcat(stack_in,buffer);
			depth = 1;
			continue;
		}
		/*
		 * End of the stack, record the entry as well as the count of times.
		 */
		if (buffer[0] == ']') {
			depth = 0;
			/* end of data */
			ptr  = strchr(buffer, ':');
			if (ptr) {
				value = atoll(&ptr[1]);
			} else {
				fprintf(stderr, "malformed line: %s\n", buffer);
				exit(EXIT_FAILURE);
			}
			/*
			 * Add the entry.
			 */
			if (number_lock_entries == 0) {
				lock_data = data_ptr = (struct lock_info *) malloc(sizeof(struct lock_info));
				number_lock_entries++;
				need_add_stack = 1;
			} else {
				/*
				 * We may have the stack already, go look for it.
				 */
				data_ptr = (struct lock_info *) bsearch(stack_in, lock_data, number_lock_entries,
				    sizeof (struct lock_info), locate_stack);
				if (data_ptr == NULL) {
					/*
					 * stack is not present, need to add the appropriate entry.
					 */
					need_add_stack = 1;
					number_lock_entries++;
					lock_data = (struct lock_info *) realloc(lock_data, sizeof (struct lock_info) * number_lock_entries);
					data_ptr = &lock_data[number_lock_entries - 1];
				}
			}
			if (need_add_stack) {
				/*
				 * Init the place saving the data and then set the fields accordingly.
				 * Do not forget to qsort it if need be.
				 */
				need_add_stack = 0;
				bzero(data_ptr, sizeof (struct lock_info));
				data_ptr->stack = strdup(stack_in);
				data_ptr->called_from = strdup(func_called);
				data_ptr->data[index] = value;
				qsort(lock_data, number_lock_entries, sizeof (struct lock_info), sort_stack);
			} else
				/*
				 * Update the value.
				 */
				data_ptr->data[index] += value;
			continue;
		}
		/*
		 * All we need to do is add the function to the stack.
		 */
		strcat(stack_in,buffer);
		if (depth < sdepth) {
			/*
			 * keep adding to funcv_called, until the designated stack depth is reached.
			 */
			depth++;
			ptr = strrchr(buffer, ' ');
			ptr[0] = ':';
			ptr[1] = '\0';
			strcat(func_called, buffer);
		}
	}
}

/*
 * Walk through the various data areas of the bpftrace output file.
 * Note, any change in format of the output file, needs to be reflected
 * here.
 */
static void
lookup_data(char *file, int sdepth)
{
	FILE *fd;
	char buffer[1024];

	fd = fopen(file, "r");
	if (fd == NULL) {
		perror(file);
		exit(EXIT_FAILURE);
	}

	/*
	 * First we have  aq data, skip the headers
	 */
	(void) fgets(buffer, 1024, fd);
	(void) fgets(buffer, 1024, fd);

	/* Now read the data in */
	(void) fgets(buffer, 1024, fd);
	(void) fgets(buffer, 1024, fd);
	read_data(fd, ACQ_DATA_HOLD_AVG, sdepth);

	(void) fgets(buffer, 1024, fd);
	(void) fgets(buffer, 1024, fd);
	read_data(fd, ACQ_DATA_HOLD_MAX, sdepth);

	(void) fgets(buffer, 1024, fd);
	(void) fgets(buffer, 1024, fd);
	read_data(fd, ACQ_DATA_HOLD_COUNT, sdepth);

	(void) fgets(buffer, 1024, fd);
	(void) fgets(buffer, 1024, fd);
	read_data(fd, HD_DATA_HOLD_AVG, sdepth);

	(void) fgets(buffer, 1024, fd);
	(void) fgets(buffer, 1024, fd);
	read_data(fd, HD_DATA_HOLD_MAX, sdepth);

	(void) fgets(buffer, 1024, fd);
	(void) fgets(buffer, 1024, fd);
	read_data(fd, HD_DATA_HOLD_COUNT, sdepth);
	
	(void) fclose(fd);
}

/*
 * Consdolidate the data based on matches with field called_from.
 */
static void
organize_data()
{
	struct lock_info *wptr;
	struct lock_info *entry_add;
	long new_average;
	size_t count;
	int add_entry;

	qsort(lock_data, number_lock_entries, sizeof (struct lock_info), sort_func);

	for (count = 0; count < number_lock_entries; count++) {
		add_entry = 0;
		wptr = &lock_data[count];
		if (count == 0) {
			/* First entry */
			cons_data = entry_add = (struct lock_info *) malloc(sizeof(struct lock_info));
			add_entry = 1;
		} else {
			/* Look up entry */
			entry_add = (struct lock_info *) bsearch(wptr->called_from, cons_data, number_cons_entries,
			    sizeof (struct lock_info), locate_caller);
			if (entry_add == NULL) {
				/* New entry */
				add_entry =  1;
				number_cons_entries++;
				cons_data = (struct lock_info *) realloc(cons_data, sizeof (struct lock_info)*number_cons_entries);
				entry_add = &cons_data[number_cons_entries - 1];
			}
		}
		if (add_entry) {
			bzero(entry_add, sizeof (struct lock_info));
			entry_add->called_from = wptr->called_from;
		}
		/* Now add things up. */

		/* Adjust average */
		new_average = entry_add->data[ACQ_DATA_HOLD_AVG]*entry_add->data[ACQ_DATA_HOLD_COUNT] +
		    wptr->data[ACQ_DATA_HOLD_AVG]*wptr->data[ACQ_DATA_HOLD_COUNT];
		entry_add->data[ACQ_DATA_HOLD_COUNT] += wptr->data[ACQ_DATA_HOLD_COUNT];

		if (entry_add->data[ACQ_DATA_HOLD_COUNT])
			entry_add->data[ACQ_DATA_HOLD_AVG] = new_average/entry_add->data[ACQ_DATA_HOLD_COUNT];

		new_average = entry_add->data[HD_DATA_HOLD_AVG]*entry_add->data[HD_DATA_HOLD_COUNT] +
		    wptr->data[HD_DATA_HOLD_AVG]*wptr->data[HD_DATA_HOLD_COUNT];
		entry_add->data[HD_DATA_HOLD_COUNT] += wptr->data[HD_DATA_HOLD_COUNT];

		if (entry_add->data[HD_DATA_HOLD_COUNT])
			entry_add->data[HD_DATA_HOLD_AVG] = new_average/entry_add->data[HD_DATA_HOLD_COUNT];

		/* Now adjust the max hold if need be */
		if (entry_add->data[ACQ_DATA_HOLD_MAX] < wptr->data[ACQ_DATA_HOLD_MAX])
			entry_add->data[ACQ_DATA_HOLD_MAX] = wptr->data[ACQ_DATA_HOLD_MAX];

		if (entry_add->data[HD_DATA_HOLD_MAX] < wptr->data[HD_DATA_HOLD_MAX])
			entry_add->data[HD_DATA_HOLD_MAX] = wptr->data[HD_DATA_HOLD_MAX];
	}
}

/*
 * Dump the lock information.
 */
static void
dump_data(char *output_file, char *caller, int sort_option, int numb_to_show)
{
	FILE *fd;
	size_t count;
	char *ptr, *ptr1, *ptr2;
	char buffer[8192];
	int stack_depth;

	if (output_file) {
		fd = fopen(output_file, "w");
		if (fd == NULL) {
			fd = stdout;
			perror(output_file);
			fprintf(stderr, "opening %s failed, falling back to stdout\n", output_file);
		}
	} else {
		fd = stdout;
	}
	for (count = 0; count < number_cons_entries; count++) {
		cons_data[count].data[ACQ_DATA_TOTAL_TIME] =
		   cons_data[count].data[ACQ_DATA_HOLD_AVG] * cons_data[count].data[ACQ_DATA_HOLD_COUNT];
		cons_data[count].data[HD_DATA_TOTAL_TIME] =
		   cons_data[count].data[HD_DATA_HOLD_AVG] * cons_data[count].data[HD_DATA_HOLD_COUNT];
	}

	switch (sort_option) {
		case 0:
			qsort(cons_data, number_cons_entries, sizeof (struct lock_info), sort_hold_count);
		break;
		case 1:
			qsort(cons_data, number_cons_entries, sizeof (struct lock_info), sort_hold_max);
		break;
		case 2:
			qsort(cons_data, number_cons_entries, sizeof (struct lock_info), sort_hold_avg);
		break;
		case 3:
			qsort(cons_data, number_cons_entries, sizeof (struct lock_info), sort_hold_total);
		break;
		case 4:
			qsort(cons_data, number_cons_entries, sizeof (struct lock_info), sort_aq_count);
		break;
		case 5:
			qsort(cons_data, number_cons_entries, sizeof (struct lock_info), sort_aq_max);
		break;
		case 6:
			qsort(cons_data, number_cons_entries, sizeof (struct lock_info), sort_aq_average);
		break;
		case 7:
		default:
			qsort(cons_data, number_cons_entries, sizeof (struct lock_info), sort_aq_spin);
		break;
	}

	fprintf(fd, "%48s%15s%15s%15s%15s%15s%15s\n",
	   "caller", "# holds", "Hold Max (ns)", "Hold Avg (ns)", "# ACQs", "ACQs Max (ns)", "ACQs Avg (ns)");
	if (numb_to_show < number_cons_entries)
		number_cons_entries = numb_to_show;
	for (count = 0;count < number_cons_entries; count++) {
		stack_depth = 0;
		if (cons_data[count].called_from != NULL) {
			ptr = strchr(cons_data[count].called_from, ':');
			if (ptr)
				ptr[0] = '\0';
			if (caller != NULL && stack_depth == 0) {
				strcpy(buffer, cons_data[count].called_from);
				ptr1 = buffer;
				while(isspace(ptr1[0]))
				       ptr1++;
				ptr2 = strchr(ptr1, ' ');
				if (ptr2)
					ptr2[0] = '\0';
				if (strcmp(ptr1, caller))
					continue;
			}
			stack_depth++;
			fprintf(fd, "%48s%15ld%15ld%15ld%15ld%15ld%15ld\n", cons_data[count].called_from, 
			   cons_data[count].data[HD_DATA_HOLD_COUNT], cons_data[count].data[HD_DATA_HOLD_MAX],
			      cons_data[count].data[HD_DATA_HOLD_AVG],
			   cons_data[count].data[ACQ_DATA_HOLD_COUNT], cons_data[count].data[ACQ_DATA_HOLD_MAX],
			      cons_data[count].data[ACQ_DATA_HOLD_AVG]);
			if (ptr) {
				ptr = &ptr[1];
				while(ptr[0] != '\0') {
					ptr1 = strchr(ptr, ':');
					if(ptr1)
						ptr1[0] = '\0';
					fprintf(fd, "%48s\n", ptr);
					ptr = ptr1;
					if (ptr)
						ptr++;
				}
			}

		}
	}
}

static void
usage(char *execname)
{
	fprintf(stderr, "usage %s:\n", execname);
	fprintf(stderr, "\t-C <func name> Just those stacks that the lock was called from this function\n");
	fprintf(stderr, "\t-c <command> command to execute, if null, will reduce the data designated by -f\n");
	fprintf(stderr, "\t-f <file name> name of data file to read from\n");
	fprintf(stderr, "\t-h: help message\n");
	fprintf(stderr, "\t-i <secs>: pull lock information every x seconds\n");
	fprintf(stderr, "\t-n <#>: Number of locks to show.\n");
	fprintf(stderr, "\t-o <file name>: output file\n");
	fprintf(stderr, "\t-s <value> depth of stack to show\n");
	fprintf(stderr, "\t-S <sort on>: recognized values\n");
	fprintf(stderr, "\t\t0: # holds\n");
	fprintf(stderr, "\t\t1: Hold Max\n");
	fprintf(stderr, "\t\t2: Hold Avg\n");
	fprintf(stderr, "\t\t3: Hold total\n");
	fprintf(stderr, "\t\t4: # ACQs\n");
	fprintf(stderr, "\t\t5: # ACQs Max\n");
	fprintf(stderr, "\t\t6: # ACQs average\n");
	fprintf(stderr, "\t\t7: # ACQs total time (AVG * count), default\n");
	exit(EXIT_SUCCESS);
}

/*
 * Generate the required bpftrace script.
 */
static void
bpftrace_create(int interval)
{
	FILE *fd;
	char buffer[8192];

	fd = fopen(BPFTRACE, "w");
	if (fd == NULL) {
		perror(BPFTRACE);
		exit(EXIT_FAILURE);
	}

	fprintf(fd, "#!/usr/local/bin/bpftrace\n\n");
	if (interval) {
		strcpy(buffer, "@interval,");
		fprintf(fd, "BEGIN\n{\n	@interval = 1;\n}\n\n");
	} else {
		buffer[0] = '\0';
	}


	fprintf(fd, "kprobe:mutex_lock\n");
	fprintf(fd, "{\n");
	fprintf(fd, "\t@track[tid] = 1;\n");
	fprintf(fd, "\t@stack[tid, @lock_depth[tid]] = kstack();\n");
	fprintf(fd, "\t@time[tid] = nsecs;\n");
	fprintf(fd, "\t@lock_depth[tid] = @lock_depth[tid] + 1;\n");
	fprintf(fd, "}\n");
	fprintf(fd, "kretprobe:mutex_lock\n");
	fprintf(fd, "\t/ @track[tid] == 1 /\n");
	fprintf(fd, "{\n");
	fprintf(fd, "\t$temp = nsecs;\n");
	fprintf(fd, "\tif ($temp > @time[tid]) {\n");
	fprintf(fd, "\t\t@aq_report_avg[%s @stack[tid, @lock_depth[tid] -1]] = avg($temp - @time[tid]);\n", buffer);
	fprintf(fd, "\t\t@aq_report_max[%s @stack[tid, @lock_depth[tid] -1]] = max($temp - @time[tid]);\n", buffer);
	fprintf(fd, "\t\t@aq_report_count[%s @stack[tid, @lock_depth[tid] -1]] = count();\n", buffer);
	fprintf(fd, "\t}\n");
	fprintf(fd, "\t@time_held[tid, @lock_depth[tid] - 1] = nsecs;\n");
	fprintf(fd, "\t@track[tid] = 0;\n");
	fprintf(fd, "}\n\n");


	fprintf(fd, "kprobe:mutex_unlock\n");
	fprintf(fd, "\t/ @lock_depth[tid] > 0 /\n");
	fprintf(fd, "{\n");
	fprintf(fd, "\t$temp = nsecs;\n");
	fprintf(fd, "\t@lock_depth[tid] = @lock_depth[tid] - 1;\n");
	fprintf(fd, "\tif ($temp > @time_held[tid, @lock_depth[tid]]) {\n");
	fprintf(fd, "\t\t$val = $temp - @time_held[tid, @lock_depth[tid]];\n");
	fprintf(fd, "\t\tif ($val < 1000000000) {\n");
	fprintf(fd, "\t\t\t@hl_histo = hist($val);\n");
	fprintf(fd, "\t\t\t@hl_report_avg[%s @stack[tid, @lock_depth[tid]]] = avg($val);\n", buffer);
	fprintf(fd, "\t\t\t@hl_report_max[%s @stack[tid, @lock_depth[tid]]] = max($val);\n", buffer);
	fprintf(fd, "\t\t\t@hl_report_count[%s @stack[tid, @lock_depth[tid]]] = count();\n", buffer);
	fprintf(fd, "\t\t}\n");
	fprintf(fd, "\t}\n");
	fprintf(fd, "\tdelete(@stack[tid, @lock_depth[tid]]);\n");
	fprintf(fd, "\tdelete(@time_held[tid, @lock_depth[tid]]);\n");
	fprintf(fd, "}\n");

	if (interval) {
		fprintf(fd, "interval:s:%d\n", interval);
		fprintf(fd, "{\n	@interval = @interval + 1;\n}\n");
	}

	fprintf(fd, "END\n");
	fprintf(fd, "{\n");
	fprintf(fd, "\tprintf(\"========================================\\n\");\n");
	fprintf(fd, "\tprintf(\"mutex aq _averages\\n\");\n");
	fprintf(fd, "\tprintf(\"========================================\\n\");\n");
	fprintf(fd, "\tprint(@aq_report_avg);\n");

	fprintf(fd, "\tprintf(\"========================================\\n\");\n");
	fprintf(fd, "\tprintf(\"mutex aq max\\n\");\n");
	fprintf(fd, "\tprintf(\"========================================\\n\");\n");
	fprintf(fd, "\tprint(@aq_report_max);\n");

	fprintf(fd, "\tprintf(\"========================================\\n\");\n");
	fprintf(fd, "\tprintf(\"mutex aq count\\n\");\n");
	fprintf(fd, "\tprintf(\"========================================\\n\");\n");
	fprintf(fd, "\tprint(@aq_report_count);\n");

	fprintf(fd, "\tprintf(\"========================================\\n\");\n");
	fprintf(fd, "\tprintf(\"mutex hold avg\\n\");\n");
	fprintf(fd, "\tprintf(\"========================================\\n\");\n");
	fprintf(fd, "\tprint(@hl_report_avg);\n");

	fprintf(fd, "\tprintf(\"========================================\\n\");\n");
	fprintf(fd, "\tprintf(\"mutex hold max\\n\");\n");
	fprintf(fd, "\tprintf(\"========================================\\n\");\n");
	fprintf(fd, "\tprint(@hl_report_max);\n");

	fprintf(fd, "\tprintf(\"========================================\\n\");\n");
	fprintf(fd, "\tprintf(\"mutex hold count\\n\");\n");
	fprintf(fd, "\tprintf(\"========================================\\n\");\n");
	fprintf(fd, "\tprint(@hl_report_count);\n");

	fprintf(fd, "\tprintf(\"=======================================\\n\");\n");
	fprintf(fd, "\tprintf(\"END OF DATA\\n\");\n");
	fprintf(fd, "\tprintf(\"=======================================\\n\");\n");
	fprintf(fd, "\tclear(@track);\n");
	fprintf(fd, "\tclear(@stack);\n");
	fprintf(fd, "\tclear(@time_held);\n");
	fprintf(fd, "\tclear(@time);\n");
	fprintf(fd, "\tclear(@lock_depth);\n");
	fprintf(fd, "\tdelete(@lock_depth);\n");
	fprintf(fd, "\tdelete(@hl_report_avg);\n");
	fprintf(fd, "\tdelete(@hl_report_max);\n");
	fprintf(fd, "\tdelete(@hl_report_count);\n");
	fprintf(fd, "\tdelete(@aq_report_avg);\n");
	fprintf(fd, "\tdelete(@aq_report_max);\n");
	fprintf(fd, "\tdelete(@aq_report_count);\n");
	fprintf(fd, "\tdelete(@time_held);\n");
	fprintf(fd, "\tdelete(@track);\n");
	fprintf(fd, "\tdelete(@stack);\n");
	fprintf(fd, "\tdelete(@time);\n");
	fprintf(fd, "}\n");
	fclose(fd);
	sprintf(buffer, "chmod 755 %s", BPFTRACE);
	(void) system(buffer);
}

/*
 * Simple stub to goto on a signal.
 */
static void
pause_stub()
{
}

/*
 * Start the bpftrace script, and then execute the command.  When the command is complete,
 * terminate the bpftrace script.  We can not simply do bpftrace -c <command> ./script > file
 * due to the fact that will redirect all stdout from the command as well as the script, which
 * is not desired.
 */
static void
execute_command(char *command, char *file)
{
	pid_t bpftrace_pid;
	pid_t command_pid;
	char cmd_buffer[8192];
	char buffer[1024];
	int status;
	struct sigaction action, p_action;
	int count;
	FILE *fd;
	char *ptr;
	int field = 0;

	/*
	 * Always start bpftrace first.
	 */

	if ((bpftrace_pid = fork()) == 0) {
		/* bpftrace child */
		sprintf(cmd_buffer, "%s > %s", BPFTRACE, file);
		if ((bpftrace_pid = fork()) == 0) {
			(void) system(cmd_buffer);
			exit(EXIT_SUCCESS);
		}
		if (bpftrace_pid < 0)
			perror("fork");
		bzero(&action, sizeof (struct sigaction));
		action.sa_sigaction = pause_stub;
		(void) sigemptyset(&action.sa_mask);
		action.sa_flags = 0;

		for (count = 0; count < _SIGRTMAX; count++) {
			if (count != SIGCHLD &&
			   count != SIGTSTP && count != SIGALRM &&
			   count != SIGSEGV) {
				sigaction(count, &action, &p_action);
                	}
        	}
		(void) pause();
		/* Find the pid for bpftrace and then sigint it */

		(void) system("ps -efl |grep bpftrace |grep local > /tmp/junk");
		fd =fopen("/tmp/junk","r");
		while(fgets(buffer, 1024, fd)) {
			if (strstr(buffer, "/usr/local/bin/bpftrace"))
				break;
		}
		fclose(fd);
		ptr = buffer;
		/* Skip the fields, as there may be multiple spaces.... */
		while (field != 3) {
			while (isspace(ptr[0]))
				ptr++;
			field++;
			while (!isspace(ptr[0]))
				ptr++;
		}
		kill(atoi(ptr), SIGINT);

		(void) waitpid(bpftrace_pid, &status, 0);
		exit(EXIT_SUCCESS);
	}
	/* Give it a chance */
	(void) sleep(5);
	if ((command_pid = fork()) == 0) {
		/* command  child */
		(void) system(command);
		exit(EXIT_SUCCESS);
	}
	/* Wait for the command to complete */
	(void) waitpid(command_pid, &status, 0);

	/* Command is complete, kill off bpftrace script. */

	kill(bpftrace_pid, SIGINT);
	/* Wait for the bpftrace to complete */
	(void) waitpid(bpftrace_pid, &status, 0);
}

static void
obtain_run_data(char *command, char *file, int interval)
{
	bpftrace_create(interval);
	execute_command(command, file);
}

int
main(int argc, char **argv)
{
	char *file = NULL;
	int stack_depth = 1;
	char value;
	char *command = NULL;
	char *caller = NULL;
	char *output_file = NULL;
	int sort_on = ACQS_SPENT;
	int interval = 0;
	int number_to_show = 999999;

	while ((optind != argc) &&
	    (value = (char)  getopt(argc, argv, "C:c:f:ho:n:s:S:i:"))) {
		switch(value) {
			case 'C':
				caller = optarg;
			break;
			case 'c':
				command = optarg;
			break;
			case 'f':
				file = optarg;
			break;
			case 'i':
				fprintf(stderr,
				   "Currently interval is not supported, hangs\n");
#if 0
				interval = atoi(optarg);
#endif
			break;
			case 'n':
				number_to_show = atoi(optarg);
			break;
			case 'o':
				output_file = optarg;
			break;
			case 'S':
				sort_on = atoi(optarg);
				if (sort_on > ACQS_SPENT) {
					fprintf(stderr, "Invalid sort option, defaulting to option 6\n");
					sort_on = ACQS_SPENT;
				}
			break;
			case 's':
				stack_depth = atoi(optarg);
			break;
			case 'h':
			default:
				usage(argv[0]);
			break;
		}
        }

	if (file == NULL)
		file = DATA_FILE;
	/*
	 * Run the command and bpftrace if required.
	 */
	if (command) {
		obtain_run_data(command, file, interval);
	}
	if (interval == 0) {
		lookup_data(file, stack_depth);
		/* Everything read in, now organize it */
		organize_data();
		/* Dump the data out. */
		dump_data(output_file, caller, sort_on, number_to_show);
	}
	return(0);
}
