#include <types.h>
#include <lib.h>
#include <mips/trapframe.h>
#include <kern/errno.h>
#include <kern/fcntl.h>
#include <kern/wait.h>
#include <addrspace.h>
#include <synch.h>
#include <current.h>
#include <copyinout.h>
#include <vfs.h>
#include <syscall.h>
#include <kern/process_syscalls.h>
#include <proc.h>
#include <kern/file_syscalls.h>
#include <vnode.h>
#include <addrspace.h>
#include <mips/tlb.h>
#include <spl.h>


/* Spawning a new process id */

pid_t
spawn_pid(struct proc *proc, int *err) {

    int i = PID_MIN;
    while(proc_ids[i] != NULL && i < PID_MAX_256) {
        i++;
    }

    if (i < PID_MAX_256) {
        proc_ids[i] = proc;

        if(proc_ids[i] == NULL) {
            *err = ENOMEM;
            return -1;
        }

        return i;
    }

    *err = EMPROC;
    return -1;
}

/* Get id of current process */

pid_t
sys_getpid() {
    return curproc->pid;
}

/* Custom implementation of fork kernel system call */

int
sys_fork(struct trapframe* tf, int *err) {
    struct trapframe* childtf = NULL;
    struct proc* childproc = NULL;
    struct addrspace* childaddr = NULL;

    int result;

    childtf = kmalloc(sizeof(struct trapframe));
    if(childtf == NULL){
        *err = ENOMEM;
        return -1;
    }

    memcpy(childtf, tf, sizeof(struct trapframe));

    result = as_copy(curproc->p_addrspace, &childaddr);
    if(childaddr == NULL){
        kfree(childtf);
        *err = ENOMEM;
        return -1;
    }

    childproc = proc_create_child("child");
    if(childproc == NULL){
        kfree(childtf);
        *err = ENOMEM;
        return -1;
    }

    result = thread_fork("process", childproc, child_forkentry, childtf,
                         (unsigned long) childaddr);

    if(result) {
        return result;
    }

    result = childproc->pid;
    childproc->p_cwd = curproc->p_cwd;
    VOP_INCREF(curproc->p_cwd);
    curproc->p_numthreads++;
    return result;
}

void
child_forkentry(void *data1, unsigned long data2){

    struct trapframe st_trapframe;
    struct trapframe* childtf = (struct trapframe*) data1;
    struct addrspace* childaddr = (struct addrspace*) data2;

    childtf->tf_v0 = 0;
    childtf->tf_a3 = 0;
    childtf->tf_epc += 4;

    memcpy(&st_trapframe, childtf, sizeof(struct trapframe));
    kfree(childtf);
    childtf = NULL;

    curproc->p_addrspace = childaddr;
    as_activate();

    mips_usermode(&st_trapframe);
};

/* Custom implementation of exec kernel system call */

int
sys_execv(char *progname, char **args, int *err) {

    struct addrspace *as;
    struct vnode *v;
    vaddr_t entrypoint, stackptr;
    int result;

    /* Validations */
    if (progname == NULL) {
        *err = EFAULT;
        return -1;
    }

    if (args == NULL || (int *)args == (int *)0x40000000 || (int *)args == (int *)0x80000000) {
        *err = EFAULT;
        return -1;
    }

    /* Count number of arguments and total size of input */
    int args_count = 0;
    for (;args_count < ARG_MAX && args[args_count] != NULL; args_count++);

    if (args_count > ARG_MAX) {
        *err = E2BIG;
        return -1;
    }

    /* Copy File name */
    char *progname_copy = (char *) kmalloc(sizeof(char) * NAME_MAX);
    size_t actual = 0;
    result = copyinstr((userptr_t)progname, progname_copy, NAME_MAX, &actual);

    if (result) {
        kfree(progname_copy);
        *err = result;
        return -1;
    }

    if (strlen(progname_copy) == 0) {
        kfree(progname_copy);
        *err = EINVAL;
        return -1;
    }

    /* Allocate Kernel Memory for arguments */
    char **args_copy = (char **) kmalloc(sizeof(char *) * args_count);

    int c_args_count = 0,
            arg_size = 0,
            padded_size = 0;

    for (;c_args_count < args_count; c_args_count++) {
        if ((int *)args[c_args_count] == (int *)0x40000000 || (int *)args[c_args_count] == (int *)0x80000000) {
            kfree(progname_copy);
            *err = EFAULT;
            return -1;
        }
    }

    c_args_count = 0;
    /* Calculate total length accounting for padding */
    for (;c_args_count < args_count; c_args_count++) {
        arg_size = strlen(args[c_args_count]) + 1;

        args_copy[c_args_count] = (char *) kmalloc(sizeof(char) * arg_size);
        copyinstr((userptr_t)args[c_args_count], args_copy[c_args_count], arg_size, &actual);

        padded_size += arg_size;
        if (padded_size % 4) {
            padded_size += (4 - (padded_size % 4)) % 4;
        }
    }

    /* Open the file. */
    result = vfs_open(progname_copy, O_RDONLY, 0, &v);
    if (result) {
        kfree(progname_copy);
        *err = result;
        return -1;
    }

    /* Destroy the current process's address space to create a new one. */
    as = curproc->p_addrspace;
    curproc->p_addrspace = NULL;

    as_destroy(as);

    /* We should be a new process. */
    KASSERT(proc_getas() == NULL);

    /* Create a new address space. */
    as = as_create();
    if (as == NULL) {
        kfree(progname_copy);
        vfs_close(v);
        *err = ENOMEM;
        return -1;
    }

    /* Switch to it and activate it. */
    proc_setas(as);
    as_activate();

    /* Load the executable. */
    result = load_elf(v, &entrypoint);
    if (result) {
        /* p_addrspace will go away when curproc is destroyed */
        kfree(progname_copy);
        vfs_close(v);
        *err = result;
        return -1;
    }

    /* Done with the file now. */
    vfs_close(v);

    /* Define the user stack in the address space */
    result = as_define_stack(as, &stackptr);
    if (result) {
        /* p_addrspace will go away when curproc is destroyed */
        kfree(progname_copy);
        *err = result;
        return -1;
    }

    stackptr -= padded_size;
    char **arg_address = (char **) kmalloc(sizeof(char *) * args_count + 1);

    /* Copy arguments into user stack */
    for(int i = 0; i < args_count; i++) {
        arg_size = strlen(args_copy[i]) + 1;

        if (arg_size % 4) {
            arg_size += (4 - arg_size % 4) % 4;
        }

        /* Store address of arguments */
        arg_address[i] = (char *)stackptr;

        copyoutstr(args_copy[i], (userptr_t)stackptr, arg_size, &actual);
        stackptr += arg_size;
    }

    /* Add Null Pointer at the end */
    arg_address[args_count] = 0;

    stackptr -= padded_size;
    stackptr -= (args_count + 1) * sizeof(char *);

    /* Copy address locations into user stack*/
    for (int i = 0; i < args_count + 1; i++) {
        copyout((arg_address + i), (userptr_t)stackptr, sizeof(char *));
        stackptr += sizeof(char *);
    }

    /* Reset pointer to start of the stack */
    stackptr -= ((args_count + 1) * sizeof(char *));

    kfree(progname_copy);

    c_args_count = 0;
    for (;c_args_count < args_count; c_args_count++) {
        kfree(args_copy[c_args_count]);
    }

    kfree(args_copy);
    kfree(arg_address);

    /* Warp to user mode. */
    enter_new_process(args_count /*argc*/, (userptr_t) stackptr /*userspace addr of argv*/,
                      (userptr_t) stackptr /*userspace addr of environment*/, stackptr, entrypoint);

    /* enter_new_process does not return. */
    panic("enter_new_process returned\n");

    *err = EINVAL;
    return -1;
}

/* Custom implementation of waitpid kernel system call */

pid_t
sys_waitpid(pid_t pid, int *status, int options, int *err) {

    if(status == (int*) 0x0) {
        return 0;
    }

    if(status == (int*) 0x40000000 || status == (int*) 0x80000000 || ((int)status & 3) != 0) {
        *err = EFAULT;
        return -1;
    }

    if(options != 0 && options != WNOHANG && options != WUNTRACED){
        *err = EINVAL;
        return -1;
    }

    if(pid < PID_MIN || pid > PID_MAX_256) {
        *err = ESRCH;
        return -1;
    }

    if(curproc->pid != proc_ids[pid]->ppid ){
        *err = ECHILD;
        return -1;
    }

    if(proc_ids[pid] == NULL){
        *err = ESRCH;
        return -1;
    }

    lock_acquire(proc_ids[pid]->exitlock);

    if (proc_ids[pid]->exit_flag == false) {

        if (options == WNOHANG) {
            lock_release(proc_ids[pid]->exitlock);
            return 0;
        }
        else {
            cv_wait(proc_ids[pid]->exitcv, proc_ids[pid]->exitlock);
        }
    }

    *status = proc_ids[pid]->exit_code;

    lock_release(proc_ids[pid]->exitlock);

    /* Clean Up */
    lock_destroy(proc_ids[pid]->exitlock);
    cv_destroy(proc_ids[pid]->exitcv);
    as_destroy(proc_ids[pid]->p_addrspace);
    proc_ids[pid]->p_addrspace = NULL;
    kfree(proc_ids[pid]->p_name);
    kfree(proc_ids[pid]);
    proc_ids[pid] = NULL;

    return pid;
}

/* Custom implementation of exit kernel system call */

void sys_exit(int exitcode, bool is_sig){

    lock_acquire(curproc->exitlock);

    for (int fd = 0; fd < OPEN_MAX; fd++) {
        int err;
        sys_close(fd, &err);
    }

    curproc->exit_flag = true;

    if (is_sig) {
        curproc->exit_code = _MKWAIT_SIG(exitcode);
    } else {
        curproc->exit_code = _MKWAIT_EXIT(exitcode);
    }

    if (proc_ids[curproc->ppid]->exit_flag == false) {
        cv_broadcast(curproc->exitcv, curproc->exitlock);
        lock_release(curproc->exitlock);
    } else {
        /* Clean Up */
        lock_release(curproc->exitlock);
        cv_destroy(curproc->exitcv);
        as_destroy(curproc->p_addrspace);
        kfree(proc_ids[curproc->pid]->p_name);
        curproc->p_addrspace = NULL;
        kfree(proc_ids[curproc->pid]);
        proc_ids[curproc->pid] = NULL;
        lock_destroy(curproc->exitlock);
    }

    thread_exit();
}

/* Custom implementation of sbrk kernel system call */

void *
sys_sbrk(intptr_t amount, int *err){

    vaddr_t retval = curproc->p_addrspace->heap_end;

    if (amount < 0 && amount <= -4096*1024*256) {
        *err = EINVAL;
        return (void *)-1;
    }

    if (curproc->p_addrspace->heap_end + amount < curproc->p_addrspace->heap_start)  {
        *err = EINVAL;
        return (void *)-1;
    }

    if (curproc->p_addrspace->heap_end + amount >= USERSTACK - 1024 * PAGE_SIZE)  {
        *err = ENOMEM;
        return (void *)-1;
    }

    /* Align in multiples of 4 */
    if (amount % 4 != 0) {
        *err = EINVAL;
        return (void *)-1;
    }

    int num_pages = (amount < 0) ? (amount * -1)/PAGE_SIZE : amount/PAGE_SIZE;

    if (amount % PAGE_SIZE != 0)
        num_pages++;

    struct page_table *proc_pg_table = curproc->p_addrspace->page_table_entry;
    struct page_table *prev_proc_pg_table;
    struct page_table *free_proc_pg_table;

    if(amount < 0) {
        for (int i = 1; i <= num_pages; i++) {

            // Page table removal :-  Loop through the page table and remove entries correspondingly

            proc_pg_table = curproc->p_addrspace->page_table_entry;
            prev_proc_pg_table = proc_pg_table;

            while(proc_pg_table != NULL) {
                if (proc_pg_table->vpn < USERSTACK - 1024 * PAGE_SIZE &&
                    proc_pg_table->vpn >= (curproc->p_addrspace->heap_end + amount)) {

                    prev_proc_pg_table->next = proc_pg_table->next;

                    free_proc_pg_table = proc_pg_table;
                    lock_acquire(page_lock);
                    if (free_proc_pg_table->state == PAGE_IN_DISK) {
                        swap_table_entry_delete(free_proc_pg_table);
                    } else {
                        kfree((void *) PADDR_TO_KVADDR(free_proc_pg_table->ppn));
                    }
                    lock_release(page_lock);
                    kfree(free_proc_pg_table);

                    break;
                }

                prev_proc_pg_table = proc_pg_table;
                proc_pg_table = proc_pg_table->next;
            }

        }

        // TLB cleanup code
        int spl;

        spl = splhigh();

        for (int i=0; i < NUM_TLB; i++) {
            tlb_write(TLBHI_INVALID(i), TLBLO_INVALID(), i);
        }

        splx(spl);
    }

    curproc->p_addrspace->heap_end += amount;

    if (amount < 0)
        as_activate();

    return (void *)retval;
}