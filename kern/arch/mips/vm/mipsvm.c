/*
 * Copyright (c) 2000, 2001, 2002, 2003, 2004, 2005, 2008, 2009
 *	The President and Fellows of Harvard College.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
*    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE UNIVERSITY AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE UNIVERSITY OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include <types.h>
#include <kern/errno.h>
#include <lib.h>
#include <spl.h>
#include <cpu.h>
#include <spinlock.h>
#include <proc.h>
#include <current.h>
#include <mips/tlb.h>
#include <vm.h>
#include <addrspace.h>
#include <synch.h>
#include <kern/file_syscalls.h>
#include <kern/fcntl.h>
#include <kern/seek.h>
#include <vfs.h>
#include <uio.h>
#include <kern/iovec.h>
#include <copyinout.h>
#include <vnode.h>
#include <kern/seek.h>
#include <kern/stat.h>

/*
 * Custom implementation of VM to handle coremap, user pages and swapping.
 */

struct spinlock mem_lock = SPINLOCK_INITIALIZER;
struct vnode *swap_vnode;
off_t swap_offset = 0;
bool booted = false;

static void
as_zero_region(paddr_t paddr, unsigned npages)
{
	bzero((void *)PADDR_TO_KVADDR(paddr), npages * PAGE_SIZE);
}

void
vm_bootstrap(void)
{
	int i;

	/*if (booted == true) {
		return;
	}*/

	char disk_name[] = "lhd0raw:";

	int result = 0;
	result = vfs_open(disk_name, O_RDWR, 0664, &swap_vnode);

	if (result)
		disk_enabled = FALSE;
	else
		disk_enabled = TRUE;

	page_lock = lock_create("page_lock");
	swap_table = NULL;
	swap_table_free = NULL;

	if (disk_enabled) {
		swap_table_free = (swap_table_entry_t *) kmalloc((sizeof(swap_table_entry_t) * (MAX_SWAP_ENTRY)));

		for (i = 0; i < MAX_SWAP_ENTRY - 1; i++) {
			swap_table_free[i].next = &swap_table_free[i+1];
			swap_table_free[i].offset = i * PAGE_SIZE;
		}

		swap_table_free[i].next = NULL;
		swap_table_free[i].offset = i * PAGE_SIZE;
	}

	last_swapped_out_page_index = coremap_addr/PAGE_SIZE;
	booted = true;
}

/*
 * Check if we're in a context that can sleep. While most of the
 * operations in dumbvm don't in fact sleep, in a real VM system many
 * of them would. In those, assert that sleeping is ok. This helps
 * avoid the situation where syscall-layer code that works ok with
 * dumbvm starts blowing up during the VM assignment.
static
void
dumbvm_can_sleep(void)
{

}
*/

/* Method to read from disk */

static void
swap_read(off_t offset, void *buf) {
	int response = 0;
	struct uio read_uio;
	struct iovec read_iovec;

	/* data and length */
	read_iovec.iov_kbase = buf;
	read_iovec.iov_len = PAGE_SIZE;

	/* flags and references */
	read_uio.uio_iovcnt = 1;
	read_uio.uio_iov = &read_iovec;
	read_uio.uio_segflg = UIO_SYSSPACE;
	read_uio.uio_rw = UIO_READ;
	read_uio.uio_space = NULL;
	read_uio.uio_resid = PAGE_SIZE;
	read_uio.uio_offset = offset;
	response = VOP_READ(swap_vnode, &read_uio);
	KASSERT(!response);
	KASSERT(offset + PAGE_SIZE == read_uio.uio_offset);
	return;
}

/* Method to write to disk */

static void
swap_write(swap_table_entry_t *ste, void *buf) {
	struct uio write_uio;
	struct iovec write_iovec;

	/* data and length */
	write_iovec.iov_kbase = buf;
	write_iovec.iov_len = PAGE_SIZE;

	/* flags and references */
	write_uio.uio_iovcnt = 1;
	write_uio.uio_iov = &write_iovec;
	write_uio.uio_segflg = UIO_SYSSPACE;
	write_uio.uio_rw = UIO_WRITE;
	write_uio.uio_space = NULL;
	write_uio.uio_resid = PAGE_SIZE;
	write_uio.uio_offset = ste->offset;
	VOP_WRITE(swap_vnode, &write_uio);
}

/* Method to get physical pages */

static
paddr_t
getppages(unsigned long npages)
{
	unsigned long count = 0, page_counter = ram_getsize() / PAGE_SIZE, i;

	if (booted) {
		spinlock_acquire(&mem_lock);
	}

	for(i = coremap_addr/PAGE_SIZE; i < page_counter && count != npages; i++) {
		if(coremap[i].state == FREE) {
			count++;
		} else {
			count = 0;
		}
	}

	if (count < npages) {

		if (booted) {
			spinlock_release(&mem_lock);
		}

		return 0;
	} else {
		i--;
	}

	while(count > 0) {
		coremap[i].state = FIXED;
		coremap[i].pte = NULL;
		coremap[i].is_user = FALSE;
		if (count == 1) {
			coremap[i].chunk_size = npages;
			break;
		}
		i--;
		count--;
	}

	if (booted) {
		spinlock_release(&mem_lock);
	}

	return i * PAGE_SIZE;
}

/* Method to retrieve user pages */

static paddr_t
get_user_pages(unsigned npages)
{
	unsigned long count = 0, tmp_page_cnt, page_counter = ram_getsize() / PAGE_SIZE, i;
	unsigned int last_swapped = last_swapped_out_page_index;
	tmp_page_cnt = page_counter;

	spinlock_acquire(&mem_lock);

	if (last_swapped_out_page_index + 1 == page_counter) {
		last_swapped = coremap_addr / PAGE_SIZE;
		tmp_page_cnt = 0;
	}

	for(i = last_swapped + 1; i < page_counter; i++) {
		if (coremap[i].state == FIXED && coremap[i].is_user == TRUE) {
			KASSERT(coremap[i].pte);
			count++;

			if (count == npages) {
				i++;
				break;
			}

		} else {
			count = 0;
		}

		if ((i == page_counter - 1) && (tmp_page_cnt == page_counter)) {
			page_counter = last_swapped + 1;
			i = coremap_addr/PAGE_SIZE - 1;
			count = 0;
		}
	}

	if (count < npages) {
		spinlock_release(&mem_lock);
		return 0;
	}

	last_swapped_out_page_index = i - 1;

	for (; count > 0; count--) {
		i--;
		coremap[i].is_user = FALSE;
	}
	coremap[i].chunk_size = npages;
	spinlock_release(&mem_lock);

	return i * PAGE_SIZE;
}

/* Lookup swap table data structure for entry */

static swap_table_entry_t *
swap_table_lookup(struct page_table *pte)
{
	swap_table_entry_t *temp = swap_table;

	while(temp) {
		if (temp->as == pte->as && temp->vpn == pte->vpn) {
			return temp;
		}
		temp = temp->next;
	}
	return NULL;
}

/* Insert into swap table */

static void
swap_table_add(swap_table_entry_t *ste, struct page_table *pte)
{
	ste->as = pte->as;
	ste->vpn = pte->vpn;
	pte->state = PAGE_IN_DISK;
	if (swap_table == NULL) {
		swap_table = ste;
		ste->next = NULL;
	} else {
		ste->next = swap_table;
		swap_table = ste;
	}
}

/* Remove from swap_table using the below methods - swap_table_remove() and swap_table_entry_delete */

static swap_table_entry_t *
swap_table_remove(struct page_table *pte)
{
	swap_table_entry_t *prev = NULL, *temp = swap_table;

	while(temp) {
		if (temp->as == pte->as && temp->vpn == pte->vpn) {
			if (prev == NULL) {
				swap_table = swap_table->next;
			} else {
				prev->next = temp->next;
			}
			return temp;
		}
		prev = temp;
		temp = temp->next;
	}
	return NULL;
}



void
swap_table_entry_delete(struct page_table *pte) {
	swap_table_entry_t *ste = swap_table_remove(pte);
	ste->next = swap_table_free;
	swap_table_free = ste;
}

/* Method to swap out pages to disk */

static paddr_t
swap_out_pages(int npages)
{
	paddr_t ppn, tmp;
	swap_table_entry_t *ste;
	int i, size, spl;

	/* Disable interrupts on this CPU while frobbing the TLB. */
	spl = splhigh();

	ppn = get_user_pages(npages);
	if (ppn == 0) {
		splx(spl);
		return 0;
	}

	tmp = ppn;
	for(i = 1; i <= npages; i++) {
		ste = swap_table_free;
		swap_table_free = swap_table_free->next;

		KASSERT(ste);

		swap_write(ste, (void *)PADDR_TO_KVADDR(tmp));

		swap_table_add(ste, coremap[tmp/PAGE_SIZE].pte);
		coremap[tmp/PAGE_SIZE].pte = NULL;

		if (size) {

		}
		tmp += PAGE_SIZE;
	}

	for (i=0; i<NUM_TLB; i++) {
		tlb_write(TLBHI_INVALID(i), TLBLO_INVALID(), i);
	}

	ipi_broadcast(IPI_TLBSHOOTDOWN);

	splx(spl);

	return ppn;
}

/* Method to swap in pages from disk. */

static int
swap_in_page(struct page_table *pte)
{
	paddr_t ppn;

	KASSERT(pte);
	ppn = getppages(1);

	if (ppn == 0) {
		ppn = swap_out_pages(1);
		KASSERT(ppn);
		if (ppn == 0) {
			return 0;
		}
	}

	coremap[ppn/PAGE_SIZE].is_user = TRUE;
	coremap[ppn/PAGE_SIZE].pte = pte;

	swap_table_entry_t *ste = swap_table_remove(pte);
	KASSERT(ste != NULL);

	swap_read(ste->offset, (void *)PADDR_TO_KVADDR(ppn));

	ste->next = swap_table_free;
	swap_table_free = ste;

	pte->ppn = ppn;
	pte->state = PAGE_IN_RAM;

	return 1;
}

/* Copy swap pages */

static void
swap_copy(struct page_table *newp, struct page_table *oldp)
{
	swap_table_entry_t *ste, *ste_old;
	char* buf = (char*) kmalloc(PAGE_SIZE);

	ste = swap_table_free;
	swap_table_free = swap_table_free->next;

	KASSERT(ste);

	ste_old = swap_table_lookup(oldp);
	KASSERT(ste_old);
	swap_read(ste_old->offset, (void *)buf);

	swap_write(ste, (void *)buf);
	swap_table_add(ste, newp);

	kfree(buf);
	return;
}

/* Allocate/free some kernel-space virtual pages */

vaddr_t
alloc_kpages(unsigned npages)
{
	(void) npages;
	paddr_t pa;
	pa = getppages(npages);
	if (pa==0) {
		if (booted && disk_enabled) {
			lock_acquire(page_lock);
			pa = swap_out_pages(npages);
			if (pa == 0) {
				lock_release(page_lock);
				return 0;
			}
			lock_release(page_lock);
			return PADDR_TO_KVADDR(pa);
		}
		return 0;
	}
	return PADDR_TO_KVADDR(pa);
}

/* Custom implementation to free pages */

void
free_kpages(vaddr_t addr)
{
	int index = (addr - MIPS_KSEG0) / PAGE_SIZE;

	if (booted) {
		spinlock_acquire(&mem_lock);
	}

	int pages = coremap[index].chunk_size;

	coremap[index].chunk_size = 0;

	for (int i = 0; i < pages; i++) {
		coremap[index+i].is_user = FALSE;
		coremap[index+i].state = FREE;
		coremap[index+i].pte = NULL;
	}

	if (booted) {
		spinlock_release(&mem_lock);
	}
}

/* Calculate bytes used by the allocated pages of the CoreMap */

unsigned
int
coremap_used_bytes() {

	int count = 0;

	if (booted) {
		spinlock_acquire(&mem_lock);
	}

	for (unsigned int i = 0 ; i < ram_getsize() / PAGE_SIZE; i++) {
		if (coremap[i].state == FIXED) {
			count++;
		}
	}

	if (booted) {
		spinlock_release(&mem_lock);
	}

	return count * PAGE_SIZE;
}

void
vm_tlbshootdown_all(void)
{
	panic("dumbvm tried to do tlb shootdown?!\n");
}

void
vm_tlbshootdown(const struct tlbshootdown *ts)
{
	(void)ts;
	panic("dumbvm tried to do tlb shootdown?!\n");
}

/* Custom implementation of vm_fault */

int
vm_fault(int faulttype, vaddr_t faultaddress)
{
	paddr_t paddr;
	uint32_t ehi, elo;
	struct addrspace *as;
	int spl;

	faultaddress &= PAGE_FRAME;

	DEBUG(DB_VM, "mipsvm: fault: 0x%x\n", faultaddress);

	if (curproc == NULL) {
		/*
		 * No process. This is probably a kernel fault early
		 * in boot. Return EFAULT so as to panic instead of
		 * getting into an infinite faulting loop.
		 */
		return EFAULT;
	}

	as = proc_getas();
	if (as == NULL) {
		/*
		 * No address space set up. This is probably also a
		 * kernel fault early in boot.
		 */
		return EFAULT;
	}

	bool found = false;


	/* Disable interrupts on this CPU while frobbing the TLB. */
	spl = splhigh();

	struct page_table *temp = as->page_table_entry;
	struct page_table *last_page = as->page_table_entry;

	switch (faulttype) {
		case VM_FAULT_READONLY:
			/* We always create pages read-write, so we can't get this */
			panic("mipsvm: got VM_FAULT_READONLY\n");
		case VM_FAULT_READ:
		case VM_FAULT_WRITE: {

			/* Bad Call Checks */
			if (faultaddress >= as->heap_end && faultaddress < USERSTACK - 1024 * PAGE_SIZE) {
				return EFAULT;
			}

			if (faultaddress >= USERSTACK) {
				KASSERT(0);
				return EFAULT;
			}

			if (faultaddress < as->heap_start) {
				struct region *temp_region = as->addr_regions;

				while (temp_region != NULL) {
					if (faultaddress >= temp_region->region_start &&
						faultaddress < temp_region->region_start + temp_region->region_size) {
						break;
					} else {
						temp_region = temp_region->next;
						if (temp_region == NULL) {
							return EFAULT;
						}
					}
				}
			}

			while (temp != NULL) {
				if (faultaddress >= temp->vpn && faultaddress < temp->vpn + PAGE_SIZE) {
					found = true;
					break;
				}

				last_page = temp;
				temp = temp->next;
			}

			if (found) {
				lock_acquire(page_lock);
				/* Handle if memory is in ram or disk */
				if (temp->state != PAGE_IN_RAM) {
					/* bring it to the RAM */
					swap_in_page(temp);
				}
				lock_release(page_lock);
			} else {
				temp = (struct page_table *) kmalloc(sizeof(struct page_table));
				if (temp == NULL) {
					KASSERT(0);
					return ENOMEM;
				}

				temp->vpn = faultaddress;
				temp->ppn = getppages(1);

				if (temp->ppn == 0) {
					if (disk_enabled) {
						lock_acquire(page_lock);
						temp->ppn = swap_out_pages(1);
						if (temp->ppn == 0) {
							KASSERT(0);
							lock_release(page_lock);
							return ENOMEM;
						}
						lock_release(page_lock);
					} else {
						KASSERT(0);
						return ENOMEM;
					}
				}

				temp->state = PAGE_IN_RAM;

				spinlock_acquire(&mem_lock);

				coremap[temp->ppn/PAGE_SIZE].is_user = TRUE;
				coremap[temp->ppn/PAGE_SIZE].pte = temp;
				temp->as = as;

				spinlock_release(&mem_lock);

				as_zero_region(temp->ppn, 1);
				temp->next = NULL;
				found = true;

				if (as->page_table_entry == NULL) {
					as->page_table_entry = temp;
				} else {
					temp->next = last_page->next;
					last_page->next = temp;
				}
			}
			break;
		}
		default:
			KASSERT(0);
			return EINVAL;
	}

	paddr = temp->ppn;
	/* make sure it's page-aligned */
	KASSERT((paddr & PAGE_FRAME) == paddr);

	ehi = faultaddress;
	elo = paddr | TLBLO_DIRTY | TLBLO_VALID;
	tlb_random(ehi, elo);
	splx(spl);
	return 0;

}

/* Address space methods */

struct addrspace *
as_create(void)
{
	struct addrspace *as = NULL;
	as = kmalloc(sizeof(struct addrspace));

	if (as==NULL) {
		return NULL;
	}

	as->addr_regions = NULL;
	as->heap_start = 0;
	as->heap_end = 0;
	as->page_table_entry = NULL;

	return as;
}

void
as_destroy(struct addrspace *as) {

	struct region *address_temp = as->addr_regions;
	struct region *addr_temp;

	while (address_temp != NULL) {
		addr_temp = address_temp->next;
		kfree(address_temp);
		address_temp = addr_temp;
	}

	struct page_table *temp = as->page_table_entry;
	struct page_table *page_temp;
	while (temp != NULL) {
		page_temp = temp->next;

		lock_acquire(page_lock);
		if (temp->state == PAGE_IN_DISK) {
			swap_table_entry_delete(temp);
		} else {
			kfree((void *)PADDR_TO_KVADDR(temp->ppn));
		}
		lock_release(page_lock);

		kfree(temp);
		temp = page_temp;
	}

	kfree(as);
}

void
as_activate(void)
{
	int i, spl;
	struct addrspace *as;

	as = proc_getas();
	if (as == NULL) {
		return;
	}

	as->parent_as = NULL;
	/* Disable interrupts on this CPU while frobbing the TLB. */
	spl = splhigh();

	for (i=0; i<NUM_TLB; i++) {
		tlb_write(TLBHI_INVALID(i), TLBLO_INVALID(), i);
	}

	splx(spl);
}

void
as_deactivate(void)
{

}

int
as_define_region(struct addrspace *as, vaddr_t vaddr, size_t sz,
				 int readable, int writeable, int executable)
{
	size_t npages;

	(void)readable;
	(void)writeable;
	(void)executable;

	/* Align the region. First, the base... */
	sz += vaddr & ~(vaddr_t)PAGE_FRAME;
	vaddr &= PAGE_FRAME;

	/* ...and now the length. */
	sz = (sz + PAGE_SIZE - 1) & PAGE_FRAME;

	npages = sz / PAGE_SIZE;

	struct region *address_temp = as->addr_regions;
	struct region *address_last = NULL;

	while (address_temp != NULL) {
		address_last = address_temp;
		address_temp = address_temp->next;
	}

	address_temp = (struct region *) kmalloc(sizeof(struct region));

	if (address_temp == NULL)
		return ENOMEM;

	address_temp->region_start = vaddr;
	address_temp->region_size = npages * PAGE_SIZE;
	address_temp->next = NULL;
	//address_temp->permission = (readable + writeable + executable);

	if (address_last == NULL) {
		as->addr_regions = address_temp;
	} else {
		address_last->next = address_temp;
	}

	as->heap_start = address_temp->region_start + address_temp->region_size;
	as->heap_end = as->heap_start;

	return 0;
}

int
as_prepare_load(struct addrspace *as)
{
	(void) as;
	//panic("as_prepare_load");
	return 0;
}

int
as_complete_load(struct addrspace *as)
{
	(void) as;
	return 0;
}

int
as_define_stack(struct addrspace *as, vaddr_t *stackptr)
{
	(void) as;
	*stackptr = USERSTACK;
	return 0;
}

int
as_copy(struct addrspace *old, struct addrspace **ret)
{
	struct addrspace *target;

	target = as_create();
	if(target == NULL){
		return ENOMEM;
	}

	target->page_table_entry = NULL;
	target->parent_as = old;

	struct page_table *new_pg_table;
	struct page_table *old_pg_table = old->page_table_entry;
	struct page_table *page_table_last = NULL;

	paddr_t address;

	while (old_pg_table != NULL) {
		new_pg_table = kmalloc(sizeof(struct page_table));

		if (new_pg_table == NULL) {
			return ENOMEM;
		}
		new_pg_table->vpn = old_pg_table->vpn;
		new_pg_table->as = target;

		lock_acquire(page_lock);
		if (old_pg_table->state == PAGE_IN_RAM) {
			address = getppages(1);
			if (address == 0) {
				if (disk_enabled) {
					address = swap_out_pages(1);
					if (address == 0) {
						lock_release(page_lock);
						/* TODO: free all new page table entries created so far */
						kfree(new_pg_table);
						return ENOMEM;
					}
				} else {
					lock_release(page_lock);
					/* TODO: free all new page table entries created so far */
					kfree(new_pg_table);
					return ENOMEM;
				}
			}

			new_pg_table->ppn = address;
			new_pg_table->state = PAGE_IN_RAM;
			coremap[address/PAGE_SIZE].is_user = TRUE;
			coremap[address/PAGE_SIZE].pte = new_pg_table;

			as_zero_region(address, 1);

			memmove((void *) PADDR_TO_KVADDR(new_pg_table->ppn),
					(const void *) PADDR_TO_KVADDR(old_pg_table->ppn), PAGE_SIZE);
			lock_release(page_lock);
		} else {
			new_pg_table->state = PAGE_IN_DISK;
			lock_release(page_lock);
			swap_copy(new_pg_table, old_pg_table);
		}
		new_pg_table->next = NULL;

		old_pg_table = old_pg_table->next;

		if (page_table_last == NULL) {
			page_table_last = new_pg_table;
		} else {
			page_table_last->next = new_pg_table;
			page_table_last = page_table_last->next;
		}

		if (target->page_table_entry == NULL) {
			target->page_table_entry = new_pg_table;
		}
	}

	target->addr_regions = NULL;

	struct region *new_region;
	struct region *old_region = old->addr_regions;
	struct region *region_last = NULL;

	while(old_region != NULL) {
		new_region = kmalloc(sizeof(struct region));

		if(new_region == NULL) {
			/* TODO: free all new page table entries created so far */
			return ENOMEM;
		}

		new_region->region_start = old_region->region_start;
		new_region->region_size = old_region->region_size;

		new_region->next = NULL;
		old_region = old_region->next;

		if (region_last == NULL) {
			region_last = new_region;
		} else {
			region_last->next = new_region;
			region_last = region_last->next;
		}

		if (target->addr_regions == NULL) {
			target->addr_regions = new_region;
		}
	}

	target->heap_start = old->heap_start;
	target->heap_end = old->heap_end;

	*ret = target;

	return 0;
}

