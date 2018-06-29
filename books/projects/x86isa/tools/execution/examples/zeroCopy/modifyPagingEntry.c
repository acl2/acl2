// X86ISA Library
//
// Note: The license below is based on the template at:
// http://opensource.org/licenses/BSD-3-Clause
//
// Copyright (C) 2015, Regents of the University of Texas
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
// o Redistributions of source code must retain the above copyright
//   notice, this list of conditions and the following disclaimer.
//
// o Redistributions in binary form must reproduce the above copyright
//   notice, this list of conditions and the following disclaimer in the
//   documentation and/or other materials provided with the distribution.
//
// o Neither the name of the copyright holders nor the names of its
//   contributors may be used to endorse or promote products derived
//   from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//
// Original Author(s):
// Shilpi Goel         <shigoel@cs.utexas.edu>

// gcc -O3 modifyPagingEntry.c -o modifyPagingEntry.o


/*

Note that I use the words "physical address" when I really mean
"kernel virtual address". Since all the kernel virtual addresses are
directly mapped to the physical address space (physical address =
__pa(kernel virtual address)) in my set up of 1G pages, I feel
comfortable about blurring the distinction.

 */

// -------------------------------------------------------------------------------

#include <stdio.h>
#include <stdlib.h>

#define CR3_PDB_SHIFT 12

typedef unsigned long long u64;

#define _direct_map(x) (x);

u64 part_select (u64 x, u64 low, u64 high) {

  u64 width, val, mask;
  width = high - low + 1;
  mask = (1UL << width) - 1;
  val =  mask & (x >> low);
  return (val);

}

u64 part_install (u64 val, u64 x, u64 low, u64 high) {

  u64 width, mask, ret;
  width = high - low + 1;
  mask = (1UL << width) - 1;
  ret = (((~(mask << low)) & x) | (val << low));
  return (ret);

}

u64 pml4e_paddr (u64 cr3, u64 vaddr) {
  // Input: Contents of the CR3 register and the virtual address
  // Output: "Physical" address of the entry in PML4 table that corresponds to vaddr

  u64 pml4_table_base_paddr;
  u64 paddr;

  pml4_table_base_paddr = _direct_map((cr3 >> CR3_PDB_SHIFT) << CR3_PDB_SHIFT);

  // Address of PML4E:
  // Bits 51:12 are from CR3.
  // Bits 11:3 are bits 47:39 of vaddr.
  // Bits 2:0 are 0.
  paddr = part_install (part_select (vaddr, 39, 47),
                        pml4_table_base_paddr, 3, 11);
  return (paddr);

}

u64 pdpte_paddr (u64 pml4e_paddr, u64 vaddr) {
  // Input: "Physical" address of the PML4E and the virtual address
  // Output: "Physical" address of the entry in PDPT table that corresponds to vaddr

  u64 pdpt_table_base_addr, pml4e, paddr;

  // Read the PML4E entry from pml4e_paddr:
  pml4e = *((u64 *)pml4e_paddr);
  // Return error if the PML4E has the P bit cleared.
  if ((pml4e & 1) == 0) {
    return -1;
  }

  pdpt_table_base_addr = _direct_map(part_select(pml4e, 12, 51) << 12);

  // Address of PDPTE:
  // Bits 51:12 are from the PML4E.
  // Bits 11:3 are bits 38:30 of vaddr.
  // Bits 2:0 are 0.

  paddr = part_install (part_select (vaddr, 30, 38),
                        pdpt_table_base_addr, 3, 11);
  return (paddr);

}

u64 paddr (u64 pdpte_addr, u64 vaddr) {
  // Input: "Physical" address of the PDPTE and the virtual address
  // Output: "Physical" address corresponding to vaddr

  u64 page_base_paddr, pdpte, paddr;

  // Read the PDPTE from the pte_addr:
  pdpte = *((u64 *)pdpte_addr);
  // Return error if the PDPTE has the P or PS bit cleared.
  if (((pdpte & 1) == 0) || (part_select(pdpte, 7, 7) == 0)) {
    return -1;
  }

  page_base_paddr = _direct_map(part_select(pdpte, 30, 51) << 30);

  // "Physical" Address corresponding to vaddr:
  // Bits 51:30 are from the PDPTE.
  // Bits 29:0 are bits 29:0 of vaddr.

  paddr = part_install (part_select (vaddr, 0, 29),
                        page_base_paddr, 0, 29);

  return (paddr);

}

u64 copy_pdpte (u64 src_pdpte_paddr, u64 dst_pdpte_paddr) {
  // Input: "Physical" addresses of the PDPTE for the source and destination
  // Output: -1 if error, 0 otherwise

  u64 src_page_base_paddr_field, src_pdpte, dst_pdpte, modified_dst_pdpte;

  // Read the PDPTE from the src_pdpte_paddr:
  src_pdpte = *((u64 *)src_pdpte_paddr);
  // Return error if the PDPTE has the P or PS bit cleared.
  if (((src_pdpte & 1) == 0) || (part_select(src_pdpte, 7, 7) == 0)) {
    return -1;
  }

  src_page_base_paddr_field = part_select(src_pdpte, 30, 51);

  // Write src_page_base_paddr_field to the dst PDPTE.
  dst_pdpte = *((u64 *)dst_pdpte_paddr);
  modified_dst_pdpte = part_install(src_page_base_paddr_field, dst_pdpte, 30, 51);
  *((u64 *)dst_pdpte_paddr) = modified_dst_pdpte;

  return 0;
}

u64 rewire_dst_to_src (u64 src_la, u64 dst_la) {

  u64 cr3;
  u64 pml4e_src_pa, pdpte_src_pa, src_pa;
  u64 pml4e_dst_pa, pdpte_dst_pa, modified_dst_pa;
  u64 copy_pdpte_ret_stat;

  __asm__ __volatile__
    ( // Get cr3.
     "mov %%cr3, %%rax\n\t"
     "mov %%rax, %0\n\t"
     : "=m"(cr3)
     : // no input
     : "%rax"
      );

  /* Obtain PDPTE address for src_la. */
  pml4e_src_pa   = pml4e_paddr(cr3, src_la);
  pdpte_src_pa   = pdpte_paddr(pml4e_src_pa, src_la);
  if (pdpte_src_pa == -1) return -1;
  src_pa         = paddr(pdpte_src_pa, src_la);
  if (src_pa       == -1) return -1;

  /* Obtain PDPTE address for dst_la. */
  pml4e_dst_pa   = pml4e_paddr(cr3, dst_la);
  pdpte_dst_pa   = pdpte_paddr(pml4e_dst_pa, dst_la);
  if (pdpte_dst_pa == -1) return -1;

  /* Map dst_la to src_pa. */
  copy_pdpte_ret_stat = copy_pdpte(pdpte_src_pa, pdpte_dst_pa);

  /* Get physical address corresponding to dst_la. */
  modified_dst_pa = paddr(pdpte_dst_pa, dst_la);
  if (modified_dst_pa       == -1) return -1;

  if (modified_dst_pa == src_pa)
    return 1; // Success
  return 0; // Failure

}

int main() {

  // rewire_dst_to_src can be made into a syscall --- pre-condition:
  // both the inputs have to be 1G-aligned, or instead, I can check
  // that inside this function, and return an error if they aren't.

  u64 src_la = 0x8C0000000; // 1G aligned
  u64 dst_la = 0x900000000; // 1G aligned
  return (rewire_dst_to_src (src_la, dst_la));
}
