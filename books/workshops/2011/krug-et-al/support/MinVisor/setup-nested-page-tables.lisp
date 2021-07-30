
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; setup-nested-page-tables.lisp
;;;
;;; setup-nested-page-tables really does setup page tables correctly.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Here is the C code corresponding to the assembly, given below, we
;;; analyze in this file.

#|

/*
 * Setting up page tables for PAE paging with 2MB pages.
 * The page tables will translate to the identity map upon
 * initialization, but will then be modified by setting all entries
 * pointing to the hypervisors code to 0.
 *
 * When used as nested page tables for the guest, this will cause a
 * page-not-present interupt to be caught by the hypervisor, which
 * can then take appropriate action.
 */


/* Copied from the AMD Doc's (P. 121, 127-128 AMD64 ArchProgManV2 Sys Programming):
 *
 * 2-Mbyte page translation is performed by dividing the 32-bit virtual
 * address into three fields. Each field is used as an index into a
 * 2-level page-translation hierarchy.
 *
 * Bits 31-30 index into the 4-entry page-directory-pointer table
 * Bits 29-21 index into the 512-entry page-directory table
 * Bits 20-0 provide the byte offset into the physical page
 *
 * [P. 136] Page data- structure tables are always aligned on 4-Kbyte
 * boundaries, so only the address bits above bit 11 are stored in the
 * translation-table base-address field. Bits 11?0 are assumed to be
 * 0.
 *
 * [RBK] I assume that the above means bits 5-11 in the CR3 should be
 * 0.
 *
 * Format of the CR3 register:
 * Bits 31-5: Page-Directory-Pointer Base Address
 * Bit 4: PCD --- page-level cache disable
 * Bit 3: PWT --- page-level write through
 * Bits 2-0: Reserved, MBZ
 *
 * Format of the page-directory-pointer entry:
 * Bits 63-52: Reserved, MBZ
 * Bits 51-12: Page-Directory Base Address
 * Bits 11-9: AVL --- available to software
 * Bits 8-5: Reserved, MBZ
 * Bit 4: PCD --- page-level cache disable
 * Bit 3: PWT --- page-level write through
 * Bits 2-1: MBZ
 * Bit 0: P --- present
 *
 * Format of the page-directory entry:
 * Bit 63: NX --- no execute
 * Bits 62-52: Reserved, MBZ
 * Bits 51-21: Physical-page Base Address
 * Bits 20-13: Reserved, MBZ
 * Bit 12: PAT
 * Bits 11-9: AVL --- available to software
 * Bit 8: G
 * Bit 7: PS --- page size (1 for 2-MB physical pages, as used here.)
 * Bit 6: D --- dirty
 * Bit 5: A --- accessed
 * Bit 4: PCD --- page-level cache disable
 * Bit 3: PWT --- page-level write through
 * Bit 2: U/S --- user/supervisor, set indicates user may access
 * Bit 1: R/W --- read/write
 * Bit 0: P --- present
 *
 * Note: When the P bit is 0, indicating a not-present page, all
 * remaining bits in the page data-structure entry are available to
 * software.
*/


typedef unsigned int u32;
typedef unsigned long long u64;

typedef u64 *pdpt_t;   // pointer to the page-directory-pointer table
typedef u64 *pdt_t;    // pointer to a page-directory table


void sec_not_present(pdpt_t pdptp, u32 *visor_start, u32 visor_size)
{
  u64 pdpt_entry;
  u64 tmp;
  u32 tmp32;
  pdt_t pdt;
  u32 start, end;
  u32 i, j;
  u64 mask;

  mask = ~((1 << 12) - 1);

  // The top two bits are the index into the 4 entry
  // page-directory-pointer table
  j = (u32)visor_start >> 30;
  pdpt_entry = pdptp[j];

  // mask will mask off the lower 12 bits of pdpt_entry.  By
  // construction, this is sufficient to (after type coercion) get us
  // the pointer to the pdt holding secvisors physical memory.
  tmp = pdpt_entry & mask;
  tmp32 = (u32)tmp;
  pdt = (pdt_t)tmp32;

  // Bits 29-21 form the index into the 512 entry page-directory
  // table.  We grab those bits for the start and end of the
  // hypervisor's memory image.
  start = ((u32)visor_start & 0x3fe00000) >> 21;
  end = (((u32)visor_start + visor_size) & 0x3fe00000) >> 21;

  // mark not present from start to end
  for(i = start; i < end; i ++){
    pdt[i] = 0;
  }
}


void init_pdts(pdt_t pdt_array[4])
{
  u64 addr;
  pdt_t pdt;
  u32 i, j;
  u64 flags;
  u64 page_size_2m;

  // present, rw, user, accessed, dirty, pse --- 2MB page
  flags = 1 | 2 | 4 | 32 | 64 | 128;
  page_size_2m = 1 << 21;
  addr = 0;
  // 4 tables
  for(i = 0; i < 4; i ++){
    pdt = pdt_array[i];
    // 512 entries per table
    for(j = 0; j < 512; j ++)
    {
      // Make a page directory entry for a 2MB page.
      // Given that we initialized addr to 0, then incremented by
      // page_size_2m, everything fits very nicely.
      pdt[j] = addr | flags;
      addr += page_size_2m;
    }
  }
}


void init_pdpt(pdpt_t pdptp, pdt_t pdt_array[4])
{
  u32 i;
  u64 page_present;

  page_present = 1;

  for(i = 0; i < 4; i++){
    // Since each element of pdt_array is a 32 bit pointer, we don't
    // have to worry about clearing bits 63-52.  Similarly, since
    // the lower 12 bits are already 0, the pointer will fit right
    // into place in the page-directory-pointer entry.  So, all we do
    // is set the page-present bit.
    pdptp[i] = (u64)((u32)pdt_array[i] | page_present);
  }
}


pdpt_t create_nested_pt(pdpt_t pdptp, pdt_t pdt_array[4], u32 *visor_start, u32 visor_size)

/* precondition
 * pdptp is a 32-bit pointer to a 4k page, aligned on a 4k boundary.
 * So lower 12 bits are 0.  The page has been initialized to 0.
 * Similarly for each of the four entries in pdt_array.
 * visor_start points to the start of the hypervisor's memory image,
 * which we wish to protect.
 * visor_size is the size of the hypervisor's image.
 * Also, visor_start and visor_size are such that the addresses of the
 * hypervisor will be covered by one page directory.  Note that each
 * directory covers one 1 GB, and is GB aligned.
 */

{
  /* Initialize the pdpt. */
  init_pdpt(pdptp, pdt_array);

  /* Initialize the 4 pdts. */
  init_pdts(pdt_array);

  /* Mark secvisor not present. */
  sec_not_present(pdptp, visor_start, visor_size);

  return pdptp;
}

int main()
{
  return 42;
}
||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Tips for next time:
;;; use trick for information-flow for effect functions
;;; include Y86-p preservation in invariant
;;; include frame condition and other desired read/access properties
;;; in invariant.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; Added by Matt K.: We now set waterfall-parallelism on by default for ACL2(p).
; I'm preserving the multiline comment that was here previously, just below.
(set-waterfall-parallelism t)

#||
 /projects/acl2/releases/v4-3-64/ccl-saved_acl2p
or
/projects/hvg/parallel/acl2p/ccl-saved_acl2p

(set-waterfall-parallelism :resource-based)
or
(set-waterfall-parallelism :full)

(set-waterfall-printing :limited)

(time$ (ld ;; Newline to fool dependency scanner
   "setup-nested-page-tables.lisp"))

||#

(include-book "../Y86/y86")
(include-book "../Y86/asm")

(include-book "../Symbolic/defsimulate+")

;;;(set-gag-mode :goals)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Some stuff which should be moved to the appropriate books

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (local
  (defun ind-fn (x y n)
    (if (zp n)
        (list x y n)
      (ind-fn (floor x 2) (floor y 2) (+ -1 n)))))

 (local
  (defthm crock-1
    (implies (and (integerp x)
                  (<= 0 x)
                  (< x (expt 2 n))
                  (integerp y)
                  (<= 0 y)
                  (< y (expt 2 n)))
             (< (logior x y) (expt 2 n)))
    :hints (("Goal" :induct (ind-fn x y n)
             :in-theory (disable |(floor x 2)|)))))

 (defthm |(n32p (logior x y))|
   (implies (and (n32p x)
                 (n32p y))
            (n32p (logior x y)))
   :hints (("Goal" :use ((:instance crock-1
                                    (n 32))))))

 ;;; but make bind-free to choode n1 n2
 (defthm logand-mask-shifted-2
   (implies (and (integerp x)
                 (integerp n1)
                 (integerp n2)
                 (<= 0 n1)
                 (<= 0 n2)
                 (equal c (* (expt 2 n1)
                             (+ -1 (expt 2 n2)))))
            (equal (logand c
                           x)
                   (* (expt 2 n1)
                      (mod (floor x (expt 2 n1))
                           (expt 2 n2)))))
   :hints (("Goal" :use ((:instance logand-mask-shifted
                                    ))))
   :rule-classes nil)
 )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Original c file is in
;;;    ~/School/Secvisor/Fragments/setup-nested-page-tables-fragment.c
;;; Original assembly is in
;;;    ~/School/Secvisor/Fragments/setup-nested-page-tables-fragment.s
;;; assembly obtained via
;;;    gcc -S setup-nested-page-tables-fragment.c
;;; Handy listing file
;;;    ~/School/Secvisor/Fragments/setup-nested-page-tables-fragment.listing

(defconst *snpt-code*
  '(
;;;         .file   "setup-nested-page-tables-fragment.c"
;;;         .text
;;; .globl sec_not_present
;;;         .type   sec_not_present, @function

;;; sec_not_present:
    :sec_not_present

;;; pushl   %ebp
    (pushl :ebp)

;;; movl    %esp, %ebp
    (rrmovl :esp :ebp)

;;; subl    $48, %esp
    (irmovl 48 :imme1)
    (subl :imme1 :esp)

;;; movl    $-4096, -8(%ebp)
    (irmovl -4096 :imme1)
    (rmmovl :imme1 -8 (:ebp))

;;; movl    $-1, -4(%ebp)
    (irmovl -1 :imme1)
    (rmmovl :imme1 -4 (:ebp))

;;; movl    12(%ebp), %eax
    (mrmovl 12 (:ebp) :eax)

;;; shrl    $30, %eax
    (irmovl 30 :imme1)
    (shrl :imme1 :eax)

;;; movl    %eax, -12(%ebp)
    (rmmovl :eax -12 (:ebp))

;;; movl    -12(%ebp), %eax
    (mrmovl -12 (:ebp) :eax)

;;; sall    $3, %eax
    (irmovl 3 :imme1)
    (sall :imme1 :eax)

;;; addl    8(%ebp), %eax
    (mrmovl 8 (:ebp) :valu1)
    (addl :valu1 :eax)

;;; movl    4(%eax), %edx
    (mrmovl 4 (:eax) :edx)

;;; movl    (%eax), %eax
    (mrmovl 0 (:eax) :eax)

;;; movl    %eax, -48(%ebp)
    (rmmovl :eax -48 (:ebp))

;;; movl    %edx, -44(%ebp)
    (rmmovl :edx -44 (:ebp))

;;; movl    -8(%ebp), %eax
    (mrmovl -8 (:ebp) :eax)

;;; andl    -48(%ebp), %eax
    (mrmovl -48 (:ebp) :valu1)
    (andl :valu1 :eax)

;;; movl    %eax, -40(%ebp)
    (rmmovl :eax -40 (:ebp))

;;; movl    -4(%ebp), %eax
    (mrmovl -4 (:ebp) :eax)

;;; andl    -44(%ebp), %eax
    (mrmovl -44 (:ebp) :valu1)
    (andl :valu1 :eax)

;;; movl    %eax, -36(%ebp)
    (rmmovl :eax -36 (:ebp))

;;; movl    -40(%ebp), %eax
    (mrmovl -40 (:ebp) :eax)

;;; movl    %eax, -32(%ebp)
    (rmmovl :eax -32 (:ebp))

;;; movl    -32(%ebp), %eax
    (mrmovl -32 (:ebp) :eax)

;;; movl    %eax, -28(%ebp)
    (rmmovl :eax -28 (:ebp))

;;; movl    12(%ebp), %eax
    (mrmovl 12 (:ebp) :eax)

;;; andl    $1071644672, %eax
    (irmovl 1071644672 :imme1)
    (andl :imme1 :eax)

;;; shrl    $21, %eax
    (irmovl 21 :imme1)
    (shrl :imme1 :eax)

;;; movl    %eax, -24(%ebp)
    (rmmovl :eax -24 (:ebp))

;;; movl    12(%ebp), %eax
    (mrmovl 12 (:ebp) :eax)

;;; addl    16(%ebp), %eax
    (mrmovl 16 (:ebp) :valu1)
    (addl :valu1 :eax)

;;; andl    $1071644672, %eax
    (irmovl 1071644672 :imme1)
    (andl :imme1 :eax)

;;; shrl    $21, %eax
    (irmovl 21 :imme1)
    (shrl :imme1 :eax)

;;; movl    %eax, -20(%ebp)
    (rmmovl :eax -20 (:ebp))

;;; movl    -24(%ebp), %eax
    (mrmovl -24 (:ebp) :eax)

;;; movl    %eax, -16(%ebp)
    (rmmovl :eax -16 (:ebp))

;;; jmp     .L2
    (jmp :L2)

;;; .L3:
    :L3

;;; movl    -16(%ebp), %eax
    (mrmovl -16 (:ebp) :eax)

;;; sall    $3, %eax
    (irmovl 3 :valu1)
    (sall :valu1 :eax)

;;; addl    -28(%ebp), %eax
    (mrmovl -28 (:ebp) :valu1)
    (addl :valu1 :eax)

;;; movl    $0, (%eax)
    (irmovl 0 :valu1)
    (rmmovl :valu1 0 (:eax))

;;; movl    $0, 4(%eax)
    (irmovl 0 :valu1)
    (rmmovl :valu1 4 (:eax))

;;; addl    $1, -16(%ebp)
    (irmovl 1 :imme1)
    (mrmovl -16 (:ebp) :valu1)
    (addl :imme1 :valu1)
    (rmmovl :valu1 -16 (:ebp))

;;; .L2:
    :L2

;;; movl    -16(%ebp), %eax
    (mrmovl -16 (:ebp) :eax)

;;; cmpl    -20(%ebp), %eax
    (mrmovl -20 (:ebp) :valu1)
    (cmpl :valu1 :eax)

;;; jb      .L3
    (jb :L3)

;;; leave
    (leave)

;;; ret
    (ret)

;;;         .size   sec_not_present, .-sec_not_present
;;; .globl init_pdts
;;;         .type   init_pdts, @function

;;; init_pdts:
    :init_pdts

;;; pushl   %ebp
    (pushl :ebp)

;;; movl    %esp, %ebp
    (rrmovl :esp :ebp)

;;; pushl   %esi
    (pushl :esi)

;;; pushl   %ebx
    (pushl :ebx)

;;; subl    $48, %esp
    (irmovl 48 :imme1)
    (subl :imme1 :esp)

;;; movl    $231, -24(%ebp)
    (irmovl 231 :imme1)
    (rmmovl :imme1 -24 (:ebp))

;;; movl    $0, -20(%ebp)
    (irmovl 0 :imme1)
    (rmmovl :imme1 -20 (:ebp))

;;; movl    $2097152, -16(%ebp)
    (irmovl 2097152 :imme1)
    (rmmovl :imme1 -16 (:ebp))

;;; movl    $0, -12(%ebp)
    (irmovl 0 :imme1)
    (rmmovl :imme1 -12 (:ebp))

;;; movl    $0, -48(%ebp)
    (irmovl 0 :imme1)
    (rmmovl :imme1 -48 (:ebp))

;;; movl    $0, -44(%ebp)
    (irmovl 0 :imme1)
    (rmmovl :imme1 -44 (:ebp))

;;; movl    $0, -32(%ebp)
    (irmovl 0 :imme1)
    (rmmovl :imme1 -32 (:ebp))

;;; jmp     .L7
    (jmp :L7)

;;; .L8:
    :L8

;;; movl    -32(%ebp), %eax
    (mrmovl -32 (:ebp) :eax)

;;; sall    $2, %eax
    (irmovl 2 :imme1)
    (sall :imme1 :eax)

;;; addl    8(%ebp), %eax
    (mrmovl 8 (:ebp) :valu1)
    (addl :valu1 :eax)

;;; movl    (%eax), %eax
    (mrmovl 0 (:eax) :eax)

;;; movl    %eax, -36(%ebp)
    (rmmovl :eax -36 (:ebp))

;;; movl    $0, -28(%ebp)
    (irmovl 0 :imme1)
    (rmmovl :imme1 -28 (:ebp))

;;; jmp     .L9
    (jmp :L9)

;;; .L10:
    :L10

;;; movl    -28(%ebp), %eax
    (mrmovl -28 (:ebp) :eax)

;;; sall    $3, %eax
    (irmovl 3 :imme1)
    (sall :imme1 :eax)

;;; movl    %eax, %esi
    (rrmovl :eax :esi)

;;; addl    -36(%ebp), %esi
    (mrmovl -36 (:ebp) :valu1)
    (addl :valu1 :esi)

;;; movl    -24(%ebp), %ecx
    (mrmovl -24 (:ebp) :ecx)

;;; movl    -20(%ebp), %ebx
    (mrmovl -20 (:ebp) :ebx)

;;; movl    -48(%ebp), %eax
    (mrmovl -48 (:ebp) :eax)

;;; orl     %ecx, %eax
    (orl :ecx :eax)

;;; movl    -44(%ebp), %edx
    (mrmovl -44 (:ebp) :edx)

;;; orl     %ebx, %edx
    (orl :ebx :edx)

;;; movl    %eax, (%esi)
    (rmmovl :eax 0 (:esi))

;;; movl    %edx, 4(%esi)
    (rmmovl :edx 4 (:esi))

;;; movl    -16(%ebp), %eax
    (mrmovl -16 (:ebp) :eax)

;;; movl    -12(%ebp), %edx
    (mrmovl -12 (:ebp) :edx)

;;; addl    %eax, -48(%ebp)
    (mrmovl -48 (:ebp) :valu1)
    (addl :eax :valu1)
    (rmmovl :valu1 -48 (:ebp))

;;; adcl    %edx, -44(%ebp)
    (mrmovl -44 (:ebp) :valu1)
    (adcl :edx :valu1)
    (rmmovl :valu1 -44 (:ebp))

;;; addl    $1, -28(%ebp)
    (irmovl 1 :imme1)
    (mrmovl -28 (:ebp) :valu1)
    (addl :imme1 :valu1)
    (rmmovl :valu1 -28 (:ebp))

;;; .L9:
    :L9

;;; cmpl    $511, -28(%ebp)
    (irmovl 511 :imme1)
    (mrmovl -28 (:ebp) :valu1)
    (cmpl :imme1 :valu1)

;;; jbe     .L10
    (jbe :L10)

;;; addl    $1, -32(%ebp)
    (irmovl 1 :imme1)
    (mrmovl -32 (:ebp) :valu1)
    (addl :imme1 :valu1)
    (rmmovl :valu1 -32 (:ebp))

;;; .L7:
    :L7

;;; cmpl    $3, -32(%ebp)
    (irmovl 3 :imme1)
    (mrmovl -32 (:ebp) :valu1)
    (cmpl :imme1 :valu1)

;;; jbe     .L8
    (jbe :L8)

;;; addl    $48, %esp
    (irmovl 48 :valu1)
    (addl :valu1 :esp)

;;; popl    %ebx
    (popl :ebx)

;;; popl    %esi
    (popl :esi)

;;; popl    %ebp
    (popl :ebp)

;;; ret
    (ret)

;;;         .size   init_pdts, .-init_pdts
;;; .globl init_pdpt
;;;         .type   init_pdpt, @function

;;; init_pdpt:
    :init_pdpt

;;; pushl   %ebp
    (pushl :ebp)

;;; movl    %esp, %ebp
    (rrmovl :esp :ebp)

;;; pushl   %esi
    (pushl :esi)

;;; pushl   %ebx
    (pushl :ebx)

;;; subl    $16, %esp
    (irmovl 16 :valu1)
    (subl :valu1 :esp)

;;; movl    $1, -16(%ebp)
    (irmovl 1 :imme1)
    (rmmovl :imme1 -16 (:ebp))

;;; movl    $0, -12(%ebp)
    (irmovl 0 :imme1)
    (rmmovl :imme1 -12 (:ebp))

;;; movl    $0, -20(%ebp)
    (irmovl 0 :imme1)
    (rmmovl :imme1 -20 (:ebp))

;;; jmp     .L15
    (jmp :L15)

;;; .L16:
    :L16

;;; movl    -20(%ebp), %eax
    (mrmovl -20 (:ebp) :eax)

;;; sall    $3, %eax
    (irmovl 3 :imme1)
    (sall :imme1 :eax)

;;; movl    %eax, %esi
    (rrmovl :eax :esi)

;;; addl    8(%ebp), %esi
    (mrmovl 8 (:ebp) :valu1)
    (addl :valu1 :esi)

;;; movl    -20(%ebp), %eax
    (mrmovl -20 (:ebp) :eax)

;;; sall    $2, %eax
    (irmovl 2 :imme1)
    (sall :imme1 :eax)

;;; addl    12(%ebp), %eax
    (mrmovl 12 (:ebp) :valu1)
    (addl :valu1 :eax)

;;; movl    (%eax), %eax
    (mrmovl 0 (:eax) :eax)

;;; movl    %eax, %ecx
    (rrmovl :eax :ecx)

;;; movl    $0, %ebx
    (irmovl 0 :ebx)

;;; movl    -16(%ebp), %eax
    (mrmovl -16 (:ebp) :eax)

;;; orl     %ecx, %eax
    (orl :ecx :eax)

;;; movl    -12(%ebp), %edx
    (mrmovl -12 (:ebp) :edx)

;;; orl     %ebx, %edx
    (orl :ebx :edx)

;;; movl    %eax, (%esi)
    (rmmovl :eax 0 (:esi))

;;; movl    %edx, 4(%esi)
    (rmmovl :edx 4 (:esi))

;;; addl    $1, -20(%ebp)
    (irmovl 1 :imme1)
    (mrmovl -20 (:ebp) :valu1)
    (addl :imme1 :valu1)
    (rmmovl :valu1 -20 (:ebp))

;;; .L15:
    :L15

;;; cmpl    $3, -20(%ebp)
    (irmovl 3 :imme1)
    (mrmovl -20 (:ebp) :valu1)
    (cmpl :imme1 :valu1)

;;; jbe     .L16
    (jbe :L16)

;;; addl    $16, %esp
    (irmovl 16 :imme1)
    (addl :imme1 :esp)

;;; popl    %ebx
    (popl :ebx)

;;; popl    %esi
    (popl :esi)

;;; popl    %ebp
    (popl :ebp)

;;; ret
    (ret)

;;;         .size   init_pdpt, .-init_pdpt
;;; .globl create_nested_pt
;;;         .type   create_nested_pt, @function

;;; create_nested_pt:
    :create_nested_pt

;;; pushl   %ebp
    (pushl :ebp)

;;; movl    %esp, %ebp
    (rrmovl :esp :ebp)

;;; subl    $16, %esp
    (irmovl 16 :imme1)
    (subl :imme1 :esp)

;;; movl    12(%ebp), %eax
    (mrmovl 12 (:ebp) :eax)

;;; movl    %eax, 4(%esp)
    (rmmovl :eax 4 (:esp))

;;; movl    8(%ebp), %eax
    (mrmovl 8 (:ebp) :eax)

;;; movl    %eax, (%esp)
    (rmmovl :eax 0 (:esp))

;;; call    init_pdpt
    (call :init_pdpt)

;;; movl    12(%ebp), %eax
    (mrmovl 12 (:ebp) :eax)

;;; movl    %eax, (%esp)
    (rmmovl :eax 0 (:esp))

;;; call    init_pdts
    (call :init_pdts)

;;; movl    20(%ebp), %eax
    (mrmovl 20 (:ebp) :eax)

;;; movl    %eax, 8(%esp)
    (rmmovl :eax 8 (:esp))

;;; movl    16(%ebp), %eax
    (mrmovl 16 (:ebp) :eax)

;;; movl    %eax, 4(%esp)
    (rmmovl :eax 4 (:esp))

;;; movl    8(%ebp), %eax
    (mrmovl 8 (:ebp) :eax)

;;; movl    %eax, (%esp)
    (rmmovl :eax 0 (:esp))

;;; call    sec_not_present
    (call :sec_not_present)

;;; movl    8(%ebp), %eax
    (mrmovl 8 (:ebp) :eax)

;;; leave
    (leave)

;;; ret
    (ret)
    ))

;;; I do not want to specify where the code is loaded, but I do need
;;; to be able to say it is loaded somewhere specific, and that the
;;; code fits into the memory.

(encapsulate
 ((snpt-code-location () t))

 (local
  (defun snpt-code-location ()
    42))

 (defthm |(natp (snpt-code-location))|
   (and (integerp (snpt-code-location))
        (< 0 (snpt-code-location)))
   :rule-classes :type-prescription)

 (defthm |irritating crock|
   (and (< 0 (snpt-code-location))
        (< (+ 991 (snpt-code-location))
           (+ -1 (expt 2 32))))
   :rule-classes nil)
)

;;; Note that I have to make the linear lemma outside the encapsulate,
;;; because during linearization of the conclusion, evaluation will
;;; "rewrite" it to true!  Which is not an inequality any more.

(defthm |(n32p (+ 991 (snpt-code-location)))|
  (and (< 0 (snpt-code-location))
       (< (+ 991 (snpt-code-location))
          (+ -1 (expt 2 32))))
  :hints (("Goal" :use ((:instance |irritating crock|))))
  :rule-classes :linear)

;;; I want to be able to specify addresses relative to
;;; (snpt-code-location), so I create a few constants.

(defconst *snpt-symbol-table-for-offsets*
  (y86-symbol-table *snpt-code*
                    0
                    '()))

(defthm handy-reference-thm-for-offsets
  (equal (reverse *snpt-symbol-table-for-offsets*)
         '((:SEC_NOT_PRESENT . 0)
           (:L3 . 247)
           (:L2 . 313)
           (:INIT_PDTS . 334)
           (:L8 . 439)
           (:L10 . 490)
           (:L9 . 614)
           (:L7 . 653)
           (:INIT_PDPT . 687)
           (:L16 . 744)
           (:L15 . 852)
           (:CREATE_NESTED_PT . 886)))
  :rule-classes nil)

;;; The offsets from (snpt-code-location) for the labels.

(defconst *SEC_NOT_PRESENT*
  (cdr (assoc :SEC_NOT_PRESENT *snpt-symbol-table-for-offsets*)))

(defconst *L3*
  (cdr (assoc :L3 *snpt-symbol-table-for-offsets*)))

(defconst *L2*
  (cdr (assoc :L2 *snpt-symbol-table-for-offsets*)))

(defconst *INIT_PDTS*
  (cdr (assoc :INIT_PDTS *snpt-symbol-table-for-offsets*)))

(defconst *L8*
  (cdr (assoc :L8 *snpt-symbol-table-for-offsets*)))

(defconst *L10*
  (cdr (assoc :L10 *snpt-symbol-table-for-offsets*)))

(defconst *L9*
  (cdr (assoc :L9 *snpt-symbol-table-for-offsets*)))

(defconst *L7*
  (cdr (assoc :L7 *snpt-symbol-table-for-offsets*)))

(defconst *INIT_PDPT*
  (cdr (assoc :INIT_PDPT *snpt-symbol-table-for-offsets*)))

(defconst *L16*
  (cdr (assoc :L16 *snpt-symbol-table-for-offsets*)))

(defconst *L15*
  (cdr (assoc :L15 *snpt-symbol-table-for-offsets*)))

(defconst *CREATE_NESTED_PT*
  (cdr (assoc :CREATE_NESTED_PT *snpt-symbol-table-for-offsets*)))

;;; I need to be able to refer to the loaded binary, so I create a
;;; concrete machine.  I will not use it directly anywhere, but see
;;; the various code-loaded-p-xxx functions and theorems.

(defconst *concrete-snpt-code-location*
  0)

(defconst *concrete-snpt-symbol-table*
  (y86-symbol-table *snpt-code*
                    *concrete-snpt-code-location*
                    '()))

(defconst *concrete-snpt-machine*
  (y86-asm *snpt-code*
           *concrete-snpt-code-location*
           *concrete-snpt-symbol-table*
           '((:CR0 . 0) (:CR3 . 0))))

(defconst *concrete-snpt-binary*
  ;; (g :mem *concrete-snpt-machine*)
  '((0 . 160)
    (1 . 88)
    (2 . 32)
    (3 . 69)
    (4 . 48)
    (5 . 136)
    (6 . 48)
    (7 . 0)
    (8 . 0)
    (9 . 0)
    (10 . 97)
    (11 . 132)
    (12 . 48)
    (13 . 136)
    (14 . 0)
    (15 . 240)
    (16 . 255)
    (17 . 255)
    (18 . 64)
    (19 . 133)
    (20 . 248)
    (21 . 255)
    (22 . 255)
    (23 . 255)
    (24 . 48)
    (25 . 136)
    (26 . 255)
    (27 . 255)
    (28 . 255)
    (29 . 255)
    (30 . 64)
    (31 . 133)
    (32 . 252)
    (33 . 255)
    (34 . 255)
    (35 . 255)
    (36 . 80)
    (37 . 5)
    (38 . 12)
    (39 . 0)
    (40 . 0)
    (41 . 0)
    (42 . 48)
    (43 . 136)
    (44 . 30)
    (45 . 0)
    (46 . 0)
    (47 . 0)
    (48 . 104)
    (49 . 128)
    (50 . 64)
    (51 . 5)
    (52 . 244)
    (53 . 255)
    (54 . 255)
    (55 . 255)
    (56 . 80)
    (57 . 5)
    (58 . 244)
    (59 . 255)
    (60 . 255)
    (61 . 255)
    (62 . 48)
    (63 . 136)
    (64 . 3)
    (65 . 0)
    (66 . 0)
    (67 . 0)
    (68 . 103)
    (69 . 128)
    (70 . 80)
    (71 . 165)
    (72 . 8)
    (73 . 0)
    (74 . 0)
    (75 . 0)
    (76 . 96)
    (77 . 160)
    (78 . 80)
    (79 . 32)
    (80 . 4)
    (81 . 0)
    (82 . 0)
    (83 . 0)
    (84 . 80)
    (85 . 0)
    (86 . 0)
    (87 . 0)
    (88 . 0)
    (89 . 0)
    (90 . 64)
    (91 . 5)
    (92 . 208)
    (93 . 255)
    (94 . 255)
    (95 . 255)
    (96 . 64)
    (97 . 37)
    (98 . 212)
    (99 . 255)
    (100 . 255)
    (101 . 255)
    (102 . 80)
    (103 . 5)
    (104 . 248)
    (105 . 255)
    (106 . 255)
    (107 . 255)
    (108 . 80)
    (109 . 165)
    (110 . 208)
    (111 . 255)
    (112 . 255)
    (113 . 255)
    (114 . 98)
    (115 . 160)
    (116 . 64)
    (117 . 5)
    (118 . 216)
    (119 . 255)
    (120 . 255)
    (121 . 255)
    (122 . 80)
    (123 . 5)
    (124 . 252)
    (125 . 255)
    (126 . 255)
    (127 . 255)
    (128 . 80)
    (129 . 165)
    (130 . 212)
    (131 . 255)
    (132 . 255)
    (133 . 255)
    (134 . 98)
    (135 . 160)
    (136 . 64)
    (137 . 5)
    (138 . 220)
    (139 . 255)
    (140 . 255)
    (141 . 255)
    (142 . 80)
    (143 . 5)
    (144 . 216)
    (145 . 255)
    (146 . 255)
    (147 . 255)
    (148 . 64)
    (149 . 5)
    (150 . 224)
    (151 . 255)
    (152 . 255)
    (153 . 255)
    (154 . 80)
    (155 . 5)
    (156 . 224)
    (157 . 255)
    (158 . 255)
    (159 . 255)
    (160 . 64)
    (161 . 5)
    (162 . 228)
    (163 . 255)
    (164 . 255)
    (165 . 255)
    (166 . 80)
    (167 . 5)
    (168 . 12)
    (169 . 0)
    (170 . 0)
    (171 . 0)
    (172 . 48)
    (173 . 136)
    (174 . 0)
    (175 . 0)
    (176 . 224)
    (177 . 63)
    (178 . 98)
    (179 . 128)
    (180 . 48)
    (181 . 136)
    (182 . 21)
    (183 . 0)
    (184 . 0)
    (185 . 0)
    (186 . 104)
    (187 . 128)
    (188 . 64)
    (189 . 5)
    (190 . 232)
    (191 . 255)
    (192 . 255)
    (193 . 255)
    (194 . 80)
    (195 . 5)
    (196 . 12)
    (197 . 0)
    (198 . 0)
    (199 . 0)
    (200 . 80)
    (201 . 165)
    (202 . 16)
    (203 . 0)
    (204 . 0)
    (205 . 0)
    (206 . 96)
    (207 . 160)
    (208 . 48)
    (209 . 136)
    (210 . 0)
    (211 . 0)
    (212 . 224)
    (213 . 63)
    (214 . 98)
    (215 . 128)
    (216 . 48)
    (217 . 136)
    (218 . 21)
    (219 . 0)
    (220 . 0)
    (221 . 0)
    (222 . 104)
    (223 . 128)
    (224 . 64)
    (225 . 5)
    (226 . 236)
    (227 . 255)
    (228 . 255)
    (229 . 255)
    (230 . 80)
    (231 . 5)
    (232 . 232)
    (233 . 255)
    (234 . 255)
    (235 . 255)
    (236 . 64)
    (237 . 5)
    (238 . 240)
    (239 . 255)
    (240 . 255)
    (241 . 255)
    (242 . 112)
    (243 . 71)
    (244 . 0)
    (245 . 0)
    (246 . 0)
    (247 . 80)
    (248 . 5)
    (249 . 240)
    (250 . 255)
    (251 . 255)
    (252 . 255)
    (253 . 48)
    (254 . 138)
    (255 . 3)
    (256 . 0)
    (257 . 0)
    (258 . 0)
    (259 . 103)
    (260 . 160)
    (261 . 80)
    (262 . 165)
    (263 . 228)
    (264 . 255)
    (265 . 255)
    (266 . 255)
    (267 . 96)
    (268 . 160)
    (269 . 48)
    (270 . 138)
    (271 . 0)
    (272 . 0)
    (273 . 0)
    (274 . 0)
    (275 . 64)
    (276 . 160)
    (277 . 0)
    (278 . 0)
    (279 . 0)
    (280 . 0)
    (281 . 48)
    (282 . 138)
    (283 . 0)
    (284 . 0)
    (285 . 0)
    (286 . 0)
    (287 . 64)
    (288 . 160)
    (289 . 4)
    (290 . 0)
    (291 . 0)
    (292 . 0)
    (293 . 48)
    (294 . 136)
    (295 . 1)
    (296 . 0)
    (297 . 0)
    (298 . 0)
    (299 . 80)
    (300 . 165)
    (301 . 240)
    (302 . 255)
    (303 . 255)
    (304 . 255)
    (305 . 96)
    (306 . 138)
    (307 . 64)
    (308 . 165)
    (309 . 240)
    (310 . 255)
    (311 . 255)
    (312 . 255)
    (313 . 80)
    (314 . 5)
    (315 . 240)
    (316 . 255)
    (317 . 255)
    (318 . 255)
    (319 . 80)
    (320 . 165)
    (321 . 236)
    (322 . 255)
    (323 . 255)
    (324 . 255)
    (325 . 101)
    (326 . 160)
    (327 . 119)
    (328 . 176)
    (329 . 255)
    (330 . 255)
    (331 . 255)
    (332 . 208)
    (333 . 144)
    (334 . 160)
    (335 . 88)
    (336 . 32)
    (337 . 69)
    (338 . 160)
    (339 . 104)
    (340 . 160)
    (341 . 56)
    (342 . 48)
    (343 . 136)
    (344 . 48)
    (345 . 0)
    (346 . 0)
    (347 . 0)
    (348 . 97)
    (349 . 132)
    (350 . 48)
    (351 . 136)
    (352 . 231)
    (353 . 0)
    (354 . 0)
    (355 . 0)
    (356 . 64)
    (357 . 133)
    (358 . 232)
    (359 . 255)
    (360 . 255)
    (361 . 255)
    (362 . 48)
    (363 . 136)
    (364 . 0)
    (365 . 0)
    (366 . 0)
    (367 . 0)
    (368 . 64)
    (369 . 133)
    (370 . 236)
    (371 . 255)
    (372 . 255)
    (373 . 255)
    (374 . 48)
    (375 . 136)
    (376 . 0)
    (377 . 0)
    (378 . 32)
    (379 . 0)
    (380 . 64)
    (381 . 133)
    (382 . 240)
    (383 . 255)
    (384 . 255)
    (385 . 255)
    (386 . 48)
    (387 . 136)
    (388 . 0)
    (389 . 0)
    (390 . 0)
    (391 . 0)
    (392 . 64)
    (393 . 133)
    (394 . 244)
    (395 . 255)
    (396 . 255)
    (397 . 255)
    (398 . 48)
    (399 . 136)
    (400 . 0)
    (401 . 0)
    (402 . 0)
    (403 . 0)
    (404 . 64)
    (405 . 133)
    (406 . 208)
    (407 . 255)
    (408 . 255)
    (409 . 255)
    (410 . 48)
    (411 . 136)
    (412 . 0)
    (413 . 0)
    (414 . 0)
    (415 . 0)
    (416 . 64)
    (417 . 133)
    (418 . 212)
    (419 . 255)
    (420 . 255)
    (421 . 255)
    (422 . 48)
    (423 . 136)
    (424 . 0)
    (425 . 0)
    (426 . 0)
    (427 . 0)
    (428 . 64)
    (429 . 133)
    (430 . 224)
    (431 . 255)
    (432 . 255)
    (433 . 255)
    (434 . 112)
    (435 . 219)
    (436 . 0)
    (437 . 0)
    (438 . 0)
    (439 . 80)
    (440 . 5)
    (441 . 224)
    (442 . 255)
    (443 . 255)
    (444 . 255)
    (445 . 48)
    (446 . 136)
    (447 . 2)
    (448 . 0)
    (449 . 0)
    (450 . 0)
    (451 . 103)
    (452 . 128)
    (453 . 80)
    (454 . 165)
    (455 . 8)
    (456 . 0)
    (457 . 0)
    (458 . 0)
    (459 . 96)
    (460 . 160)
    (461 . 80)
    (462 . 0)
    (463 . 0)
    (464 . 0)
    (465 . 0)
    (466 . 0)
    (467 . 64)
    (468 . 5)
    (469 . 220)
    (470 . 255)
    (471 . 255)
    (472 . 255)
    (473 . 48)
    (474 . 136)
    (475 . 0)
    (476 . 0)
    (477 . 0)
    (478 . 0)
    (479 . 64)
    (480 . 133)
    (481 . 228)
    (482 . 255)
    (483 . 255)
    (484 . 255)
    (485 . 112)
    (486 . 129)
    (487 . 0)
    (488 . 0)
    (489 . 0)
    (490 . 80)
    (491 . 5)
    (492 . 228)
    (493 . 255)
    (494 . 255)
    (495 . 255)
    (496 . 48)
    (497 . 136)
    (498 . 3)
    (499 . 0)
    (500 . 0)
    (501 . 0)
    (502 . 103)
    (503 . 128)
    (504 . 32)
    (505 . 6)
    (506 . 80)
    (507 . 165)
    (508 . 220)
    (509 . 255)
    (510 . 255)
    (511 . 255)
    (512 . 96)
    (513 . 166)
    (514 . 80)
    (515 . 21)
    (516 . 232)
    (517 . 255)
    (518 . 255)
    (519 . 255)
    (520 . 80)
    (521 . 53)
    (522 . 236)
    (523 . 255)
    (524 . 255)
    (525 . 255)
    (526 . 80)
    (527 . 5)
    (528 . 208)
    (529 . 255)
    (530 . 255)
    (531 . 255)
    (532 . 102)
    (533 . 16)
    (534 . 80)
    (535 . 37)
    (536 . 212)
    (537 . 255)
    (538 . 255)
    (539 . 255)
    (540 . 102)
    (541 . 50)
    (542 . 64)
    (543 . 6)
    (544 . 0)
    (545 . 0)
    (546 . 0)
    (547 . 0)
    (548 . 64)
    (549 . 38)
    (550 . 4)
    (551 . 0)
    (552 . 0)
    (553 . 0)
    (554 . 80)
    (555 . 5)
    (556 . 240)
    (557 . 255)
    (558 . 255)
    (559 . 255)
    (560 . 80)
    (561 . 37)
    (562 . 244)
    (563 . 255)
    (564 . 255)
    (565 . 255)
    (566 . 80)
    (567 . 165)
    (568 . 208)
    (569 . 255)
    (570 . 255)
    (571 . 255)
    (572 . 96)
    (573 . 10)
    (574 . 64)
    (575 . 165)
    (576 . 208)
    (577 . 255)
    (578 . 255)
    (579 . 255)
    (580 . 80)
    (581 . 165)
    (582 . 212)
    (583 . 255)
    (584 . 255)
    (585 . 255)
    (586 . 100)
    (587 . 42)
    (588 . 64)
    (589 . 165)
    (590 . 212)
    (591 . 255)
    (592 . 255)
    (593 . 255)
    (594 . 48)
    (595 . 136)
    (596 . 1)
    (597 . 0)
    (598 . 0)
    (599 . 0)
    (600 . 80)
    (601 . 165)
    (602 . 228)
    (603 . 255)
    (604 . 255)
    (605 . 255)
    (606 . 96)
    (607 . 138)
    (608 . 64)
    (609 . 165)
    (610 . 228)
    (611 . 255)
    (612 . 255)
    (613 . 255)
    (614 . 48)
    (615 . 136)
    (616 . 255)
    (617 . 1)
    (618 . 0)
    (619 . 0)
    (620 . 80)
    (621 . 165)
    (622 . 228)
    (623 . 255)
    (624 . 255)
    (625 . 255)
    (626 . 101)
    (627 . 138)
    (628 . 120)
    (629 . 118)
    (630 . 255)
    (631 . 255)
    (632 . 255)
    (633 . 48)
    (634 . 136)
    (635 . 1)
    (636 . 0)
    (637 . 0)
    (638 . 0)
    (639 . 80)
    (640 . 165)
    (641 . 224)
    (642 . 255)
    (643 . 255)
    (644 . 255)
    (645 . 96)
    (646 . 138)
    (647 . 64)
    (648 . 165)
    (649 . 224)
    (650 . 255)
    (651 . 255)
    (652 . 255)
    (653 . 48)
    (654 . 136)
    (655 . 3)
    (656 . 0)
    (657 . 0)
    (658 . 0)
    (659 . 80)
    (660 . 165)
    (661 . 224)
    (662 . 255)
    (663 . 255)
    (664 . 255)
    (665 . 101)
    (666 . 138)
    (667 . 120)
    (668 . 28)
    (669 . 255)
    (670 . 255)
    (671 . 255)
    (672 . 48)
    (673 . 138)
    (674 . 48)
    (675 . 0)
    (676 . 0)
    (677 . 0)
    (678 . 96)
    (679 . 164)
    (680 . 176)
    (681 . 56)
    (682 . 176)
    (683 . 104)
    (684 . 176)
    (685 . 88)
    (686 . 144)
    (687 . 160)
    (688 . 88)
    (689 . 32)
    (690 . 69)
    (691 . 160)
    (692 . 104)
    (693 . 160)
    (694 . 56)
    (695 . 48)
    (696 . 138)
    (697 . 16)
    (698 . 0)
    (699 . 0)
    (700 . 0)
    (701 . 97)
    (702 . 164)
    (703 . 48)
    (704 . 136)
    (705 . 1)
    (706 . 0)
    (707 . 0)
    (708 . 0)
    (709 . 64)
    (710 . 133)
    (711 . 240)
    (712 . 255)
    (713 . 255)
    (714 . 255)
    (715 . 48)
    (716 . 136)
    (717 . 0)
    (718 . 0)
    (719 . 0)
    (720 . 0)
    (721 . 64)
    (722 . 133)
    (723 . 244)
    (724 . 255)
    (725 . 255)
    (726 . 255)
    (727 . 48)
    (728 . 136)
    (729 . 0)
    (730 . 0)
    (731 . 0)
    (732 . 0)
    (733 . 64)
    (734 . 133)
    (735 . 236)
    (736 . 255)
    (737 . 255)
    (738 . 255)
    (739 . 112)
    (740 . 113)
    (741 . 0)
    (742 . 0)
    (743 . 0)
    (744 . 80)
    (745 . 5)
    (746 . 236)
    (747 . 255)
    (748 . 255)
    (749 . 255)
    (750 . 48)
    (751 . 136)
    (752 . 3)
    (753 . 0)
    (754 . 0)
    (755 . 0)
    (756 . 103)
    (757 . 128)
    (758 . 32)
    (759 . 6)
    (760 . 80)
    (761 . 165)
    (762 . 8)
    (763 . 0)
    (764 . 0)
    (765 . 0)
    (766 . 96)
    (767 . 166)
    (768 . 80)
    (769 . 5)
    (770 . 236)
    (771 . 255)
    (772 . 255)
    (773 . 255)
    (774 . 48)
    (775 . 136)
    (776 . 2)
    (777 . 0)
    (778 . 0)
    (779 . 0)
    (780 . 103)
    (781 . 128)
    (782 . 80)
    (783 . 165)
    (784 . 12)
    (785 . 0)
    (786 . 0)
    (787 . 0)
    (788 . 96)
    (789 . 160)
    (790 . 80)
    (791 . 0)
    (792 . 0)
    (793 . 0)
    (794 . 0)
    (795 . 0)
    (796 . 32)
    (797 . 1)
    (798 . 48)
    (799 . 131)
    (800 . 0)
    (801 . 0)
    (802 . 0)
    (803 . 0)
    (804 . 80)
    (805 . 5)
    (806 . 240)
    (807 . 255)
    (808 . 255)
    (809 . 255)
    (810 . 102)
    (811 . 16)
    (812 . 80)
    (813 . 37)
    (814 . 244)
    (815 . 255)
    (816 . 255)
    (817 . 255)
    (818 . 102)
    (819 . 50)
    (820 . 64)
    (821 . 6)
    (822 . 0)
    (823 . 0)
    (824 . 0)
    (825 . 0)
    (826 . 64)
    (827 . 38)
    (828 . 4)
    (829 . 0)
    (830 . 0)
    (831 . 0)
    (832 . 48)
    (833 . 136)
    (834 . 1)
    (835 . 0)
    (836 . 0)
    (837 . 0)
    (838 . 80)
    (839 . 165)
    (840 . 236)
    (841 . 255)
    (842 . 255)
    (843 . 255)
    (844 . 96)
    (845 . 138)
    (846 . 64)
    (847 . 165)
    (848 . 236)
    (849 . 255)
    (850 . 255)
    (851 . 255)
    (852 . 48)
    (853 . 136)
    (854 . 3)
    (855 . 0)
    (856 . 0)
    (857 . 0)
    (858 . 80)
    (859 . 165)
    (860 . 236)
    (861 . 255)
    (862 . 255)
    (863 . 255)
    (864 . 101)
    (865 . 138)
    (866 . 120)
    (867 . 134)
    (868 . 255)
    (869 . 255)
    (870 . 255)
    (871 . 48)
    (872 . 136)
    (873 . 16)
    (874 . 0)
    (875 . 0)
    (876 . 0)
    (877 . 96)
    (878 . 132)
    (879 . 176)
    (880 . 56)
    (881 . 176)
    (882 . 104)
    (883 . 176)
    (884 . 88)
    (885 . 144)
    (886 . 160)
    (887 . 88)
    (888 . 32)
    (889 . 69)
    (890 . 48)
    (891 . 136)
    (892 . 16)
    (893 . 0)
    (894 . 0)
    (895 . 0)
    (896 . 97)
    (897 . 132)
    (898 . 80)
    (899 . 5)
    (900 . 12)
    (901 . 0)
    (902 . 0)
    (903 . 0)
    (904 . 64)
    (905 . 4)
    (906 . 4)
    (907 . 0)
    (908 . 0)
    (909 . 0)
    (910 . 80)
    (911 . 5)
    (912 . 8)
    (913 . 0)
    (914 . 0)
    (915 . 0)
    (916 . 64)
    (917 . 4)
    (918 . 0)
    (919 . 0)
    (920 . 0)
    (921 . 0)
    (922 . 128)
    (923 . 21)
    (924 . 255)
    (925 . 255)
    (926 . 255)
    (927 . 80)
    (928 . 5)
    (929 . 12)
    (930 . 0)
    (931 . 0)
    (932 . 0)
    (933 . 64)
    (934 . 4)
    (935 . 0)
    (936 . 0)
    (937 . 0)
    (938 . 0)
    (939 . 128)
    (940 . 163)
    (941 . 253)
    (942 . 255)
    (943 . 255)
    (944 . 80)
    (945 . 5)
    (946 . 20)
    (947 . 0)
    (948 . 0)
    (949 . 0)
    (950 . 64)
    (951 . 4)
    (952 . 8)
    (953 . 0)
    (954 . 0)
    (955 . 0)
    (956 . 80)
    (957 . 5)
    (958 . 16)
    (959 . 0)
    (960 . 0)
    (961 . 0)
    (962 . 64)
    (963 . 4)
    (964 . 4)
    (965 . 0)
    (966 . 0)
    (967 . 0)
    (968 . 80)
    (969 . 5)
    (970 . 8)
    (971 . 0)
    (972 . 0)
    (973 . 0)
    (974 . 64)
    (975 . 4)
    (976 . 0)
    (977 . 0)
    (978 . 0)
    (979 . 0)
    (980 . 128)
    (981 . 44)
    (982 . 252)
    (983 . 255)
    (984 . 255)
    (985 . 80)
    (986 . 5)
    (987 . 8)
    (988 . 0)
    (989 . 0)
    (990 . 0)
    (991 . 208)
    (992 . 144)))

(defthm check-code
  (equal (g :mem *concrete-snpt-machine*)
         *concrete-snpt-binary*)
  :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Specifying the machine is well-formed to run the code

;;; the code is loaded

;;; The code loaded into the abstract machine is the same as that in
;;; the concrete machine, but the location is shifted by
;;; (snpt-code-location).

;;; This section should be generated automatically.

(defun code-loaded-p-1 (lower upper i s)
  (declare (xargs :measure (nfix (+ 1 upper (- lower) (- i)))
                  :hints (("Goal" :in-theory (disable assoc)))))
  (if (or (not (integerp lower))
          (not (integerp upper))
          (not (integerp i))
          (< (+ upper (- lower) (- i)) 0))
      'T
    (and (equal (r08 (+ lower i) s)
                (cdr (assoc (+ lower i (- (snpt-code-location)))
                            *concrete-snpt-binary*)))
         (code-loaded-p-1 lower upper (+ 1 i) s))))

(defun code-loaded-p (lower upper s)
  (code-loaded-p-1 lower upper 0 s))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (local
  (defthm crock-1
   (implies (and (code-loaded-p-1 lower upper i s)
                 (integerp lower)
                 (integerp upper)
                 (integerp i)
                 (integerp n)
                 (<= lower upper)
                 (<= (+ i lower) n)
                 (<= n upper))
            (equal (r08 n s)
                   (cdr (assoc (+ n (- (snpt-code-location)))
                               *concrete-snpt-binary*))))
    :hints (("Goal" :in-theory (disable assoc)))))

(defthm code-loaded-p-thm-08
   (implies (and (code-loaded-p lower upper s)
                 (integerp lower)
                 (integerp upper)
                 (integerp n)
                 (<= lower n)
                 (<= n upper))
            (equal (r08 n s)
                   (cdr (assoc (+ n (- (snpt-code-location)))
                               *concrete-snpt-binary*))))
   :hints (("Goal" :in-theory (disable assoc))))

(defthm code-loaded-p-thm-32
   (implies (and (code-loaded-p lower upper s)
                 (not (paging-p s))
                 (memoryp (g :mem s))
                 (integerp lower)
                 (integerp upper)
                 (integerp n)
                 (good-32-address-p n s)
                 (<= lower n)
                 (<= (+ 3 n) upper))
            (equal (r32 n s)
                   (let ((n (+ n (- (snpt-code-location)))))
                     (LET ((BYTE0 (cdr (assoc      n  *concrete-snpt-binary*)))
                           (BYTE1 (cdr (assoc (+ 1 n) *concrete-snpt-binary*)))
                           (BYTE2 (cdr (assoc (+ 2 n) *concrete-snpt-binary*)))
                           (BYTE3 (cdr (assoc (+ 3 n) *concrete-snpt-binary*))))
                          (+ (ASH BYTE3 24)
                             (ASH BYTE2 16)
                             (ASH BYTE1 8)
                             BYTE0)))))
   :hints (("Goal" :use ((:instance r32-from-four-r08
                                    (addr n)
                                    (byte0 (r08 n s))
                                    (byte1 (r08 (+ 1 n) s))
                                    (byte2 (r08 (+ 2 n) s))
                                    (byte3 (r08 (+ 3 n) s))))
                   :in-theory (e/d (good-32-address-p)
                                   (code-loaded-p
                                    assoc
                                    ash)))))

)

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (local
  (defthm crock-1
    (implies (and (code-loaded-p-1 lower upper i s)
                  (<= 0 (+ upper (- lower)))
                  (<= 0 i)
                  (<= (+ i lower) upper)
                  (memoryp (g :mem s))
                  (not (paging-p s))
                  (n32p addr)
                  (n32p lower)
                  (n32p upper)
                  (disjointp (list (range lower 0 (+ 1 upper (- lower)))
                                   (list addr))))
             (code-loaded-p-1 lower upper i (w08 addr val s)))
    :hints (("Goal" :in-theory (disable assoc)))))

 (local
  (defthm crock-2
    (implies (and (code-loaded-p-1 lower upper i s)
                  (<= 0 (+ upper (- lower)))
                  (<= 0 i)
                  (<= (+ i lower) upper)
                  (memoryp (g :mem s))
                  (not (paging-p s))
                  (good-32-address-p addr s)
                  (n32p lower)
                  (n32p upper)
                  (disjointp (list (range lower 0 (+ 1 upper (- lower)))
                                   (range addr 0 4))))
             (code-loaded-p-1 lower upper i (w32 addr val s)))
    :hints (("Goal" :in-theory (disable assoc)))))

 (defthm |(code-loaded-p lower upper (w08 addr s))|
   (implies (and (code-loaded-p lower upper s)
                 (<= 0 (+ upper (- lower)))
                 (memoryp (g :mem s))
                 (not (paging-p s))
                 (n32p addr)
                 (n32p lower)
                 (n32p upper)
                 (disjointp (list (range lower 0 (+ 1 upper (- lower)))
                                  (list addr))))
            (code-loaded-p lower upper (w08 addr val s)))
   :hints (("Goal" :in-theory (disable assoc))))

 (defthm |(code-loaded-p lower upper (w32 addr s))|
   (implies (and (code-loaded-p lower upper s)
                 (<= 0 (+ upper (- lower)))
                 (memoryp (g :mem s))
                 (not (paging-p s))
                 (good-32-address-p addr s)
                 (n32p lower)
                 (n32p upper)
                 (disjointp (list (range lower 0 (+ 1 upper (- lower)))
                                  (range addr 0 4))))
            (code-loaded-p lower upper (w32 addr val s)))
   :hints (("Goal" :in-theory (disable assoc))))
 )

(defun sec_not_present-loaded-p (s)
  (code-loaded-p (+ *SEC_NOT_PRESENT* (snpt-code-location))
                 (+ -1 *INIT_PDTS* (snpt-code-location))
                 s))

(defthm sec_not_present-loaded-thm-08
  (implies (and (syntaxp (intersectp-equal (non-quotep-addends n)
                                           '((snpt-code-location))))
                (sec_not_present-loaded-p s)
                (integerp n)
                (<= (+ *SEC_NOT_PRESENT* (snpt-code-location)) n)
                (<= n (+ -1 *INIT_PDTS* (snpt-code-location))))
           (equal (r08 n s)
                  (cdr (assoc (+ n (- (snpt-code-location)))
                              *concrete-snpt-binary*))))
   :hints (("Goal" :in-theory (disable code-loaded-p
                                       assoc))))

(defthm sec_not_present-loaded-thm-32
  (implies (and (syntaxp (intersectp-equal (non-quotep-addends n)
                                           '((snpt-code-location))))
                (sec_not_present-loaded-p s)
                (not (paging-p s))
                (memoryp (g :mem s))
                (integerp n)
                (<= (+ *SEC_NOT_PRESENT* (snpt-code-location)) n)
                (<= (+ 3 n) (+ -1 *INIT_PDTS* (snpt-code-location))))
           (equal (r32 n s)
                  (let ((n (+ n (- (snpt-code-location)))))
                    (LET ((BYTE0 (cdr (assoc      n  *concrete-snpt-binary*)))
                          (BYTE1 (cdr (assoc (+ 1 n) *concrete-snpt-binary*)))
                          (BYTE2 (cdr (assoc (+ 2 n) *concrete-snpt-binary*)))
                          (BYTE3 (cdr (assoc (+ 3 n) *concrete-snpt-binary*))))
                         (+ (ASH BYTE3 24)
                            (ASH BYTE2 16)
                            (ASH BYTE1 8)
                            BYTE0)))))
  :hints (("Goal" :in-theory (disable code-loaded-p
                                      assoc
                                      ash))))

(defun init_pdts-loaded-p (s)
  (code-loaded-p (+ *INIT_PDTS* (snpt-code-location))
                 (+ -1 *INIT_PDPT* (snpt-code-location))
                 s))

(defthm init_pdts-loaded-thm-08
  (implies (and (syntaxp (intersectp-equal (non-quotep-addends n)
                                           '((snpt-code-location))))
                (init_pdts-loaded-p s)
                (integerp n)
                (<= (+ *INIT_PDTS* (snpt-code-location)) n)
                (<= n (+ -1 *INIT_PDPT* (snpt-code-location))))
           (equal (r08 n s)
                  (cdr (assoc (+ n (- (snpt-code-location)))
                              *concrete-snpt-binary*))))
   :hints (("Goal" :in-theory (disable code-loaded-p
                                       assoc))))

(defthm init_pdts-loaded-thm-32
  (implies (and (syntaxp (intersectp-equal (non-quotep-addends n)
                                           '((snpt-code-location))))
                (init_pdts-loaded-p s)
                (not (paging-p s))
                (memoryp (g :mem s))
                (integerp n)
                (<= (+ *INIT_PDTS* (snpt-code-location)) n)
                (<= (+ 3 n) (+ -1 *INIT_PDPT* (snpt-code-location))))
           (equal (r32 n s)
                  (let ((n (+ n (- (snpt-code-location)))))
                    (LET ((BYTE0 (cdr (assoc      n  *concrete-snpt-binary*)))
                          (BYTE1 (cdr (assoc (+ 1 n) *concrete-snpt-binary*)))
                          (BYTE2 (cdr (assoc (+ 2 n) *concrete-snpt-binary*)))
                          (BYTE3 (cdr (assoc (+ 3 n) *concrete-snpt-binary*))))
                         (+ (ASH BYTE3 24)
                            (ASH BYTE2 16)
                            (ASH BYTE1 8)
                            BYTE0)))))
   :hints (("Goal" :in-theory (disable code-loaded-p
                                       assoc
                                       ash))))

(defun init_pdpt-loaded-p (s)
  (code-loaded-p (+ *INIT_PDPT* (snpt-code-location))
                 (+ -1 *CREATE_NESTED_PT* (snpt-code-location))
                 s))

(defthm init_pdpt-loaded-thm-08
  (implies (and (syntaxp (intersectp-equal (non-quotep-addends n)
                                           '((snpt-code-location))))
                (init_pdpt-loaded-p s)
                (integerp n)
                (<= (+ *INIT_PDPT* (snpt-code-location)) n)
                (<= n (+ -1 *CREATE_NESTED_PT* (snpt-code-location))))
           (equal (r08 n s)
                  (cdr (assoc (+ n (- (snpt-code-location)))
                              *concrete-snpt-binary*))))
   :hints (("Goal" :in-theory (disable code-loaded-p
                                       assoc))))

(defthm init_pdpt-loaded-thm-32
  (implies (and (syntaxp (intersectp-equal (non-quotep-addends n)
                                           '((snpt-code-location))))
                (init_pdpt-loaded-p s)
                (not (paging-p s))
                (memoryp (g :mem s))
                (integerp n)
                (<= (+ *INIT_PDPT* (snpt-code-location)) n)
                (<= (+ 3 n) (+ -1 *CREATE_NESTED_PT* (snpt-code-location))))
           (equal (r32 n s)
                  (let ((n (+ n (- (snpt-code-location)))))
                    (LET ((BYTE0 (cdr (assoc      n  *concrete-snpt-binary*)))
                          (BYTE1 (cdr (assoc (+ 1 n) *concrete-snpt-binary*)))
                          (BYTE2 (cdr (assoc (+ 2 n) *concrete-snpt-binary*)))
                          (BYTE3 (cdr (assoc (+ 3 n) *concrete-snpt-binary*))))
                         (+ (ASH BYTE3 24)
                            (ASH BYTE2 16)
                            (ASH BYTE1 8)
                            BYTE0)))))
   :hints (("Goal" :in-theory (disable code-loaded-p
                                       assoc
                                       ash))))

(defun create_nested_pt-loaded-p (s)
  (code-loaded-p (+ *CREATE_NESTED_PT* (snpt-code-location))
                 (+ 992 (snpt-code-location))
                 s))

(defthm create_nested_pt-loaded-thm-08
  (implies (and (syntaxp (intersectp-equal (non-quotep-addends n)
                                           '((snpt-code-location))))
                (create_nested_pt-loaded-p s)
                (integerp n)
                (<= (+ *CREATE_NESTED_PT* (snpt-code-location)) n)
                (<= n (+ 992 (snpt-code-location))))
           (equal (r08 n s)
                  (cdr (assoc (+ n (- (snpt-code-location)))
                              *concrete-snpt-binary*))))
   :hints (("Goal" :in-theory (disable code-loaded-p
                                       assoc))))

(defthm create_nested_pt-loaded-thm-32
  (implies (and (syntaxp (intersectp-equal (non-quotep-addends n)
                                           '((snpt-code-location))))
                (create_nested_pt-loaded-p s)
                (not (paging-p s))
                (memoryp (g :mem s))
                (integerp n)
                (<= (+ *CREATE_NESTED_PT* (snpt-code-location)) n)
                (<= (+ 3 n) (+ 992 (snpt-code-location))))
           (equal (r32 n s)
                  (let ((n (+ n (- (snpt-code-location)))))
                    (LET ((BYTE0 (cdr (assoc      n  *concrete-snpt-binary*)))
                          (BYTE1 (cdr (assoc (+ 1 n) *concrete-snpt-binary*)))
                          (BYTE2 (cdr (assoc (+ 2 n) *concrete-snpt-binary*)))
                          (BYTE3 (cdr (assoc (+ 3 n) *concrete-snpt-binary*))))
                         (+ (ASH BYTE3 24)
                            (ASH BYTE2 16)
                            (ASH BYTE1 8)
                            BYTE0)))))
  :hints (("Goal" :in-theory (disable code-loaded-p
                                      assoc
                                      ash))))

(defun all-code-loaded-p (s)
  (and (sec_not_present-loaded-p s)
       (init_pdts-loaded-p s)
       (init_pdpt-loaded-p s)
       (create_nested_pt-loaded-p s)))

(defthm all-code-loaded-p-fc
  (implies (all-code-loaded-p s)
           (and (sec_not_present-loaded-p s)
                (init_pdts-loaded-p s)
                (init_pdpt-loaded-p s)
                (create_nested_pt-loaded-p s)))
  :rule-classes :forward-chaining)

;;; and all is good

(defun good-state-p (s)
  (and (y86-p s)
       (all-code-loaded-p s)))

(defthm good-state-p-fc
  (implies (good-state-p s)
           (and (y86-p s)
                (all-code-loaded-p s)))
  :hints (("Goal" :in-theory (disable code-loaded-p)))
  :rule-classes :forward-chaining)

(encapsulate
 ()

 (local
  (defthm crock-1-1
    (IMPLIES (AND (CODE-LOADED-P-1 upper lower i S)
                  (not (equal field :cr0))
                  (not (equal field :cr3))
                  (NOT (EQUAL FIELD :MEM)))
             (CODE-LOADED-P-1 upper lower i
                                 (UPDATE-REGS FIELD VAL S)))
    :hints (("Goal" :in-theory (e/d ()
                                    (assoc))))))

 (local
  (defthm crock-1
    (implies (and (code-loaded-p upper lower s)
                  (not (equal field :cr0))
                  (not (equal field :cr3))
                  (not (equal field :mem)))
             (code-loaded-p upper lower (s field val s)))
    :hints (("Goal" :in-theory (e/d ()
                                    (assoc))))))

 (local
  (defthm crock-3
    (equal (g field1 (s field2 val s))
           (if (equal field1 field2)
               val
             (g field1 s)))
    :hints (("Goal" :use ((:instance g-same-s
                                     (a field1)
                                     (v val)
                                     (r s))
                          (:instance g-diff-s
                                     (a field1)
                                     (b field2)
                                     (v val)
                                     (r s)))))))

 (defthm |(good-state-p (s field val) s) --- n32p|
   (implies (and (good-state-p s)
                 (memberp field '(:eax :ebx :ecx :edx
                                  :esi :edi :esp :ebp :eip
                                  :eflags :zteps
                                  :imme1 :valu1
                                  :user-eip :user-esp :sys-eip :sys-esp))
                 (n32p val))
            (good-state-p (s field val s)))
   :hints (("Goal" :in-theory (e/d (y86-p
                                   y86-register-guard
                                   y86-flags-guard
                                   y86-misc-guard
                                   y86-supervisor-guard
                                   memberp)
                                   (code-loaded-p))))
   :otf-flg t)

 (defthm |(good-state-p (s field val) s) --- n01p|
   (implies (and (good-state-p s)
                 (memberp field '(:f-cf :f-of :f-sf :f-zf
                                  :supervisor-mode))
                 (n01p val))
            (good-state-p (s field val s)))
   :hints (("Goal" :in-theory (e/d (y86-p
                                   y86-register-guard
                                   y86-flags-guard
                                   y86-misc-guard
                                   y86-supervisor-guard
                                   memberp)
                                   (code-loaded-p))))
   :otf-flg t)

 (defthm |(good-state-p (w32 addr val s))|
   (implies (and (good-state-p s)
                 (not (paging-p s))
                 (good-32-address-p addr s)
                 (n32p val)
                 (disjointp (list (range (snpt-code-location) 0 993)
                                  (range addr 0 4))))
            (good-state-p (w32 addr val s)))
   :hints (("Goal" :in-theory (e/d (y86-p
                                   y86-register-guard
                                   y86-flags-guard
                                   y86-misc-guard
                                   y86-supervisor-guard
                                   memberp)
                                   (code-loaded-p))))
   :otf-flg t)

 )

(in-theory (disable code-loaded-p
                    code-loaded-p-thm-08
                    code-loaded-p-thm-32
                    sec_not_present-loaded-p
                    init_pdts-loaded-p
                    init_pdpt-loaded-p
                    create_nested_pt-loaded-p
                    all-code-loaded-p
                    good-state-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; init_pdpt

;;; set up the top level page descriptor pointer table --- holds four
;;; entries, pointing to the lower level page descriptor tables

;;; this is what I would like to use,
(defun in-init_pdpt (s)
  (let ((eip (g :eip s)))
    (and (<= (+ *INIT_PDPT* (snpt-code-location)) eip)
         (< eip (+ *CREATE_NESTED_PT* (snpt-code-location))))))

;;; but we need to have only one in-sub for everything when using
;;; Sandip's macros
;;; !!! should probably be based upon stack height instead
(defun in-sub (s)
  (let ((eip (g :eip s)))
    (and (<= (+ *SEC_NOT_PRESENT* (snpt-code-location)) eip)
         (< eip (+ *CREATE_NESTED_PT* (snpt-code-location))))))

(defun init_pdpt-cutpoint-p (s)
  (let ((eip (g :eip s)))
    (or (equal eip (+ *INIT_PDPT* (snpt-code-location))) ; start
        (equal eip (+ *L15* (snpt-code-location)))       ; loop test
        (not (in-sub s)))))                        ; exit

(defun init_pdpt-pre (s)
  (and (good-state-p s)
       (equal (g :eip s) (+ *INIT_PDPT* (snpt-code-location)))
       (not (paging-p s))
       (disjointp (list (range (snpt-code-location) 0 993)            ; code
                        (range (g :esp s) -24 36)                     ; stack
                        (range (r32 (+ 4 (g :esp s)) s) 0 (* 4 8))    ; pdpt
                        (range (r32 (+ 8 (g :esp s)) s) 0 (* 4 4))))  ; pdt pointer array
       ;; all stack addresses are "good" --- the stack does not wrap around memory
       (n32p (+ -28 (g :esp s)))
       (n32p (+ 11 (g :esp s)))
       ;; addresses in pdpt and pdt pointer array are "good"
       (n32p (+ 31 (r32 (+ 4 (g :esp s)) s)))
       (n32p (+ 27 (r32 (+ 8 (g :esp s)) s))) ; 15 is not enough?
       ;; we return to create_nested_pt
       (< (+ *CREATE_NESTED_PT* (snpt-code-location)) (R32 (g :esp s) S))
       ;; ??? needed tp prove init_pdpt-modify returns a y86-p
       (N32P (+ 1
                (R32 (+ 12 (R32 (+ 8 (G :ESP S)) S))
                     S)))
       ))

(defun init_pdpt-loop-pre (s)
  (and (good-state-p s)
       (equal (g :eip s) (+ *L15* (snpt-code-location)))
       (not (paging-p s))
       (disjointp (list (range (snpt-code-location) 0 993)                 ; code
                        (range (+ 4 (g :ebp s)) -24 36)                    ; stack
                        (range (r32 (+ 4 (+ 4 (g :ebp s))) s) 0 (* 4 8))   ; pdpt
                        (range (r32 (+ 8 (+ 4 (g :ebp s))) s) 0 (* 4 4)))) ; pdt pointer array
       ;; all stack addresses are "good" --- the stack does not wrap around memory
       (n32p (+ -28 (+ 4 (g :ebp s))))
       (n32p (+ 11 (+ 4 (g :ebp s))))
       ;; addresses in pdpt and pdt pointer array are "good"
       (n32p (+ 31 (r32 (+ 4 (+ 4 (g :ebp s))) s)))
       (n32p (+ 15 (r32 (+ 8 (+ 4 (g :ebp s))) s)))
       ;; we return to create_nested_pt
       (< (+ *CREATE_NESTED_PT* (snpt-code-location)) (R32 (+ 4 (G :EBP S)) S))
       ;; the alignment of :esp and :ebp --- why do we need this?
       (equal (g :esp s) (+ -24 (g :ebp s)))
       ;; loop-counter, we are in the loop
       (<= (r32 (+ -20 (g :ebp s)) s) 4)))

(defun init_pdpt-modify-loop-1 (loop-counter s)
  (if (zp loop-counter)
      (update-mem (R32 (+ 4 (G :ESP S)) S)
                  (LOGIOR 1
                          (R32 (R32 (+ 8 (G :ESP S)) S)
                               S))

                  (+ 4
                     (R32 (+ 4 (G :ESP S)) S))
                  0
                  s)
    (init_pdpt-modify-loop-1 (+ -1 loop-counter)
                             (update-mem (+ (* 8 LOOP-COUNTER)
                                            (R32 (+ 4 (G :ESP S)) S))
                                         (LOGIOR 1
                                                 (R32 (+ (* 4 LOOP-COUNTER)
                                                         (R32 (+ 8 (G :ESP S)) S))
                                                      S))

                                         (+ 4 (* 8 LOOP-COUNTER)
                                            (R32 (+ 4 (G :ESP S)) S))
                                         0
                                         s))))

(defthm |(paging-p (init_pdpt-modify-loop-1 loop-counter s))|
  (equal (paging-p (init_pdpt-modify-loop-1 loop-counter s))
         (paging-p s)))

(defthm |(va-to-pa addr (init_pdpt-modify-loop-1 loop-counter s))|
  (implies (not (paging-p s))
           (equal (va-to-pa addr (init_pdpt-modify-loop-1 loop-counter s))
                  (va-to-pa addr s))))

(defthm |(good-32-address-p addr (init_pdpt-modify-loop-1 loop-counter s))|
  (implies (not (paging-p s))
           (equal (good-32-address-p addr (init_pdpt-modify-loop-1 loop-counter s))
                  (good-32-address-p addr s)))
  :hints (("Goal" :in-theory (enable good-32-address-p))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm |(memoryp (g :mem (init_pdpt-modify-loop-1 loop-counter s)))|
   (implies (and (y86-p s)
                 ;; Only needed because of absence of rules about
                 ;; partially overlapping reads and writes
                 (disjointp (list (range (g :esp s) -24 36)
                                  (range (r32 (+ 4 (g :esp s)) s) 0 (+ 8 (* loop-counter 8)))))
                 (n32p (+ 11 (g :esp s)))
                 (n32p (+ (+ 7 (* loop-counter 8)) (R32 (+ 4 (G :ESP S)) S)))
                 (not (paging-p s))
                 (integerp loop-counter)
                 (<= 0 loop-counter)
                 ;; (< loop-counter 4)
                 )
            (memoryp (g :mem (init_pdpt-modify-loop-1 loop-counter s))))
   :hints (("Goal" :in-theory (disable |(logior 1 x)|
                                       y86-p))))

 (defthm |(good-state-p (init_pdpt-modify-loop-1 loop-counter s))|
   (implies (and (good-state-p s)
                 ;; Only needed because of absence of rules about
                 ;; partially overlapping reads and writes
                 (disjointp (list (range (g :esp s) -24 36)
                                  (range (r32 (+ 4 (g :esp s)) s) 0 (+ 8 (* loop-counter 8)))
                                  (RANGE (SNPT-CODE-LOCATION) 0 993)))
                 (n32p (+ 11 (g :esp s)))
                 (n32p (+ (+ 7 (* loop-counter 8)) (R32 (+ 4 (G :ESP S)) S)))
                 (not (paging-p s))
                 (integerp loop-counter)
                 (<= 0 loop-counter)
                 ;; (< loop-counter 4)
                 )
            (good-state-p (init_pdpt-modify-loop-1 loop-counter s)))
   :hints (("Goal" :in-theory (disable |(logior 1 x)|
                                       y86-p))))

 (defthm |(r32 addr (init_pdpt-modify-loop-1 loop-counter s))|
   (implies (and (y86-p s)
                 (disjointp (list (range addr 0 4)
                                  (range (r32 (+ 4 (g :esp s)) s) 0 (+ 8 (* loop-counter 8)))))
                 (disjointp (list (range (g :esp s) -24 36)
                                  (range (r32 (+ 4 (g :esp s)) s) 0 (+ 8 (* loop-counter 8)))))
                 (n32p addr)
                 (n32p (+ 3 addr))
                 (n32p (+ 11 (g :esp s)))
                 (n32p (+ (+ 7 (* loop-counter 8)) (R32 (+ 4 (G :ESP S)) S)))
                 (not (paging-p s))
                 (integerp loop-counter)
                 (<= 0 loop-counter)
                 ;;(< loop-counter 4)
                 )
            (equal (r32 addr (init_pdpt-modify-loop-1 loop-counter s))
                   (r32 addr s)))
   :hints (("Goal" :in-theory (disable |(logior 1 x)|
                                       y86-p))))

 (defthm |(init_pdpt-modify-loop-1 loop-counter (w32 addr val s))|
   (implies (and (y86-p s)
                 (disjointp (list (range addr 0 4)
                                  (range (g :esp s) -24 36)))
                 (disjointp (list (range addr 0 4)
                                  (range (r32 (+ 4 (g :esp s)) s) 0 (+ 8 (* 8 loop-counter)))))
                 (disjointp (list (range addr 0 4)
                                  (range (r32 (+ 8 (g :esp s)) s) 0 (+ 4 (* 4 loop-counter)))))
                 ;; Only needed because of absence of rules about ;
                 ;; partially overlapping reads and writes ;
                 (disjointp (list (range (g :esp s) -24 36)
                                  (range (r32 (+ 4 (g :esp s)) s) 0 (+ 8 (* 8 loop-counter)))))
                 (n32p addr)
                 (n32p (+ 3 addr))
                 (n32p (+ 11 (g :esp s)))
                 (n32p (+ 31 (R32 (+ 4 (G :ESP S)) S)))
                 (n32p (+ 15 (R32 (+ 8 (G :ESP S)) S)))
                 (not (paging-p s))
                 (integerp loop-counter)
                 (<= 0 loop-counter)
                 (< loop-counter 4))
            (equal (init_pdpt-modify-loop-1 loop-counter
                                            (w32 addr val s))
                   (w32 addr val (init_pdpt-modify-loop-1 loop-counter s))))
   :hints (("Goal" :in-theory (disable |(logior 1 x)|
                                       y86-p))))

 (defthm |(r32 addr (init_pdpt-modify-loop-1 loop-counter s)) --- written to 1|
   (implies (and (y86-p s)
                 (disjointp (list (range (g :esp s) -24 36)
                                  (range (r32 (+ 4 (g :esp s)) s) 0 (+ 8 (* loop-counter 8)))))


                 (disjointp (list (range (r32 (+ 4 (g :esp s)) s) 0 (+ 8 (* loop-counter 8)))
                                  (range (r32 (+ 8 (g :esp s)) s) 0 (+ 4 (* loop-counter 4)))))

                 (integerp i)
                 (<= 0 i)
                 (<= i loop-counter)

                 (n32p (+ 4 (* 8 i)
                          (R32 (+ 4 (G :ESP S)) S)))
                 (n32p (+ 3 4 (+ (* 8 i)
                                 (R32 (+ 4 (G :ESP S)) S))))
                 (n32p (+ 11 (g :esp s)))
                 (n32p (+ (+ 7 (* LOOP-COUNTER 8)) (R32 (+ 4 (G :ESP S)) S)))
                 (n32p (+ (+ 3 (* LOOP-COUNTER 8)) (R32 (+ 8 (G :ESP S)) S)))

                 (not (paging-p s))
                 (integerp loop-counter)
                 (<= 0 loop-counter)
                 ;; (< loop-counter 4)
                 )
            (equal (r32 (+ (* 8 i)
                           (R32 (+ 4 (G :ESP S)) S))
                        (init_pdpt-modify-loop-1 loop-counter s))
                   (LOGIOR 1
                           (R32 (+ (* 4 i)
                                   (R32 (+ 8 (G :ESP S)) S))
                                S))))
   :hints (("Goal" :in-theory (disable |(logior 1 x)|
                                       y86-p))
           ("Subgoal *1/5" :expand ((INIT_PDPT-MODIFY-LOOP-1 I S)))))

 (defthm |(r32 addr (init_pdpt-modify-loop-1 loop-counter s)) --- written to 2|
   (implies (and (y86-p s)
                 (disjointp (list (range (g :esp s) -24 36)
                                  (range (r32 (+ 4 (g :esp s)) s) 0 (+ 8 (* loop-counter 8)))))

                 (integerp i)
                 (<= 0 i)
                 (<= i loop-counter)

                 (n32p (+ 4 (* 8 i)
                          (R32 (+ 4 (G :ESP S)) S)))
                 (n32p (+ 3 4 (+ (* 8 i)
                                 (R32 (+ 4 (G :ESP S)) S))))
                 (n32p (+ 11 (g :esp s)))
                 (n32p (+ (+ 7 (* LOOP-COUNTER 8)) (R32 (+ 4 (G :ESP S)) S)))
                 (N32P (+ 15 (R32 (+ 8 (G :ESP S)) S)))

                 (not (paging-p s))
                 (integerp loop-counter)
                 (<= 0 loop-counter)
                 ;; (< loop-counter 4)
                 )
            (equal (r32 (+ 4
                           (* 8 i)
                           (R32 (+ 4 (G :ESP S)) S))
                        (init_pdpt-modify-loop-1 loop-counter s))
                   0))
   :hints (("Goal" :in-theory (disable |(logior 1 x)|
                                       y86-p))
           ("Subgoal *1/4" :expand ((INIT_PDPT-MODIFY-LOOP-1 I S)))))
 )


(defun init_pdpt-modify-loop (loop-counter cf of sf zf imme1 valu1 s)
  (if (equal loop-counter 0)

      (UPDATE-REGS :EBP (+ -4 (G :ESP S))
                   :EIP (+ 852 (SNPT-CODE-LOCATION))
                   :ESP (+ -28 (G :ESP S))
                   :F-CF cf
                   :F-OF of
                   :F-SF sf
                   :F-ZF zf
                   :IMME1 imme1
                   :VALU1 valu1
                   (UPDATE-MEM (+ -4 (G :ESP S)) (G :EBP S)
                               (+ -8 (G :ESP S)) (G :ESI S)
                               (+ -12 (G :ESP S)) (G :EBX S)
                               ;; 64-bit page present
                               (+ -16 (G :ESP S)) 0
                               (+ -20 (G :ESP S)) 1
                               ;; i --- loop counter
                               (+ -24 (G :ESP S)) 0
                               S))

    (let ((loop-counter (+ -1 loop-counter)))
      (UPDATE-REGS :EAX (LOGIOR 1
                                (R32 (+ (* 4 LOOP-COUNTER)
                                        (R32 (+ 8 (G :ESP S)) S))
                                     S))
                   :EBP (+ -4 (G :ESP S))
                   :EBX 0
                   :ECX (R32 (+ (* 4 LOOP-COUNTER)
                                (R32 (+ 8 (G :ESP S)) S))
                             S)
                   :EDX 0
                   :EIP (+ 852 (SNPT-CODE-LOCATION))
                   :ESI (+ (* 8 LOOP-COUNTER)
                           (R32 (+ 4 (G :ESP S)) S))
                   :ESP (+ -28 (G :ESP S))
                   :F-CF cf
                   :F-OF of
                   :F-SF sf
                   :F-ZF zf
                   :IMME1 imme1
                   :VALU1 valu1
                   (UPDATE-MEM (+ -4 (G :ESP S))
                               (G :EBP S)

                               (+ -8 (G :ESP S))
                               (G :ESI S)

                               (+ -12 (G :ESP S))
                               (G :EBX S)

                               (+ -16 (G :ESP S))
                               0

                               (+ -20 (G :ESP S))
                               1

                               (+ -24 (G :ESP S))
                               (+ 1 loop-counter)

                               (init_pdpt-modify-loop-1 loop-counter S))))))

(defun init_pdpt-modify (s)
  (let ((loop-counter 3))
    (UPDATE-REGS :EAX (LOGIOR 1
                              (R32 (+ (* 4 LOOP-COUNTER)
                                      (R32 (+ 8 (G :ESP S)) S))
                                   S))
                 :EBP (G :EBP S)
                 :EBX (G :EBX S)
                 :ECX (R32 (+ (* 4 LOOP-COUNTER)
                              (R32 (+ 8 (G :ESP S)) S))
                           S)
                 :EDX 0
                 :EIP (R32 (G :ESP S) S)
                 :ESI (G :ESI S)
                 :ESP (+ 4 (G :ESP S))
                 :F-CF (CF (+ -12 (G :ESP S))
                           (+ -12 (G :ESP S)))
                 :F-OF (OF (N32-TO-I32 (+ -12 (G :ESP S)))
                           (+ 16 (N32-TO-I32 (+ -28 (G :ESP S)))))
                 :F-SF (SF (N32-TO-I32 (+ -12 (G :ESP S))))
                 :F-ZF (ZF (+ -12 (G :ESP S)))
                 :IMME1 16
                 :VALU1 (+ 1 LOOP-COUNTER)
                 (UPDATE-MEM (+ -4 (G :ESP S))
                             (G :EBP S)

                             (+ -8 (G :ESP S))
                             (G :ESI S)

                             (+ -12 (G :ESP S))
                             (G :EBX S)

                             (+ -16 (G :ESP S))
                             0

                             (+ -20 (G :ESP S))
                             1

                             (+ -24 (G :ESP S))
                             (+ 1 LOOP-COUNTER)

                             (init_pdpt-modify-loop-1 loop-counter S)))))

;;; qwerty
;;; These are the theorems we want about init_pdpt-modify
(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm |(paging-p (init_pdpt-modify s))|
   (equal (paging-p (init_pdpt-modify s))
          (paging-p s)))

 (defthm |(va-to-pa addr (init_pdpt-modify s))|
   (implies (not (paging-p s))
            (equal (va-to-pa addr (init_pdpt-modify s))
                   (va-to-pa addr s))))

 (defthm |(good-32-address-p addr (init_pdpt-modify s))|
   (implies (not (paging-p s))
            (equal (good-32-address-p addr (init_pdpt-modify s))
                   (good-32-address-p addr s)))
   :hints (("Goal" :in-theory (enable good-32-address-p))))

 (local
  (defthm |(G field (INIT_PDPT-MODIFY-loop-1 i s))|
    (implies (not (equal field :mem))
             (equal (G field (INIT_PDPT-MODIFY-loop-1 i s))
                    (g field s)))))

 (defthm |(y86-p (init_pdpt-modify s))|
   (implies (init_pdpt-pre s)
            (y86-p (init_pdpt-modify s)))
   :hints (("Goal" :in-theory (enable y86-p
                                      Y86-REGISTER-GUARD
                                      Y86-SUPERVISOR-GUARD
                                      Y86-FLAGS-GUARD
                                      Y86-MISC-GUARD
                                      ))))

 (defthm |(memoryp (g :mem (init_pdpt-modify s)))|
   (implies (init_pdpt-pre s)
            (memoryp (g :mem (init_pdpt-modify s)))))

 (defthm |(good-state-p (init_pdpt-modify s))|
   (implies (init_pdpt-pre s)
            (good-state-p (init_pdpt-modify s))))

 (defthm |(g :cr0 (init_pdpt-modify s))|
   (implies (init_pdpt-pre s)
            (equal (g :cr0 (init_pdpt-modify s))
                   (G :cr0 s))))

 (defthm |(g :eip (init_pdpt-modify s))|
   (implies (init_pdpt-pre s)
            (equal (g :eip (init_pdpt-modify s))
                   (R32 (G :ESP S) S))))

 (defthm |(g :ebp (init_pdpt-modify s))|
   (implies (init_pdpt-pre s)
            (equal (g :ebp (init_pdpt-modify s))
                   (G :EBP S))))

 (defthm |(g :esp (init_pdpt-modify s))|
   (implies (init_pdpt-pre s)
            (equal (g :esp (init_pdpt-modify s))
                   (+ 4 (G :ESP S)))))

 (defthm |(r32 addr (init_pdpt-modify s))|
   (implies (and (init_pdpt-pre s)
                 (n32p addr)
                 (n32p (+ 3 addr))
                 (disjointp (list (range addr 0 4)
                                  (range (g :esp s) -24 24)
                                  (range (r32 (+ 4 (g :esp s)) s) 0 (* 4 8)))))
            (equal (r32 addr (init_pdpt-modify s))
                   (r32 addr s))))

 (defthm |(r32 addr (init_pdpt-modify s)) --- written to 1|
   (implies (and (init_pdpt-pre s)

                 (integerp i)
                 (<= 0 i)
                 (<= i 3))
            (equal (r32 (+ (* 8 i)
                           (R32 (+ 4 (G :ESP S)) S))
                        (init_pdpt-modify s))
                   (LOGIOR 1
                           (R32 (+ (* 4 i)
                                   (R32 (+ 8 (G :ESP S)) S))
                                S)))))

 (defthm |(r32 addr (init_pdpt-modify s)) --- written to 2|
   (implies (and (init_pdpt-pre s)

                 (integerp i)
                 (<= 0 i)
                 (<= i 3))
            (equal (r32 (+ 4
                           (* 8 i)
                           (R32 (+ 4 (G :ESP S)) S))
                        (init_pdpt-modify s))
                   0)))
 )

(defun init_pdpt-assertion (s0 s1)
  (cond ((not (in-sub s1))
         ;; exit
         (equal s1 (init_pdpt-modify s0)))
        ((equal (g :eip s1)
                (+ *INIT_PDPT* (snpt-code-location)))
         ;; start
         (and (init_pdpt-pre s1)
              (equal s1 s0)))
        ((equal (g :eip s1)
                (+ *L15* (snpt-code-location)))
         ;; loop
         (and (init_pdpt-pre s0)
              (init_pdpt-loop-pre s1)
              (let ((loop-counter (r32 (+ -20 (g :ebp s1)) s1))
                    (cf (g :f-cf s1))
                    (of (g :f-of s1))
                    (sf (g :f-sf s1))
                    (zf (g :f-zf s1))
                    (imme1 (g :imme1 s1))
                    (valu1 (g :valu1 s1)))
                (equal s1 (init_pdpt-modify-loop loop-counter cf of sf zf imme1 valu1 s0)))))
        (t
         'NIL)))

(ENCAPSULATE
 NIL
 (LOCAL (DEFTHEORY USER-THEORY (CURRENT-THEORY :HERE)))
 (LOCAL
  (ENCAPSULATE
   NIL
   (LOCAL (DEFTHEORY $$$SUBTHEORY (CURRENT-THEORY :HERE)))
   (LOCAL (IN-THEORY (THEORY 'GROUND-ZERO)))
   (DEFUN-NX $$$INSUB (S1)
     (DECLARE (XARGS :NORMALIZE NIL))
     NIL)
   (DEFUN-NX $$$PRESUB (S1) NIL)
   (DEFUN-NX $$$MODIFYSUB (S1)
     (DECLARE (XARGS :NORMALIZE NIL))
     "Should never see this in a proof")
   (DEFTHM $$$NO-MAIN-CUTPOINT-IN-SUB
     (IMPLIES ($$$INSUB S1)
              (NOT (INIT_PDPT-CUTPOINT-P S1)))
     :RULE-CLASSES NIL)
   (DEFTHM $$$IN-SUB-IMPLIES-IN-MAIN
     (IMPLIES ($$$INSUB S1)
              (IN-SUB S1))
     :RULE-CLASSES NIL)
   (DEFTHM $$$PRESUB-IMPLIES-INSUB
     (IMPLIES ($$$PRESUB S1) ($$$INSUB S1))
     :RULE-CLASSES NIL)
   (DEFP $$$STEPS-TO-EXITPOINT-SUB-TAIL (S1 I)
     (IF (NOT ($$$INSUB S1))
         I
         (LET* ((S1 (Y86-STEP S1)))
               ($$$STEPS-TO-EXITPOINT-SUB-TAIL S1 (1+ I)))))
   (DEFUN-NX $$$STEPS-TO-EXITPOINT-SUB (S1)
     (DECLARE (XARGS :NORMALIZE NIL))
     (LET* ((STEPS ($$$STEPS-TO-EXITPOINT-SUB-TAIL S1 0))
            (S1 (Y86 S1 STEPS)))
           (IF (NOT ($$$INSUB S1)) STEPS (OMEGA))))
   (DEFUN-NX $$$NEXT-EXITPOINT-SUB (S1)
     (Y86 S1 ($$$STEPS-TO-EXITPOINT-SUB S1)))
   (DEFUN-SK $$$EXISTS-EXITPOINT-SUB (S1)
     (DECLARE (XARGS :NORMALIZE NIL))
     (EXISTS N
             (LET* ((S1 (Y86 S1 N)))
                   (NOT ($$$INSUB S1)))))
   (DEFTHM $$$CORRECTNESS-OF-SUB
     (IMPLIES (AND ($$$PRESUB S1)
                   ($$$EXISTS-EXITPOINT-SUB S1))
              (AND (LET* ((S1 ($$$NEXT-EXITPOINT-SUB S1)))
                         (NOT ($$$INSUB S1)))
                   (EQUAL ($$$NEXT-EXITPOINT-SUB S1)
                          ($$$MODIFYSUB S1))))
     :RULE-CLASSES NIL)
   (LOCAL (IN-THEORY (THEORY 'GROUND-ZERO)))
   (DEFP $$$NEXT-CUTPOINT-MAIN (S1)
     (IF (OR (INIT_PDPT-CUTPOINT-P S1)
             (NOT (IN-SUB S1)))
         S1
         (LET* ((S1 (IF ($$$PRESUB S1)
                        ($$$MODIFYSUB S1)
                        (Y86-STEP S1))))
               ($$$NEXT-CUTPOINT-MAIN S1))))

;;; adding this hypothesis allowed me to control the opening up of
;;; $$$NEXT-CUTPOINT-MAIN.  Without this, I got rewrite-stack
;;; overflows.

   (DEFTHM $$$DEFP-SYMSIM-THEOREM
     (implies (syntaxp (not (equal (fn-symb s1)
                                   'y86-step)))
              (EQUAL ($$$NEXT-CUTPOINT-MAIN S1)
                     (IF (OR (INIT_PDPT-CUTPOINT-P S1)
                             (NOT (IN-SUB S1)))
                         S1
                         (LET* ((S1 (Y86-STEP S1)))
                               ($$$NEXT-CUTPOINT-MAIN S1)))))
     :HINTS (("Goal" :IN-THEORY (ENABLE $$$PRESUB $$$MODIFYSUB))))))
 (LOCAL (DEFTHM $$$PRE-IMPLIES-ASSERTION
          (IMPLIES (INIT_PDPT-PRE S1)
                   (LET ((S0 S1))
                        (INIT_PDPT-ASSERTION S0 S1)))
          :RULE-CLASSES NIL))
 (LOCAL (DEFTHM $$$ASSERTION-MAIN-IMPLIES-POST
          (IMPLIES (AND (INIT_PDPT-ASSERTION S0 S1)
                        (NOT (IN-SUB S1)))
                   (EQUAL S1
                          (LET ((S1 S0)) (INIT_PDPT-MODIFY S1))))
          :RULE-CLASSES NIL))
 (LOCAL (DEFTHM $$$ASSERTION-IMPLIES-CUTPOINT
          (IMPLIES (INIT_PDPT-ASSERTION S0 S1)
                   (OR (INIT_PDPT-CUTPOINT-P S1)
                       (NOT (IN-SUB S1))))
          :RULE-CLASSES NIL))
 (LOCAL (IN-THEORY (THEORY 'GROUND-ZERO)))
 (LOCAL (DEFUN-SK $$$EXISTS-NEXT-CUTPOINT (S1)
          (EXISTS N
                  (LET* ((S1 (Y86 S1 N)))
                        (INIT_PDPT-CUTPOINT-P S1)))))
 (LOCAL (IN-THEORY (UNION-THEORIES (THEORY 'USER-THEORY)
                                   (LIST '$$$DEFP-SYMSIM-THEOREM))))

;;; $$$ASSERTION-INVARIANT-OVER-CUTPOINTS uses $$$NEXT-CUTPOINT-MAIN
;;; in too many places and too amny subgoals.  If I allowed the
;;; expansion to occur there, things exploded.  So I do it once here.

;;; The cond in the hyp's is just main-assertion, with the equalities
;;; replaced with t.

 (local (include-book "arithmetic-5/top" :dir :system))

 (local
  (in-theory (disable $$$DEFP-SYMSIM-THEOREM)))

 (local
  (defun simulation-default-hint (stable-under-simplificationp clause)
    (if stable-under-simplificationp
        (let ((concl (car (last clause))))
          (cond ((and (equal (fn-symb concl) 'EQUAL)
                      (equal (fn-symb (arg1 concl)) '$$$NEXT-CUTPOINT-MAIN)
                      (not (equal (fn-symb (arg1 (arg1 concl))) 'Y86-STEP)))
                 `(:computed-hint-replacement t
                                              :expand (,(arg1 concl))))
                ((and (equal (fn-symb concl) 'EQUAL)
                      (equal (fn-symb (arg2 concl)) '$$$NEXT-CUTPOINT-MAIN)
                      (not (equal (fn-symb (arg1 (arg2 concl))) 'Y86-STEP)))
                 `(:computed-hint-replacement t
                                              :expand (,(arg2 concl))))
                (t
                 nil)))
      nil)))

 (local
  (set-default-hints '((simulation-default-hint stable-under-simplificationp clause))))

 (local
  (in-theory (enable n32+ n32)))

 (local
  (in-theory (disable cf zf sf of
                      subl-cf
                      sall-cf sall-of
                      shrl-cf shrl-of
                      unpack)))




 (local
  (defthm simulate-main
    (implies (and (cond ((not (in-sub s1))
                         ;; exit
                         t)
                        ((equal (g :eip s1)
                                (+ *INIT_PDPT* (snpt-code-location)))
                         ;; start
                         (and (init_pdpt-pre s1)
                              t))
                        ((equal (g :eip s1)
                                (+ *L15* (snpt-code-location)))
                         ;; loop
                         (and t
                              (init_pdpt-loop-pre s1)
                              t))
                        (t
                         'NIL))
                  (in-sub s1))
             (equal ($$$NEXT-CUTPOINT-MAIN (Y86-STEP S1))
                    (cond ((not (in-sub s1))
                           ;; exit
                           t)
                          ((equal (g :eip s1)
                                  (+ *INIT_PDPT* (snpt-code-location)))
                           ;; start
                           (UPDATE-REGS :EBP (+ -4 (G :ESP S1))
                                        :EIP (+ 852 (SNPT-CODE-LOCATION))
                                        :ESP (+ -28 (G :ESP S1))
                                        :F-CF (SUBL-CF 16 (+ -12 (G :ESP S1)))
                                        :F-OF (OF (N32-TO-I32 (+ -28 (G :ESP S1)))
                                                  (+ -16 (N32-TO-I32 (+ -12 (G :ESP S1)))))
                                        :F-SF (SF (N32-TO-I32 (+ -28 (G :ESP S1))))
                                        :F-ZF (ZF (+ -28 (G :ESP S1)))
                                        :IMME1 0
                                        :VALU1 16
                                        (UPDATE-MEM (+ -4 (G :ESP S1)) (G :EBP S1)
                                                    (+ -8 (G :ESP S1)) (G :ESI S1)
                                                    (+ -12 (G :ESP S1)) (G :EBX S1)
                                                    ;; 64-bit page present
                                                    (+ -16 (G :ESP S1)) 0
                                                    (+ -20 (G :ESP S1)) 1
                                                    ;; i --- loop counter
                                                    (+ -24 (G :ESP S1)) 0
                                                    S1)))
                          ((and (equal (g :eip s1)
                                       (+ *L15* (snpt-code-location)))
                                (<= (R32 (+ -20 (G :EBP S1)) S1) 3))
                           ;; stay in loop
                           (UPDATE-REGS
                            :EAX
                            (LOGIOR (R32 (+ -16 (G :EBP S1)) S1)
                                    (R32 (+ (R32 (+ 12 (G :EBP S1)) S1)
                                            (* 4 (R32 (+ -20 (G :EBP S1)) S1)))
                                         S1))
                            :EBX 0 :ECX
                            (R32 (+ (R32 (+ 12 (G :EBP S1)) S1)
                                    (* 4 (R32 (+ -20 (G :EBP S1)) S1)))
                                 S1)
                            :EDX (R32 (+ -12 (G :EBP S1)) S1)
                            :EIP (+ 852 (SNPT-CODE-LOCATION))
                            :ESI
                            (+ (R32 (+ 8 (G :EBP S1)) S1)
                               (* 8 (R32 (+ -20 (G :EBP S1)) S1)))
                            :F-CF
                            (CF (+ 1 (R32 (+ -20 (G :EBP S1)) S1))
                                (+ 1 (R32 (+ -20 (G :EBP S1)) S1)))
                            :F-OF
                            (OF (N32-TO-I32 (+ 1 (R32 (+ -20 (G :EBP S1)) S1)))
                                (+ 1 (R32 (+ -20 (G :EBP S1)) S1)))
                            :F-SF
                            (SF (N32-TO-I32 (+ 1 (R32 (+ -20 (G :EBP S1)) S1))))
                            :F-ZF
                            (ZF (+ 1 (R32 (+ -20 (G :EBP S1)) S1)))
                            :IMME1 1 :VALU1
                            (+ 1 (R32 (+ -20 (G :EBP S1)) S1))
                            (UPDATE-MEM ;; i --- loop counter
                             (+ -20 (G :EBP S1))
                             (+ 1 (R32 (+ -20 (G :EBP S1)) S1))

                             (+ 4 (R32 (+ 8 (G :EBP S1)) S1)
                                (* 8 (R32 (+ -20 (G :EBP S1)) S1)))
                             (R32 (+ -12 (G :EBP S1)) S1)

                             (+ (R32 (+ 8 (G :EBP S1)) S1)
                                (* 8 (R32 (+ -20 (G :EBP S1)) S1)))
                             (LOGIOR (R32 (+ -16 (G :EBP S1)) S1)
                                     (R32 (+ (R32 (+ 12 (G :EBP S1)) S1)
                                             (* 4 (R32 (+ -20 (G :EBP S1)) S1)))
                                          S1))

                             S1)))
                          ((and (equal (g :eip s1)
                                       (+ *L15* (snpt-code-location)))
                                (< 3 (R32 (+ -20 (G :EBP S1)) S1)))
                           ;; exit loop
                           (UPDATE-REGS :EBP (R32 (G :EBP S1) S1)
                                        :EBX (R32 (+ 16 (G :ESP S1)) S1)
                                        :EIP (R32 (+ 4 (G :EBP S1)) S1)
                                        :ESI (R32 (+ 20 (G :ESP S1)) S1)
                                        :ESP (+ 8 (G :EBP S1))
                                        :F-CF
                                        (CF (+ 16 (G :ESP S1))
                                            (+ 16 (G :ESP S1)))
                                        :F-OF
                                        (OF (N32-TO-I32 (+ 16 (G :ESP S1)))
                                            (+ 16 (N32-TO-I32 (G :ESP S1))))
                                        :F-SF
                                        (SF (N32-TO-I32 (+ 16 (G :ESP S1))))
                                        :F-ZF (ZF (+ 16 (G :ESP S1)))
                                        :IMME1
                                        16 :VALU1 (R32 (+ -20 (G :EBP S1)) S1)
                                        S1))
                          (t
                           'NIL))))
    :hints (("Goal" :in-theory (disable MOD-BOUNDS-1
                                        N32+-WHEN-WORD-ALIGNED
                                        |(word-aligned-p x)|
                                        INIT_PDTS-LOADED-THM-32
                                        CREATE_NESTED_PT-LOADED-THM-32
                                        SEC_NOT_PRESENT-LOADED-THM-32
                                        |(mod (+ x y) z) where (<= 0 z)|
                                        CANCEL-MOD-+
                                        )
             :do-not '(generalize eliminate-destructors fertilize)))
    :otf-flg t))

 (local
  (set-default-hints nil))

 (local
  (in-theory (disable |(y86-step st)|
                      |(logior 1 x)|)))

;;; !!! messy
 (local
  (defun assertion-invariant-default-hint-1 (hyps)
    (cond ((endp hyps)
           (mv nil nil))                ; should be error
          ((and (equal (fn-symb (car hyps)) 'NOT)
                (equal (fn-symb (arg1 (car hyps))) 'EQUAL)
                (equal (fn-symb (arg1 (arg1 (car hyps)))) 'S)
                (equal (arg2 (arg1 (car hyps))) 'S1))
           (mv (cdr hyps) (arg1 (arg1 (car hyps)))))
          ((and (equal (fn-symb (car hyps)) 'NOT)
                (equal (fn-symb (arg1 (car hyps))) 'EQUAL)
                (equal (fn-symb (arg2 (arg1 (car hyps)))) 'S)
                (equal (arg1 (arg1 (car hyps))) 'S1))
           (mv (cdr hyps) (arg2 (arg1 (car hyps)))))
          (t
           (mv-let (new-hyps s1-subst)
                   (assertion-invariant-default-hint-1 (cdr hyps))
                   (mv (cons (car hyps) new-hyps)
                       s1-subst))))))

;;; maybe give minimal-theory hint on orig-goal implies instance
;;; maybe construct instance on own dime, rather than use
;;; prettyify-clause --- no need to untranslate.
;;; maybe use subst on concl (or whole goal), rather than use lambda
 (local
  (defun assertion-invariant-default-hint (stable-under-simplificationp clause world)
    (declare (xargs :mode :program))
    (if stable-under-simplificationp
        (b* ((concl (car (last clause)))
             ((mv new-hyps s1-subst)
              (assertion-invariant-default-hint-1 (butlast clause 1)))
             (concl-vars (all-vars concl))
             (new-concl `((LAMBDA ,concl-vars ,concl) ,@(subst s1-subst 's1 concl-vars)))
             (instance (prettyify-clause (append new-hyps
                                                 (list new-concl))
                                         nil world)))
            `(:use ((:instance
                     (:theorem ,instance)))
                   :expand ((INIT_PDPT-MODIFY-LOOP-1 (R32 (+ -20 (G :EBP S1)) S1)
                                                     S0))))
      nil)))


 (local
  (set-default-hints '((assertion-invariant-default-hint stable-under-simplificationp
                                                         clause
                                                         world))))


;;; This has gotten much slower (it was still slow before) now that I
;;; tightened up the constants in the ranges required to be disjoint,
;;; and the constants in the (n32p ...) hypotheses.
 (LOCAL (DEFTHM $$$ASSERTION-INVARIANT-OVER-CUTPOINTS
          (IMPLIES (AND (INIT_PDPT-ASSERTION S0 S1)
                        (IN-SUB S1)
                        (LET* ((S1 (Y86 S1 N)))
                              (NOT (IN-SUB S1))))
                   (LET* ((S1 (Y86-STEP S1))
                          (S1 ($$$NEXT-CUTPOINT-MAIN S1)))
                         (INIT_PDPT-ASSERTION S0 S1)))
          :RULE-CLASSES NIL
          :HINTS (("Goal" :in-theory (disable INIT_PDTS-LOADED-THM-32
                                              INIT_PDPT-LOADED-THM-32
                                              CREATE_NESTED_PT-LOADED-THM-32
                                              SEC_NOT_PRESENT-LOADED-THM-32)
                   :do-not '(generalize eliminate-destructors fertilize)))
          :otf-flg t))

 (local
  (set-default-hints nil))

 (LOCAL (IN-THEORY (THEORY 'GROUND-ZERO)))
 (DEFP EXITSTEPS-TAIL (S1 I)
   (IF (NOT (IN-SUB S1))
       I
       (LET* ((S1 (Y86-STEP S1)))
             (EXITSTEPS-TAIL S1 (1+ I)))))
 (DEFUN EXITSTEPS (S1)
   (LET* ((STEPS (EXITSTEPS-TAIL S1 0))
          (S1 (Y86 S1 STEPS)))
         (IF (NOT (IN-SUB S1))
             STEPS (OMEGA))))
 (DEFUN-SK EXISTS-NEXT-EXITPOINT (S1)
   (EXISTS N
           (LET* ((S1 (Y86 S1 N)))
                 (NOT (IN-SUB S1)))))
 (DEFUN NEXT-EXITPOINT (S1)
   (LET* ((STEPS (EXITSTEPS S1)))
         (Y86 S1 STEPS)))
 (LOCAL (IN-THEORY (THEORY 'MINIMAL-THEORY)))

 (DEFTHM
   INIT_PDPT-CORRECT
   (IMPLIES (AND (INIT_PDPT-PRE S1)
                 (EXISTS-NEXT-EXITPOINT S1))
            (AND (LET ((S1 (NEXT-EXITPOINT S1)))
                      (NOT (IN-SUB S1)))
                 (EQUAL (NEXT-EXITPOINT S1)
                        (INIT_PDPT-MODIFY S1))))
   :OTF-FLG T
   :RULE-CLASSES NIL
   :HINTS
   (("Goal"
     :USE
     ((:INSTANCE
       (:FUNCTIONAL-INSTANCE
        |epc composite partial correctness|
        (EPC-NEXT (LAMBDA (S)
                          (LET ((S1 S)) (Y86-STEP S1))))
        (EPC-RUN (LAMBDA (S N) (Y86 S N)))
        (EXISTS-EPC-NEXT-CUTPOINT
         (LAMBDA (S)
                 (LET ((S1 S))
                      ($$$EXISTS-NEXT-CUTPOINT S1))))
        (EXISTS-EPC-NEXT-CUTPOINT-WITNESS
         (LAMBDA (S)
                 (LET ((S1 S))
                      ($$$EXISTS-NEXT-CUTPOINT-WITNESS S1))))
        (EPC-PRE-SUB (LAMBDA (S)
                             (LET ((S1 S)) ($$$PRESUB S1))))
        (EPC-IN-SUB (LAMBDA (S)
                            (LET ((S1 S)) ($$$INSUB S1))))
        (EPC-EXISTS-EXITPOINT-SUB
         (LAMBDA (S)
                 (LET ((S1 S))
                      ($$$EXISTS-EXITPOINT-SUB S1))))
        (EPC-EXISTS-EXITPOINT-SUB-WITNESS
         (LAMBDA (S)
                 (LET ((S1 S))
                      ($$$EXISTS-EXITPOINT-SUB-WITNESS S1))))
        (EPC-STEPS-TO-EXITPOINT-TAIL-SUB
         (LAMBDA (S I)
                 (LET ((S1 S))
                      ($$$STEPS-TO-EXITPOINT-SUB-TAIL S1 I))))
        (EPC-MODIFY-SUB (LAMBDA (S)
                                (LET ((S1 S)) ($$$MODIFYSUB S1))))
        (EPC-NEXT-EXITPOINT-SUB (LAMBDA (S)
                                        (LET ((S1 S))
                                             ($$$NEXT-EXITPOINT-SUB S1))))
        (EPC-STEPS-TO-EXITPOINT-SUB
         (LAMBDA (S)
                 (LET ((S1 S))
                      ($$$STEPS-TO-EXITPOINT-SUB S1))))
        (EPC-PRE-MAIN (LAMBDA (S)
                              (LET ((S1 S)) (INIT_PDPT-PRE S1))))
        (EPC-CUTPOINT-MAIN (LAMBDA (S)
                                   (LET ((S1 S))
                                        (INIT_PDPT-CUTPOINT-P S1))))
        (EPC-EXISTS-EXITPOINT-MAIN
         (LAMBDA (S)
                 (LET ((S1 S))
                      (EXISTS-NEXT-EXITPOINT S1))))
        (EPC-EXISTS-EXITPOINT-MAIN-WITNESS
         (LAMBDA (S)
                 (LET ((S1 S))
                      (EXISTS-NEXT-EXITPOINT-WITNESS S1))))
        (EPC-NEXT-EXITPOINT-MAIN
         (LAMBDA (S)
                 (LET ((S1 S)) (NEXT-EXITPOINT S1))))
        (EPC-EXITSTEPS-MAIN (LAMBDA (S)
                                    (LET ((S1 S)) (EXITSTEPS S1))))
        (EPC-EXITSTEPS-MAIN-TAIL
         (LAMBDA (S I)
                 (LET ((S1 S)) (EXITSTEPS-TAIL S1 I))))
        (EPC-IN-MAIN (LAMBDA (S)
                             (LET ((S1 S)) (IN-SUB S1))))
        (EPC-NEXT-EPC-CUTPOINT-MAIN
         (LAMBDA (S)
                 (LET ((S1 S))
                      ($$$NEXT-CUTPOINT-MAIN S1))))
        (EPC-ASSERTION-MAIN (LAMBDA (S0 S)
                                    (LET ((S0 S0) (S1 S))
                                         (INIT_PDPT-ASSERTION S0 S1))))
        (EPC-MODIFY-MAIN (LAMBDA (S)
                                 (LET ((S1 S)) (INIT_PDPT-MODIFY S1)))))
       (S S1))))
    ("Subgoal 22" :USE ((:INSTANCE $$$ASSERTION-INVARIANT-OVER-CUTPOINTS
                                   (S0 S0)
                                   (S1 S))))
    ("Subgoal 21" :USE ((:INSTANCE $$$ASSERTION-MAIN-IMPLIES-POST (S0 S0)
                                   (S1 S))))
    ("Subgoal 20" :USE ((:INSTANCE $$$PRE-IMPLIES-ASSERTION (S1 S))))
    ("Subgoal 19" :USE ((:INSTANCE $$$ASSERTION-IMPLIES-CUTPOINT (S0 S0)
                                   (S1 S))))
    ("Subgoal 18" :USE ((:INSTANCE $$$PRESUB-IMPLIES-INSUB (S1 S))))
    ("Subgoal 17" :USE ((:INSTANCE $$$IN-SUB-IMPLIES-IN-MAIN (S1 S))))
    ("Subgoal 16" :USE ((:INSTANCE $$$NO-MAIN-CUTPOINT-IN-SUB (S1 S))))
    ("Subgoal 15" :USE ((:INSTANCE (:DEFINITION $$$EXISTS-NEXT-CUTPOINT)
                                   (S1 S))))
    ("Subgoal 14" :USE ((:INSTANCE $$$EXISTS-NEXT-CUTPOINT-SUFF (S1 S))))
    ("Subgoal 13" :USE ((:INSTANCE $$$NEXT-CUTPOINT-MAIN$DEF (S1 S))))
    ("Subgoal 12" :USE ((:INSTANCE $$$CORRECTNESS-OF-SUB (S1 S))))
    ("Subgoal 11" :USE ((:INSTANCE $$$STEPS-TO-EXITPOINT-SUB-TAIL$DEF
                                   (S1 S))))
    ("Subgoal 10" :USE ((:INSTANCE (:DEFINITION $$$EXISTS-EXITPOINT-SUB)
                                   (S1 S))))
    ("Subgoal 9" :USE ((:INSTANCE $$$EXISTS-EXITPOINT-SUB-SUFF (S1 S))))
    ("Subgoal 8" :USE ((:INSTANCE (:DEFINITION $$$NEXT-EXITPOINT-SUB)
                                  (S1 S))))
    ("Subgoal 7" :USE ((:INSTANCE (:DEFINITION $$$STEPS-TO-EXITPOINT-SUB)
                                  (S1 S))))
    ("Subgoal 6" :IN-THEORY (ENABLE Y86))
    ("Subgoal 5" :USE ((:INSTANCE (:DEFINITION NEXT-EXITPOINT)
                                  (S1 S))))
    ("Subgoal 4" :USE ((:INSTANCE (:DEFINITION EXITSTEPS)
                                  (S1 S))))
    ("Subgoal 3" :USE ((:INSTANCE EXITSTEPS-TAIL$DEF (S1 S))))
    ("Subgoal 2" :USE ((:INSTANCE EXISTS-NEXT-EXITPOINT-SUFF (S1 S))))
    ("Subgoal 1" :USE ((:INSTANCE (:DEFINITION EXISTS-NEXT-EXITPOINT)
                                  (S1 S))))))
 )

#||
(defsimulate+
  y86-step
  :run y86
  :inmain in-sub
  :cutpoint init_pdpt-cutpoint-p
  :assertion-params (s0 s1)
  :precondition init_pdpt-pre
  :assertion init_pdpt-assertion
  :modify init_pdpt-modify

  :exitsteps exitsteps
  :exists-next-exitpoint exists-next-exitpoint
  :next-exitpoint next-exitpoint

  :correctness-theorem init_pdpt-correct)
||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; init_pdts

;;; set up the four page descriptor tables

(defun in-init_pdts (s)
  (let ((eip (g :eip s)))
    (and (<= (+ *INIT_PDTS* (snpt-code-location)) eip)
         (< eip (+ *INIT_PDPT* (snpt-code-location))))))

;;; but we need to have only one in-sub for everything
;;; repeat from init_pdpt
(defun in-sub (s)
  (let ((eip (g :eip s)))
    (and (<= (+ *SEC_NOT_PRESENT* (snpt-code-location)) eip)
         (< eip (+ *CREATE_NESTED_PT* (snpt-code-location))))))

(defun init_pdts-cutpoint-p (s)
  (let ((eip (g :eip s)))
    (or (equal eip (+ *INIT_PDTS* (snpt-code-location))) ; start
        (equal eip (+ *L7* (snpt-code-location)))        ; outer loop test
        (equal eip (+ *L9* (snpt-code-location)))        ; inner loop test
        (not (in-sub s)))))                        ; exit

(defun init_pdts-pre (s)
  (and (good-state-p s)
       (equal (g :eip s) (+ *INIT_PDTS* (snpt-code-location)))
       (not (paging-p s))
       (disjointp
        (list (range (snpt-code-location) 0 993)                            ; code
              (range (g :esp s) -56 68)                                     ; stack
              (range (r32 (+ 4 (g :esp s)) s) 0 (* 4 4))                    ; pdt pointer array
              (range (r32 (r32 (+ 4 (g :esp s)) s) s) 0 (* 512 8))          ; ptd one
              (range (r32 (+ 4 (r32 (+ 4 (g :esp s)) s)) s) 0 (* 512 8))    ; pdt two
              (range (r32 (+ 8 (r32 (+ 4 (g :esp s)) s)) s) 0 (* 512 8))    ; pdt three
              (range (r32 (+ 12 (r32 (+ 4 (g :esp s)) s)) s) 0 (* 512 8)))) ; pdt four
       ;; all stack addresses are "good" --- the stack does not wrap around memory
       (n32p (+ -60 (g :esp s)))
       (n32p (+ 11 (g :esp s)))
       ;; addresses in pdt pointer array are "good"
       (n32p (+ 15 (r32 (+ 4 (g :esp s)) s)))
       ;; addresses in the pdt are "good"
       (n32p (+ 4095 (r32 (r32 (+ 4 (g :esp s)) s) s)))
       (n32p (+ 4095 (r32 (+ 4 (r32 (+ 4 (g :esp s)) s)) s)))
       (n32p (+ 4095 (r32 (+ 8 (r32 (+ 4 (g :esp s)) s)) s)))
       (n32p (+ 4095 (r32 (+ 12 (r32 (+ 4 (g :esp s)) s)) s)))
       ;; we return to create_nested_pt
       (< (+ *CREATE_NESTED_PT* (snpt-code-location)) (R32 (g :esp s) S))))

(defun init_pdts-outer-loop-pre (s)
  (and (good-state-p s)
       (equal (g :eip s) (+ *L7* (snpt-code-location)))
       (not (paging-p s))
       (disjointp
        (list (range (snpt-code-location) 0 993)                            ; code
              (range (+ 4 (g :ebp s)) -56 68)                                     ; stack
              (range (r32 (+ 4 (+ 4 (g :ebp s))) s) 0 (* 4 4))                    ; pdt pointer array
              (range (r32 (r32 (+ 4 (+ 4 (g :ebp s))) s) s) 0 (* 512 8))          ; ptd one
              (range (r32 (+ 4 (r32 (+ 4 (+ 4 (g :ebp s))) s)) s) 0 (* 512 8))    ; pdt two
              (range (r32 (+ 8 (r32 (+ 4 (+ 4 (g :ebp s))) s)) s) 0 (* 512 8))    ; pdt three
              (range (r32 (+ 12 (r32 (+ 4 (+ 4 (g :ebp s))) s)) s) 0 (* 512 8)))) ; pdt four
       ;; all stack addresses are "good" --- the stack does not wrap around memory
       (n32p (+ -60 (+ 4 (g :ebp s))))
       (n32p (+ 11 (+ 4 (g :ebp s))))
       ;; addresses in pdt pointer array are "good"
       (n32p (+ 15 (r32 (+ 4 (+ 4 (g :ebp s))) s)))
       ;; addresses in the pdt are "good"
       (n32p (+ 4095 (r32 (r32 (+ 4 (+ 4 (g :ebp s))) s) s)))
       (n32p (+ 4095 (r32 (+ 4 (r32 (+ 4 (+ 4 (g :ebp s))) s)) s)))
       (n32p (+ 4095 (r32 (+ 8 (r32 (+ 4 (+ 4 (g :ebp s))) s)) s)))
       (n32p (+ 4095 (r32 (+ 12 (r32 (+ 4 (+ 4 (g :ebp s))) s)) s)))
       ;; we return to create_nested_pt
       (< (+ *CREATE_NESTED_PT* (snpt-code-location)) (R32 (+ 4 (g :ebp s)) S))
       ;; the alignment of :esp and :ebp --- why do we need this?
       (equal (g :esp s) (+ -56 (g :ebp s)))
       ;; page_size_2m is set correctly
       (equal (R32 (+ -12 (G :EBP S)) S)
              0)
       (equal (R32 (+ -16 (G :EBP S)) S)
              2097152)
       ;; flags is set correctly
       (equal (R32 (+ -20 (G :EBP S)) S)
              0)
       (equal (R32 (+ -24 (G :EBP S)) S)
              231)
       ;; outer loop-counter, we are in the loop
       (<= (r32 (+ -32 (g :ebp s)) s) 4)
       ;; if we have returned to the outer loop test, the inner loop
       ;; must have kicked out, so j is 512
       (if (equal (r32 (+ -32 (g :ebp s)) s)
                  0)
           'T
         (equal (r32 (+ -28 (g :ebp s)) s)
                512))
       ;; the address we are writing into the pdt is correctly formed.
       ;; In particular, it fits into lower 32 bits of the pdt entry,
       ;; and we don't have to case split because of the adcl's carry
       ;; bit until the very end
       (equal (R32 (+ -44 (G :EBP S)) S)
              (if (equal (r32 (+ -32 (g :ebp s)) s)
                         4)
                  1
                0))
       (equal (R32 (+ -48 (G :EBP S)) S)
              (if (equal (r32 (+ -32 (g :ebp s)) s)
                         4)
                  0
                (* (* 512 (r32 (+ -32 (g :ebp s)) s))
                   2097152)))))

;;; The need for this case split below indicates a weakness in the
;;; current version of disjointp.  Perhaps it should be uniquep ---
;;; which declares that after flattening, all addresses are unique.
;;; This would allow the four pdt to be gathered up by a single
;;; function, and the use if some lemmatta to say when an address is a
;;; member of one of them.  Further lemmatta would be required to
;;; distinguish different addresses within the pdt.
(defun init_pdts-inner-loop-pre (s)
  (and (good-state-p s)
       (equal (g :eip s) (+ *L9* (snpt-code-location)))
       (not (paging-p s))
       (disjointp
        (list (range (snpt-code-location) 0 993)                            ; code
              (range (+ 4 (g :ebp s)) -56 68)                                     ; stack
              (range (r32 (+ 4 (+ 4 (g :ebp s))) s) 0 (* 4 4))                    ; pdt pointer array
              (range (r32 (r32 (+ 4 (+ 4 (g :ebp s))) s) s) 0 (* 512 8))          ; ptd one
              (range (r32 (+ 4 (r32 (+ 4 (+ 4 (g :ebp s))) s)) s) 0 (* 512 8))    ; pdt two
              (range (r32 (+ 8 (r32 (+ 4 (+ 4 (g :ebp s))) s)) s) 0 (* 512 8))    ; pdt three
              (range (r32 (+ 12 (r32 (+ 4 (+ 4 (g :ebp s))) s)) s) 0 (* 512 8)))) ; pdt four
       ;; all stack addresses are "good" --- the stack does not wrap around memory
       (n32p (+ -60 (+ 4 (g :ebp s))))
       (n32p (+ 11 (+ 4 (g :ebp s))))
       ;; addresses in pdt pointer array are "good"
       (n32p (+ 15 (r32 (+ 4 (+ 4 (g :ebp s))) s)))
       ;; addresses in the pdt are "good"
       (n32p (+ 4095 (r32 (r32 (+ 4 (+ 4 (g :ebp s))) s) s)))
       (n32p (+ 4095 (r32 (+ 4 (r32 (+ 4 (+ 4 (g :ebp s))) s)) s)))
       (n32p (+ 4095 (r32 (+ 8 (r32 (+ 4 (+ 4 (g :ebp s))) s)) s)))
       (n32p (+ 4095 (r32 (+ 12 (r32 (+ 4 (+ 4 (g :ebp s))) s)) s)))
       ;; we return to create_nested_pt
       (< (+ *CREATE_NESTED_PT* (snpt-code-location)) (R32 (+ 4 (g :ebp s)) S))
       ;; the alignment of :esp and :ebp --- why do we need this?
       (equal (g :esp s) (+ -56 (g :ebp s)))
       ;; page_size_2m is set correctly
       (equal (R32 (+ -12 (G :EBP S)) S)
              0)
       (equal (R32 (+ -16 (G :EBP S)) S)
              2097152)
       ;; flags is set correctly
       (equal (R32 (+ -20 (G :EBP S)) S)
              0)
       (equal (R32 (+ -24 (G :EBP S)) S)
              231)
       ;; inner loop-counter, we are in the loop
       (<= (r32 (+ -28 (g :ebp s)) s) 512)
       ;; induce a case split, so we know which pdt we are working on.
       ;; Without this, we cannot tell that, for instance, the code is
       ;; disjoint from the pdt we are writing into.
       (or (equal (r32 (+ -32 (g :ebp s)) s)
                  0)
           (equal (r32 (+ -32 (g :ebp s)) s)
                  1)
           (equal (r32 (+ -32 (g :ebp s)) s)
                  2)
           (equal (r32 (+ -32 (g :ebp s)) s)
                  3))
       ;; We have stuffed a pointer to a pdt into the the proper place
       ;; on the stack.
       (equal (r32 (+ -36 (G :EBP S)) s)
              (R32 (+ (R32 (+ 8 (G :EBP S)) S)
                      (* 4 (R32 (+ -32 (G :EBP S)) S)))
                   S))
       ;; the address we are writing into the pdt is correctly formed.
       ;; In particular, it fits into lower 32 bits of the pdt entry,
       ;; and we don't have to case split because of the adcl's carry
       ;; bit until the very end.
       (equal (R32 (+ -44 (G :EBP S)) S)
              (if (and (equal (r32 (+ -28 (g :ebp s)) s)
                              512)
                       (equal (r32 (+ -32 (g :ebp s)) s)
                              3))
                  1
                0))
       (equal (R32 (+ -48 (G :EBP S)) S)
              (if (and (equal (r32 (+ -28 (g :ebp s)) s)
                              512)
                       (equal (r32 (+ -32 (g :ebp s)) s)
                              3))
                  0
                (+ (* (* 512 (r32 (+ -32 (g :ebp s)) s))
                      2097152)
                   (* (r32 (+ -28 (g :ebp s)) s)
                      2097152))))))

(defun init_pdts-modify-inner-loop-1 (i j s)
  (if (zp j)
      (update-mem (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                          (* 4 i))
                       S)
                  (LOGIOR 231
                          (* 512 i 2097152))

                  (+ 4 (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                               (* 4 i))
                            S))
                  0

                  S)
    (update-mem (+ (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                           (* 4 i))
                        S)
                   (* 8 j))
                (LOGIOR 231
                        (+ (* 512 i 2097152)
                           (* 2097152 j)))

                (+ 4 (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                             (* 4 i))
                          S)
                   (* 8 j))
                0

                (init_pdts-modify-inner-loop-1 i (+ -1 j)
                                               s))))

(defthm |(paging-p (init_pdts-modify-inner-loop-1 i j s))|
  (equal (paging-p (init_pdts-modify-inner-loop-1 i j s))
         (paging-p s)))

(defthm |(va-to-pa addr (init_pdts-modify-inner-loop-1 i j s))|
  (implies (not (paging-p s))
           (equal (va-to-pa addr (init_pdts-modify-inner-loop-1 i j s))
                  (va-to-pa addr s))))

(defthm |(good-32-address-p addr (init_pdts-modify-inner-loop-1 i j s))|
  (implies (not (paging-p s))
           (equal (good-32-address-p addr (init_pdts-modify-inner-loop-1 i j s))
                  (good-32-address-p addr s)))
  :hints (("Goal" :in-theory (enable good-32-address-p))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

;;; Why didn't I need this for init_pdpt-modify-loop-1?

 (defthm |(G field (INIT_PDTS-MODIFY-INNER-LOOP-1 i j s))|
   (implies (not (equal field :mem))
            (equal (G field (INIT_PDTS-MODIFY-INNER-LOOP-1 i j s))
                   (g field s))))

 (defthm |(y86-p (init_pdts-modify-inner-loop-1 i j s))|
   (implies (and (y86-p s)
                 (integerp i)
                 (integerp j)
                 (<= 0 i)
                 ;; (<= i 3)
                 (<= 0 j)
                 ;; (<= j 511)
                 (n32p (+ (* 2097152 J)
                          (* 1073741824 I)))
                 (n32p (+ 7 (* 8 J)
                          (R32 (+ (* 4 I) (R32 (+ 4 (G :ESP S)) S))
                               S))))
            (y86-p (init_pdts-modify-inner-loop-1 i j s)))
   :hints (("Goal" :in-theory (enable y86-p
                                      Y86-REGISTER-GUARD
                                      Y86-SUPERVISOR-GUARD
                                      Y86-FLAGS-GUARD
                                      Y86-MISC-GUARD
                                      ))))

 (defthm |(memoryp (g :mem (init_pdts-modify-inner-loop-1 i j s)))|
   (implies (and (y86-p s)
                 (integerp i)
                 (integerp j)
                 (<= 0 i)
                 ;; (<= i 3)
                 (<= 0 j)
                 ;; (<= j 511)
                 (n32p (+ (* 2097152 J)
                          (* 1073741824 I)))
                 (n32p (+ 7 (* 8 J)
                          (R32 (+ (* 4 I) (R32 (+ 4 (G :ESP S)) S))
                               S))))
            (memoryp (g :mem (init_pdts-modify-inner-loop-1 i j s)))))



 (defthm |(good-state-p (init_pdts-modify-inner-loop-1 i j s))|
   (implies (and (good-state-p s)
                 (not (paging-p s))
                 (integerp i)
                 (integerp j)
                 (<= 0 i)
                 (<= i 3)
                 (<= 0 j)
                 (<= j 511)
                 (n32p (+ (* 2097152 J)
                          (* 1073741824 I)))
                 (n32p (+ 7 (* 8 J)
                          (R32 (+ (* 4 I) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (disjointp (list (range (snpt-code-location) 0 993)
                                 (range (R32 (+ 0 (R32 (+ 4 (G :ESP S)) S)) S) 0 4096)
                                 (range (R32 (+ 4 (R32 (+ 4 (G :ESP S)) S)) S) 0 4096)
                                 (range (R32 (+ 8 (R32 (+ 4 (G :ESP S)) S)) S) 0 4096)
                                 (range (R32 (+ 12 (R32 (+ 4 (G :ESP S)) S)) S) 0 4096)))
                 )
            (good-state-p (init_pdts-modify-inner-loop-1 i j s)))
   :hints (("Subgoal *1/6" :cases ((equal i 0)
                                   (equal i 1)
                                   (equal i 2)
                                   (equal i 3)))
           ("Subgoal *1/1" :cases ((equal i 0)
                                   (equal i 1)
                                   (equal i 2)
                                   (equal i 3)))))

 (defthm |(r32 addr (init_pdts-modify-inner-loop-1 i j s))|
   (implies (and (y86-p s)
                 (integerp i)
                 (integerp j)
                 (<= 0 i)
                 ;; (<= i 3)
                 (<= 0 j)
                 ;; (<= j 511)
                 (not (paging-p s))
                 ;; !!! This should subsume the next two
                 ;; (good-32-address-p addr s)
                 (n32p addr)
                 (n32p (+ 3 addr))
                 (n32p (+ (* 2097152 J)
                          (* 1073741824 I)))
                 (n32p (+ 7 (* 8 J)
                          (R32 (+ (* 4 I) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (disjointp (list (range addr 0 4)
                                  (range (R32 (+ (* 4 I) (R32 (+ 4 (G :ESP S)) S))
                                              S)
                                         0
                                         (+ 8 (* 8 j))))))
            (equal (r32 addr (init_pdts-modify-inner-loop-1 i j s))
                   (r32 addr s))))

 (defthm |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|
   (implies (and (y86-p s)
                 (integerp i)
                 (integerp j)
                 (<= 0 i)
                 ;; (<= i 3)
                 (<= 0 j)
                 ;; (<= j 511)
                 (n32p (+ (* 2097152 J)
                          (* 1073741824 I)))
                 (integerp j-prime)
                 (<= 0 j-prime)
                 (<= j-prime j)
                 (not (paging-p s))
                 (n32p (+ 7 (* 8 J)
                          (R32 (+ (* 4 I) (R32 (+ 4 (G :ESP S)) S))
                               S))))
            (equal (r32 (+ (* 8 j-prime)
                           (R32 (+ (* 4 i)
                                   (R32 (+ 4 (G :ESP S)) S))
                                S))
                        (init_pdts-modify-inner-loop-1 i j s))
                   (LOGIOR 231
                           (+ (* 512 I 2097152)
                              (* 2097152 J-PRIME)))))
   :hints (("Subgoal *1/7" :cases ((equal j j-prime)))))

 (defthm |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|
   (implies (and (y86-p s)
                 (integerp i)
                 (integerp j)
                 (<= 0 i)
                 ;; (<= i 3)
                 (<= 0 j)
                 ;; (<= j 511)
                 (n32p (+ (* 2097152 J)
                          (* 1073741824 I)))
                 (integerp j-prime)
                 (<= 0 j-prime)
                 (<= j-prime j)
                 (not (paging-p s))
                 (n32p (+ 7 (* 8 J)
                          (R32 (+ (* 4 I) (R32 (+ 4 (G :ESP S)) S))
                               S))))
            (equal (r32 (+ 4
                           (* 8 j-prime)
                           (R32 (+ (* 4 i)
                                   (R32 (+ 4 (G :ESP S)) S))
                                S))
                        (init_pdts-modify-inner-loop-1 i j s))
                   0))
   :hints (("Subgoal *1/7" :cases ((equal j j-prime)))))

;;; !!! Why so many more hyps than
;;; |(r32 addr (init_pdts-modify-inner-loop-1 i j s))|
;;; are they all relly needed?
 (defthm |(init_pdts-modify-inner-loop-1 i j (w32 addr val s))|
   (implies (and (y86-p s)
                 (integerp i)
                 (integerp j)
                 (<= 0 i)
                 ;; (<= i 3)
                 (<= 0 j)
                 ;; (<= j 511)
                 (n32p (+ (* 2097152 J)
                          (* 1073741824 I)))
                 (not (paging-p s))
                 ;; !!! This should subsume the next two
                 ;; (good-32-address-p addr s)
                 (n32p addr)
                 (n32p (+ 3 addr))
                 (n32p (+ 7 (G :ESP S)))
                 (n32p (+ 3 (* 4 I) (R32 (+ 4 (G :ESP S)) S)))
                 (n32p (+ 7 (* 8 J)
                          (R32 (+ (* 4 I) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (disjointp (list (range addr 0 4)
                                  (range (+ 4 (G :ESP S)) 0 4)
                                  (range (+ (* 4 I) (R32 (+ 4 (G :ESP S)) S)) 0 4)
                                  (range (R32 (+ (* 4 I) (R32 (+ 4 (G :ESP S)) S))
                                              S)
                                         0
                                         (+ 8 (* 8 j))))))
            (equal (init_pdts-modify-inner-loop-1 i j
                                                  (w32 addr val s))
                   (w32 addr val (init_pdts-modify-inner-loop-1 i j s)))))
 )

(defun init_pdts-modify-outer-loop-1 (i s)
  (if (zp i)
      (init_pdts-modify-inner-loop-1 i 511 s)
    (init_pdts-modify-inner-loop-1 i 511
                                   (init_pdts-modify-outer-loop-1 (+ -1 i) s))))

(defthm |(paging-p (init_pdts-modify-outer-loop-1 i s))|
  (equal (paging-p (init_pdts-modify-outer-loop-1 i s))
         (paging-p s)))

(defthm |(va-to-pa addr (init_pdts-modify-outer-loop-1 i s))|
  (implies (not (paging-p s))
           (equal (va-to-pa addr (init_pdts-modify-outer-loop-1 i s))
                  (va-to-pa addr s))))

(defthm |(good-32-address-p addr (init_pdts-modify-outer-loop-1 i s))|
  (implies (not (paging-p s))
           (equal (good-32-address-p addr (init_pdts-modify-outer-loop-1 i s))
                  (good-32-address-p addr s))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

;;; Why didn't I need this for init_pdpt-modify-loop-1?

 (defthm |(G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))|
   (implies (not (equal field :mem))
            (equal (G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))
                   (g field s))))

;;; Can this be done without the cases hint?
;;; Perhaps the disjoint library needs generalization?
 (defthm |(y86-p (init_pdts-modify-outer-loop-1 i s))|
   (implies (and (y86-p s)
                 (integerp i)
                 (<= 0 i)
                 (<= i 3)
                 (not (paging-p s))
                 ;; These next two hyps are needed because we write to
                 ;; them in the loop.  If I were to drop the
                 ;; rewuirement that all addresses be 32-bit, this
                 ;; would go away.  Simplification is good.
                 ;; (N32P (+ 4 (G :ESP S)))
                 (N32P (+ 7 (G :ESP S)))
                 ;; (N32P (+ 4 (R32 (+ 4 (G :ESP S)) S)))
                 (N32P (+ 15 (R32 (+ 4 (G :ESP S)) S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 0) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 1) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 2) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 3) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (disjointp (LIST (RANGE (+ 4 (G :ESP S)) 0 4)
                                  (RANGE (+ 4 (R32 (+ 4 (G :ESP S)) S))
                                         0 12)
                                  (RANGE (R32 (R32 (+ 4 (G :ESP S)) S) S)
                                         0 4096)
                                  (RANGE (R32 (+ 4 (R32 (+ 4 (G :ESP S)) S)) S)
                                         0 4096)
                                  (RANGE (R32 (+ 8 (R32 (+ 4 (G :ESP S)) S)) S)
                                         0 4096))))
            (y86-p (init_pdts-modify-outer-loop-1 i s)))
   :hints (("Goal" :cases ((equal i 0)
                           (equal i 1)
                           (equal i 2)
                           (equal i 3))
            :expand ((INIT_PDTS-MODIFY-OUTER-LOOP-1 1 S)
                     (INIT_PDTS-MODIFY-OUTER-LOOP-1 2 S)
                     (INIT_PDTS-MODIFY-OUTER-LOOP-1 3 S))))
   :otf-flg t)



 (defthm |(memoryp (g :mem (init_pdts-modify-outer-loop-1 i s)))|
   (implies (and (y86-p s)
                 (integerp i)
                 (<= 0 i)
                 (<= i 3)
                 (not (paging-p s))
                 ;; These next two hyps are needed because we write to
                 ;; them in the loop.  If I were to drop the
                 ;; rewuirement that all addresses be 32-bit, this
                 ;; would go away.  Simplification is good.
                 ;; (N32P (+ 4 (G :ESP S)))
                 (N32P (+ 7 (G :ESP S)))
                 ;; (N32P (+ 4 (R32 (+ 4 (G :ESP S)) S)))
                 (N32P (+ 15 (R32 (+ 4 (G :ESP S)) S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 0) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 1) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 2) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 3) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (disjointp (LIST (RANGE (+ 4 (G :ESP S)) 0 4)
                                  (RANGE (+ 4 (R32 (+ 4 (G :ESP S)) S))
                                         0 12)
                                  (RANGE (R32 (R32 (+ 4 (G :ESP S)) S) S)
                                         0 4096)
                                  (RANGE (R32 (+ 4 (R32 (+ 4 (G :ESP S)) S)) S)
                                         0 4096)
                                  (RANGE (R32 (+ 8 (R32 (+ 4 (G :ESP S)) S)) S)
                                         0 4096))))
            (memoryp (g :mem (init_pdts-modify-outer-loop-1 i s))))
   :hints (("Goal" :cases ((equal i 0)
                           (equal i 1)
                           (equal i 2)
                           (equal i 3))
            :expand ((INIT_PDTS-MODIFY-OUTER-LOOP-1 2 S)
                     (INIT_PDTS-MODIFY-OUTER-LOOP-1 3 S)))))


;;; !!! The ancestors-check gets in the way again

 (local
  (defun ancestors-check-disjointp-hack-2 (lit ancestors tokens)
    (declare (xargs :guard (and (pseudo-termp lit)
                                (ancestor-listp ancestors)
                                (true-listp tokens))))
    (cond ((memberp tokens '(((:REWRITE  |(r32 addr (init_pdts-modify-inner-loop-1 i j s))|))
                             ((:REWRITE |(init_pdts-modify-inner-loop-1 i j (w32 addr val s))|))
                             ((:REWRITE |(not (equal x y)) --- disjointp|))
                             ((:REWRITE DISJOINTP-ADDR-ADDR))
                             ((:REWRITE DISJOINTP-ADDR-RANGE))
                             ((:REWRITE DISJOINTP-RANGE-ADDR))
                             ((:REWRITE DISJOINTP-RANGE-RANGE))))
           (mv nil nil))
          ((atom ancestors)
           (mv nil nil))
          (t (mv-let (not-flg lit-atm)
                     (strip-not lit)
                     (declare (ignore not-flg))
                     (mv-let (var-cnt fn-cnt p-fn-cnt)
                             (var-fn-count lit-atm nil) ; Matt K. change from fn-count after v6-1
                             (ancestors-check1 lit-atm lit var-cnt fn-cnt p-fn-cnt
                                               ancestors tokens)))))))

 (local
  (defthm ancestors-check-disjointp-hack-constraint-2
    (mv-let (on-ancestors assumed-true)
            (ancestors-check-disjointp-hack-2 lit ancestors tokens)
            (implies (and on-ancestors
                          assumed-true)
                     (member-equal-mod-commuting lit (strip-ancestor-literals ancestors) nil)))
    :hints (("Goal" :use ancestors-check-builtin-property))
    :rule-classes nil))

 (local
  (defattach (ancestors-check ancestors-check-disjointp-hack-2)
    :system-ok t
    :hints (("Goal" :use ancestors-check-disjointp-hack-constraint-2))))


 (defthm |(r32 addr (init_pdts-modify-outer-loop-1 i s))|
   (implies (and (y86-p s)
                 (integerp i)
                 (<= 0 i)
                 (<= i 3)
                 (not (paging-p s))
                 ;; (good-32-address-p addr s)
                 (n32p addr)
                 (n32p (+ 3 addr))
                 ;; (N32P (+ 4 (G :ESP S)))
                 (N32P (+ 7 (G :ESP S)))
                 ;; (N32P (+ 4 (R32 (+ 4 (G :ESP S)) S)))
                 (N32P (+ 15 (R32 (+ 4 (G :ESP S)) S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 0) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 1) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 2) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 3) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (disjointp (LIST (RANGE ADDR 0 4)
                                  (RANGE (R32 (R32 (+ 4 (G :ESP S)) S) S)
                                         0 4096)
                                  (RANGE (R32 (+ 4 (R32 (+ 4 (G :ESP S)) S)) S)
                                         0 4096)
                                  (RANGE (R32 (+ 8 (R32 (+ 4 (G :ESP S)) S)) S)
                                         0 4096)
                                  (RANGE (R32 (+ 12 (R32 (+ 4 (G :ESP S)) S)) S)
                                         0 4096)))
                 (disjointp (LIST (RANGE (+ 4 (G :ESP S)) 0 4)
                                  (RANGE (+ 4 (R32 (+ 4 (G :ESP S)) S))
                                         0 12)
                                  (RANGE (R32 (R32 (+ 4 (G :ESP S)) S) S)
                                         0 4096)
                                  (RANGE (R32 (+ 4 (R32 (+ 4 (G :ESP S)) S)) S)
                                         0 4096)
                                  (RANGE (R32 (+ 8 (R32 (+ 4 (G :ESP S)) S)) S)
                                         0 4096)
                                  (RANGE (R32 (+ 12 (R32 (+ 4 (G :ESP S)) S)) S)
                                         0 4096))))
            (equal (r32 addr (init_pdts-modify-outer-loop-1 i s))
                   (r32 addr s)))
   :hints (("Goal" :cases ((equal i 0)
                           (equal i 1)
                           (equal i 2)
                           (equal i 3))
            :expand ((INIT_PDTS-MODIFY-OUTER-LOOP-1 2 S)
                     (INIT_PDTS-MODIFY-OUTER-LOOP-1 3 S))))
   :otf-flg t)




;;; very messy!!!
;;; DO I need to instantiate
;;; |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|
;;; because it is not unifying, or is worse-than to blame?
 (defthm |(r32 addr (init_pdts-modify-outer-loop-1 i s)) --- written to 1|
   (implies (and (y86-p s)
                 (integerp i)
                 (<= 0 i)
                 (<= i 3)
                 (integerp i-prime)
                 (<= 0 i-prime)
                 (<= i-prime i)
                 (integerp j-prime)
                 (<= 0 j-prime)
                 (<= j-prime 511)
                 (not (paging-p s))
                 ;; (N32P (+ 4 (G :ESP S)))
                 (N32P (+ 7 (G :ESP S)))
                 ;; (N32P (+ 4 (R32 (+ 4 (G :ESP S)) S)))
                 (N32P (+ 15 (R32 (+ 4 (G :ESP S)) S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 0) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 1) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 2) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 3) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (disjointp (LIST (RANGE (+ 4 (G :ESP S)) 0 4)
                                  (RANGE (+ 4 (R32 (+ 4 (G :ESP S)) S))
                                         0 12)
                                  (RANGE (R32 (R32 (+ 4 (G :ESP S)) S) S)
                                         0 4096)
                                  (RANGE (R32 (+ 4 (R32 (+ 4 (G :ESP S)) S)) S)
                                         0 4096)
                                  (RANGE (R32 (+ 8 (R32 (+ 4 (G :ESP S)) S)) S)
                                         0 4096)
                                  (RANGE (R32 (+ 12 (R32 (+ 4 (G :ESP S)) S)) S)
                                         0 4096))))
            (equal (r32 (+ (* 8 j-prime)
                           (R32 (+ (* 4 i-prime)
                                   (R32 (+ 4 (G :ESP S)) S))
                                S))
                        (init_pdts-modify-outer-loop-1 i s))
                   (LOGIOR 231
                           (+ (* 512 I-PRIME 2097152)
                              (* 2097152 J-PRIME)))))
   :hints (("Goal" :cases ((equal i 0)
                           (equal i 1)
                           (equal i 2)
                           (equal i 3))
            :expand ((INIT_PDTS-MODIFY-OUTER-LOOP-1 2 S)
                     (INIT_PDTS-MODIFY-OUTER-LOOP-1 3 S)))
           ("Subgoal 4" :cases ((equal i-prime 0)
                                (equal i-prime 1)
                                (equal i-prime 2)
                                (equal i-prime 3)))
           ("Subgoal 3" :cases ((equal i-prime 0)
                                (equal i-prime 1)
                                (equal i-prime 2)
                                (equal i-prime 3)))
           ("Subgoal 2" :cases ((equal i-prime 0)
                                (equal i-prime 1)
                                (equal i-prime 2)
                                (equal i-prime 3)))
           ("Subgoal 1" :cases ((equal i-prime 0)
                                (equal i-prime 1)
                                (equal i-prime 2)
                                (equal i-prime 3)))
           ("Subgoal 4.4" :in-theory (disable |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|)
            :use ((:instance |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|
                             (i 0)
                             (j 511)
                             (j-prime j-prime)
                             (s s))))
           ("Subgoal 3.4" :in-theory (disable |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|)
            :use ((:instance |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|
                             (i 0)
                             (j 511)
                             (j-prime j-prime)
                             (s s))))
           ("Subgoal 3.3" :in-theory (disable |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|)
            :use ((:instance |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|
                             (i 1)
                             (j 511)
                             (j-prime j-prime)
                             (s (INIT_PDTS-MODIFY-INNER-LOOP-1 0 511 S)))))
           ("Subgoal 2.4" :in-theory (disable |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|)
            :use ((:instance |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|
                             (i 0)
                             (j 511)
                             (j-prime j-prime)
                             (s s))))
           ("Subgoal 2.3" :in-theory (disable |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|)
            :use ((:instance |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|
                             (i 1)
                             (j 511)
                             (j-prime j-prime)
                             (s (INIT_PDTS-MODIFY-INNER-LOOP-1 0 511 S)))))
           ("Subgoal 2.2" :in-theory (disable |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|)
            :use ((:instance |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|
                             (i 2)
                             (j 511)
                             (j-prime j-prime)
                             (s (INIT_PDTS-MODIFY-INNER-LOOP-1 1 511
                                                               (INIT_PDTS-MODIFY-INNER-LOOP-1 0 511 S))))))
           ("Subgoal 1.4" :in-theory (disable |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|)
            :use ((:instance |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|
                             (i 0)
                             (j 511)
                             (j-prime j-prime)
                             (s s))))
           ("Subgoal 1.3" :in-theory (disable |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|)
            :use ((:instance |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|
                             (i 1)
                             (j 511)
                             (j-prime j-prime)
                             (s (INIT_PDTS-MODIFY-INNER-LOOP-1 0 511 S)))))
           ("Subgoal 1.2" :in-theory (disable |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|)
            :use ((:instance |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|
                             (i 2)
                             (j 511)
                             (j-prime j-prime)
                             (s (INIT_PDTS-MODIFY-INNER-LOOP-1 1 511
                                                               (INIT_PDTS-MODIFY-INNER-LOOP-1 0 511 S))))))
           ("Subgoal 1.1" :in-theory (disable |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|)
            :use ((:instance |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|
                             (i 3)
                             (j 511)
                             (j-prime j-prime)
                             (s (INIT_PDTS-MODIFY-INNER-LOOP-1
                                 2 511
                                 (INIT_PDTS-MODIFY-INNER-LOOP-1
                                  1 511
                                  (INIT_PDTS-MODIFY-INNER-LOOP-1 0 511 S)))))))
           )
   :otf-flg t)

;;; Very messy!!!
;;; DO I need to instantiate
;;; |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|
;;; because it is not unifying, or is worse-than to blame?
 (defthm |(r32 addr (init_pdts-modify-outer-loop-1 i s)) --- written to 2|
   (implies (and (y86-p s)
                 (integerp i)
                 (<= 0 i)
                 (<= i 3)
                 (integerp i-prime)
                 (<= 0 i-prime)
                 (<= i-prime i)
                 (integerp j-prime)
                 (<= 0 j-prime)
                 (<= j-prime 511)
                 (not (paging-p s))
                 ;; (N32P (+ 4 (G :ESP S)))
                 (N32P (+ 7 (G :ESP S)))
                 ;; (N32P (+ 4 (R32 (+ 4 (G :ESP S)) S)))
                 (N32P (+ 15 (R32 (+ 4 (G :ESP S)) S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 0) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 1) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 2) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 3) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (disjointp (LIST (RANGE (+ 4 (G :ESP S)) 0 4)
                                  (RANGE (+ 4 (R32 (+ 4 (G :ESP S)) S))
                                         0 12)
                                  (RANGE (R32 (R32 (+ 4 (G :ESP S)) S) S)
                                         0 4096)
                                  (RANGE (R32 (+ 4 (R32 (+ 4 (G :ESP S)) S)) S)
                                         0 4096)
                                  (RANGE (R32 (+ 8 (R32 (+ 4 (G :ESP S)) S)) S)
                                         0 4096)
                                  (RANGE (R32 (+ 12 (R32 (+ 4 (G :ESP S)) S)) S)
                                         0 4096))))
            (equal (r32 (+ 4
                           (* 8 j-prime)
                           (R32 (+ (* 4 i-prime)
                                   (R32 (+ 4 (G :ESP S)) S))
                                S))
                        (init_pdts-modify-outer-loop-1 i s))
                   0))
   :hints (("Goal" :cases ((equal i 0)
                           (equal i 1)
                           (equal i 2)
                           (equal i 3))
            :expand ((INIT_PDTS-MODIFY-OUTER-LOOP-1 2 S)
                     (INIT_PDTS-MODIFY-OUTER-LOOP-1 3 S)))
           ("Subgoal 4" :cases ((equal i-prime 0)
                                (equal i-prime 1)
                                (equal i-prime 2)
                                (equal i-prime 3)))
           ("Subgoal 3" :cases ((equal i-prime 0)
                                (equal i-prime 1)
                                (equal i-prime 2)
                                (equal i-prime 3)))
           ("Subgoal 2" :cases ((equal i-prime 0)
                                (equal i-prime 1)
                                (equal i-prime 2)
                                (equal i-prime 3)))
           ("Subgoal 1" :cases ((equal i-prime 0)
                                (equal i-prime 1)
                                (equal i-prime 2)
                                (equal i-prime 3)))
           ("Subgoal 4.4" :in-theory (disable |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|)
            :use ((:instance |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|
                             (i 0)
                             (j 511)
                             (j-prime j-prime)
                             (s s))))
           ("Subgoal 3.4" :in-theory (disable |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|)
            :use ((:instance |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|
                             (i 0)
                             (j 511)
                             (j-prime j-prime)
                             (s s))))
           ("Subgoal 3.3" :in-theory (disable |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|)
            :use ((:instance |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|
                             (i 1)
                             (j 511)
                             (j-prime j-prime)
                             (s (INIT_PDTS-MODIFY-INNER-LOOP-1 0 511 S)))))
           ("Subgoal 2.4" :in-theory (disable |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|)
            :use ((:instance |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|
                             (i 0)
                             (j 511)
                             (j-prime j-prime)
                             (s s))))
           ("Subgoal 2.3" :in-theory (disable |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|)
            :use ((:instance |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|
                             (i 1)
                             (j 511)
                             (j-prime j-prime)
                             (s (INIT_PDTS-MODIFY-INNER-LOOP-1 0 511 S)))))
           ("Subgoal 2.2" :in-theory (disable |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|)
            :use ((:instance |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|
                             (i 2)
                             (j 511)
                             (j-prime j-prime)
                             (s (INIT_PDTS-MODIFY-INNER-LOOP-1 1 511
                                                               (INIT_PDTS-MODIFY-INNER-LOOP-1 0 511 S))))))
           ("Subgoal 1.4" :in-theory (disable |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|)
            :use ((:instance |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|
                             (i 0)
                             (j 511)
                             (j-prime j-prime)
                             (s s))))
           ("Subgoal 1.3" :in-theory (disable |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|)
            :use ((:instance |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|
                             (i 1)
                             (j 511)
                             (j-prime j-prime)
                             (s (INIT_PDTS-MODIFY-INNER-LOOP-1 0 511 S)))))
           ("Subgoal 1.2" :in-theory (disable |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|)
            :use ((:instance |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|
                             (i 2)
                             (j 511)
                             (j-prime j-prime)
                             (s (INIT_PDTS-MODIFY-INNER-LOOP-1 1 511
                                                               (INIT_PDTS-MODIFY-INNER-LOOP-1 0 511 S))))))
           ("Subgoal 1.1" :in-theory (disable |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|)
            :use ((:instance |(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|
                             (i 3)
                             (j 511)
                             (j-prime j-prime)
                             (s (INIT_PDTS-MODIFY-INNER-LOOP-1
                                 2 511
                                 (INIT_PDTS-MODIFY-INNER-LOOP-1
                                  1 511
                                  (INIT_PDTS-MODIFY-INNER-LOOP-1 0 511 S)))))))

           )
   :otf-flg t)




 (defthm |(good-state-p (init_pdts-modify-outer-loop-1 i s))|
   (implies (and (good-state-p s)
                 (integerp i)
                 (<= 0 i)
                 (<= i 3)
                 (not (paging-p s))
                 ;; These next two hyps are needed because we write to
                 ;; them in the loop.  If I were to drop the
                 ;; rewuirement that all addresses be 32-bit, this
                 ;; would go away.  Simplification is good.
                 ;; (N32P (+ 4 (G :ESP S)))
                 (N32P (+ 7 (G :ESP S)))
                 ;; (N32P (+ 4 (R32 (+ 4 (G :ESP S)) S)))
                 (N32P (+ 15 (R32 (+ 4 (G :ESP S)) S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 0) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 1) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 2) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 3) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (disjointp (LIST (range (snpt-code-location) 0 993)
                                  (RANGE (+ 4 (G :ESP S)) 0 4)
                                  (RANGE (+ 0 (R32 (+ 4 (G :ESP S)) S))
                                         0 16)  ; !!! diff
                                  (RANGE (R32 (R32 (+ 4 (G :ESP S)) S) S)
                                         0 4096)
                                  (RANGE (R32 (+ 4 (R32 (+ 4 (G :ESP S)) S)) S)
                                         0 4096)
                                  (RANGE (R32 (+ 8 (R32 (+ 4 (G :ESP S)) S)) S)
                                         0 4096)
                                  (RANGE (R32 (+ 12 (R32 (+ 4 (G :ESP S)) S)) S)
                                         0 4096))))
            (good-state-p (init_pdts-modify-outer-loop-1 i s)))
   :hints (("Goal" :cases ((equal i 0)
                           (equal i 1)
                           (equal i 2)
                           (equal i 3))
            :expand ((INIT_PDTS-MODIFY-OUTER-LOOP-1 2 S)
                     (INIT_PDTS-MODIFY-OUTER-LOOP-1 3 S)))))


 (defthm |(init_pdts-modify-outer-loop-1 i (w32 addr val s))|
   (implies (and (y86-p s)
                 (integerp i)
                 (<= 0 i)
                 (<= i 3)
                 (not (paging-p s))
                 ;; !!! This should subsume the next two
                 ;; (good-32-address-p addr s)
                 (n32p addr)
                 (n32p (+ 3 addr))
                 ;; (N32P (+ 4 (G :ESP S)))
                 (N32P (+ 7 (G :ESP S)))
                 ;; (N32P (+ 4 (R32 (+ 4 (G :ESP S)) S)))
                 (N32P (+ 15 (R32 (+ 4 (G :ESP S)) S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 0) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 1) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 2) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (n32p (+ 7 (* 8 511)
                          (R32 (+ (* 4 3) (R32 (+ 4 (G :ESP S)) S))
                               S)))
                 (disjointp (list (range addr 0 4)
                                  (range (+ 4 (G :ESP S)) 0 4)
                                  (range (R32 (+ 4 (G :ESP S)) S) 0 16)
                                  (range (R32 (+ (* 4 0) (R32 (+ 4 (G :ESP S)) S))
                                              S)
                                         0
                                         4096)
                                  (range (R32 (+ (* 4 1) (R32 (+ 4 (G :ESP S)) S))
                                              S)
                                         0
                                         4096)
                                  (range (R32 (+ (* 4 2) (R32 (+ 4 (G :ESP S)) S))
                                              S)
                                         0
                                         4096)
                                  (range (R32 (+ (* 4 3) (R32 (+ 4 (G :ESP S)) S))
                                              S)
                                         0
                                         4096))))
            (equal (init_pdts-modify-outer-loop-1 i
                                                  (w32 addr val s))
                   (w32 addr val (init_pdts-modify-outer-loop-1 i s))))
   :hints (("Goal" :cases ((equal i 0)
                           (equal i 1)
                           (equal i 2)
                           (equal i 3))
            :expand ((INIT_PDTS-MODIFY-OUTER-LOOP-1 2 S)
                     (INIT_PDTS-MODIFY-OUTER-LOOP-1 3 S))))
   :otf-flg t)
 )

;;; i --- outer loop counter
;;; j --- inner loop counter
(defun init_pdts-modify-inner-loop (i j cf of sf zf imme1 valu1 s)
  (if (equal i 0)
      (if (equal j 0)
          (UPDATE-REGS :EAX (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                    (* 4 i))
                                 S)
                       :EBP (+ -4 (G :ESP S))
                       :EIP (+ 614 (SNPT-CODE-LOCATION))
                       :ESP (+ -60 (G :ESP S))
                       :F-CF cf
                       :F-OF of
                       :F-SF sf
                       :F-ZF zf
                       :IMME1 imme1
                       :VALU1 valu1
                       (UPDATE-MEM (+ -4 (G :ESP S))
                                   (G :EBP S)

                                   (+ -8 (G :ESP S))
                                   (G :ESI S)

                                   (+ -12 (G :ESP S))
                                   (G :EBX S)

                                   (+ -16 (G :ESP S))
                                   0

                                   (+ -20 (G :ESP S))
                                   2097152

                                   (+ -24 (G :ESP S))
                                   0

                                   (+ -28 (G :ESP S))
                                   231

                                   (+ -32 (G :ESP S))
                                   j

                                   (+ -36 (G :ESP S))
                                   i

                                   (+ -40 (G :ESP S))
                                   (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                           (* 4 i))
                                        S)

                                   (+ -48 (G :ESP S))
                                   0

                                   (+ -52 (G :ESP S))
                                   0

                                   S))
        (let ((j (+ -1 j)))
          (UPDATE-REGS :EAX 2097152
                       :EBP (+ -4 (G :ESP S))
                       :EBX 0
                       :ECX 231
                       :EDX 0
                       :EIP (+ 614 (SNPT-CODE-LOCATION))
                       :ESI (+ (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                       (* 4 i))
                                    S)
                               (* 8 j))
                       :ESP (+ -60 (G :ESP S))
                       :F-CF cf
                       :F-OF of
                       :F-SF sf
                       :F-ZF zf
                       :IMME1 imme1
                       :VALU1 valu1
                       (UPDATE-MEM (+ -4 (G :ESP S))
                                   (G :EBP S)

                                   (+ -8 (G :ESP S))
                                   (G :ESI S)

                                   (+ -12 (G :ESP S))
                                   (G :EBX S)

                                   (+ -16 (G :ESP S))
                                   0

                                   (+ -20 (G :ESP S))
                                   2097152

                                   (+ -24 (G :ESP S))
                                   0

                                   (+ -28 (G :ESP S))
                                   231

                                   (+ -32 (G :ESP S))
                                   (+ 1 j)

                                   (+ -36 (G :ESP S))
                                   i

                                   (+ -40 (G :ESP S))
                                   (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                           (* 4 i))
                                        S)

                                   (+ -48 (G :ESP S))
                                   0

                                   (+ -52 (G :ESP S))
                                   (* 2097152 (+ 1 j))

                                   (init_pdts-modify-inner-loop-1 i j S)))))
    (if (equal j 0)
        (UPDATE-REGS :EAX (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                    (* 4 i))
                                 S)
                       :EBP (+ -4 (G :ESP S))
                       :EBX 0
                       :ECX 231
                       :EDX 0
                       :EIP (+ 614 (SNPT-CODE-LOCATION))
                       ;; set at the end of the previous time through
                       :ESI (+ (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                       (* 4 (+ -1 i)))
                                    S)
                               (* 8 511))
                       :ESP (+ -60 (G :ESP S))
                       :F-CF cf
                       :F-OF of
                       :F-SF sf
                       :F-ZF zf
                       :IMME1 imme1
                       :VALU1 valu1
                       (UPDATE-MEM (+ -4 (G :ESP S))
                                   (G :EBP S)

                                   (+ -8 (G :ESP S))
                                   (G :ESI S)

                                   (+ -12 (G :ESP S))
                                   (G :EBX S)

                                   (+ -16 (G :ESP S))
                                   0

                                   (+ -20 (G :ESP S))
                                   2097152

                                   (+ -24 (G :ESP S))
                                   0

                                   (+ -28 (G :ESP S))
                                   231

                                   (+ -32 (G :ESP S))
                                   j

                                   (+ -36 (G :ESP S))
                                   i

                                   (+ -40 (G :ESP S))
                                   (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                           (* 4 i))
                                        S)

                                   (+ -48 (G :ESP S))
                                   0

                                   (+ -52 (G :ESP S))
                                   (* 512 i 2097152)

                                   (init_pdts-modify-outer-loop-1 (+ -1 i) S)))
        (let ((j (+ -1 j)))
          (UPDATE-REGS :EAX 2097152
                       :EBP (+ -4 (G :ESP S))
                       :EBX 0
                       :ECX 231
                       :EDX 0
                       :EIP (+ 614 (SNPT-CODE-LOCATION))
                       :ESI (+ (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                       (* 4 i))
                                    S)
                               (* 8 j))
                       :ESP (+ -60 (G :ESP S))
                       :F-CF cf
                       :F-OF of
                       :F-SF sf
                       :F-ZF zf
                       :IMME1 imme1
                       :VALU1 valu1
                       (UPDATE-MEM (+ -4 (G :ESP S))
                                   (G :EBP S)

                                   (+ -8 (G :ESP S))
                                   (G :ESI S)

                                   (+ -12 (G :ESP S))
                                   (G :EBX S)

                                   (+ -16 (G :ESP S))
                                   0

                                   (+ -20 (G :ESP S))
                                   2097152

                                   (+ -24 (G :ESP S))
                                   0

                                   (+ -28 (G :ESP S))
                                   231

                                   (+ -32 (G :ESP S))
                                   (+ 1 j)

                                   (+ -36 (G :ESP S))
                                   i

                                   (+ -40 (G :ESP S))
                                   (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                           (* 4 i))
                                        S)

                                   (+ -48 (G :ESP S))
                                   (if (and (equal i 3)
                                            (equal j 511))
                                       1
                                     0)

                                   (+ -52 (G :ESP S))
                                   (if (and (equal i 3)
                                            (equal j 511))
                                       0
                                     (+ (* 512 i 2097152)
                                        (* 2097152 (+ 1 j))))

                                   (init_pdts-modify-inner-loop-1
                                    i j
                                    (init_pdts-modify-outer-loop-1 (+ -1 i) S))))))))

(defun init_pdts-modify-outer-loop (i j cf of sf zf imme1 valu1 s)
  (if (equal i 0)
      (UPDATE-REGS :EBP (+ -4 (G :ESP S))
                   :EIP (+ 653 (SNPT-CODE-LOCATION))
                   :ESP (+ -60 (G :ESP S))
                   :F-CF cf
                   :F-OF of
                   :F-SF sf
                   :F-ZF zf
                   :IMME1 imme1
                   (UPDATE-MEM (+ -4 (G :ESP S))
                               (G :EBP S)

                               (+ -8 (G :ESP S))
                               (G :ESI S)

                               (+ -12 (G :ESP S))
                               (G :EBX S)

                               (+ -16 (G :ESP S))
                               0

                               (+ -20 (G :ESP S))
                               2097152

                               (+ -24 (G :ESP S))
                               0

                               (+ -28 (G :ESP S))
                               231

                               (+ -36 (G :ESP S))
                               i

                               (+ -48 (G :ESP S))
                               0

                               (+ -52 (G :ESP S))
                               0

                               S))
    (let ((i (+ -1 i))
          (j (+ -1 j)))
      (UPDATE-REGS :EAX 2097152
                   :EBP (+ -4 (G :ESP S))
                   :EBX 0
                   :ECX 231
                   :EDX 0
                   :EIP (+ 653 (SNPT-CODE-LOCATION))
                   :ESI (+ (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                   (* 4 i))
                                S)
                           (* 8 j))
                   :ESP (+ -60 (G :ESP S))
                   :F-CF cf
                   :F-OF of
                   :F-SF sf
                   :F-ZF zf
                   :IMME1 imme1
                   :VALU1 valu1
                   (UPDATE-MEM (+ -4 (G :ESP S))
                               (G :EBP S)

                               (+ -8 (G :ESP S))
                               (G :ESI S)

                               (+ -12 (G :ESP S))
                               (G :EBX S)

                               (+ -16 (G :ESP S))
                               0

                               (+ -20 (G :ESP S))
                               2097152

                               (+ -24 (G :ESP S))
                               0

                               (+ -28 (G :ESP S))
                               231

                               (+ -32 (G :ESP S))
                               (+ 1 j)

                               (+ -36 (G :ESP S))
                               (+ 1 i)

                               (+ -40 (G :ESP S))
                               (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                       (* 4 i))
                                    S)

                               (+ -48 (G :ESP S))
                               (if (equal i 3)
                                   1
                                 0)

                               (+ -52 (G :ESP S))
                               (if (equal i 3)
                                   0
                                 (* 512 (+ 1 i) 2097152))

                               (init_pdts-modify-outer-loop-1 i S))))))

(defun init_pdts-modify (s)
  (let ((i 3)
        (j 512))
    (UPDATE-REGS :EAX 2097152
                 :EBP (G :EBP S)
                 :EBX (G :EBX S)
                 :ECX 231
                 :EDX 0
                 :EIP (R32 (G :ESP S) S)
                 :ESI (G :ESI S)
                 :ESP (+ 4 (G :ESP S))
                 :F-CF (CF (+ -12 (G :ESP S))
                           (+ -12 (G :ESP S)))
                 :F-OF (OF (N32-TO-I32 (+ -12 (G :ESP S)))
                           (+ 48 (N32-TO-I32 (+ -60 (G :ESP S)))))
                 :F-SF (SF (N32-TO-I32 (+ -12 (G :ESP S))))
                 :F-ZF (ZF (+ -12 (G :ESP S)))
                 :IMME1 3
                 :VALU1 48
                 (UPDATE-MEM (+ -4 (G :ESP S))
                             (G :EBP S)

                             (+ -8 (G :ESP S))
                             (G :ESI S)

                             (+ -12 (G :ESP S))
                             (G :EBX S)

                             (+ -16 (G :ESP S))
                             0

                             (+ -20 (G :ESP S))
                             2097152

                             (+ -24 (G :ESP S))
                             0

                             (+ -28 (G :ESP S))
                             231

                             (+ -32 (G :ESP S))
                             j

                             (+ -36 (G :ESP S))
                             (+ 1 i)

                             (+ -40 (G :ESP S))
                             (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                     (* 4 i))
                                  S)

                             (+ -48 (G :ESP S))
                             1

                             (+ -52 (G :ESP S))
                             0

                             (init_pdts-modify-outer-loop-1 i S)))))

;;; qwerty
;;; these are the theorems we want about init_pdts-modify
(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm |(paging-p (init_pdts-modify s))|
   (equal (paging-p (init_pdts-modify s))
          (paging-p s)))

 (defthm |(va-to-pa addr (init_pdts-modify s))|
   (implies (not (paging-p s))
            (equal (va-to-pa addr (init_pdts-modify s))
                   (va-to-pa addr s))))

 (defthm |(good-32-address-p addr (init_pdts-modify s))|
   (implies (not (paging-p s))
            (equal (good-32-address-p addr (init_pdts-modify s))
                   (good-32-address-p addr s)))
   :hints (("Goal" :in-theory (enable good-32-address-p))))

 (defthm |(y86-p (init_pdts-modify s))|
   (implies (init_pdts-pre s)
            (y86-p (init_pdts-modify s)))
   :hints (("Goal" :in-theory (enable y86-p
                                      Y86-REGISTER-GUARD
                                      Y86-SUPERVISOR-GUARD
                                      Y86-FLAGS-GUARD
                                      Y86-MISC-GUARD
                                      ))))

 (defthm |(memoryp (g :mem (init_pdts-modify s)))|
   (implies (init_pdts-pre s)
            (memoryp (g :mem (init_pdts-modify s)))))

 (defthm |(good-state-p (init_pdts-modify s))|
   (implies (init_pdts-pre s)
            (good-state-p (init_pdts-modify s))))

 (defthm |(g :cr0 (init_pdts-modify s))|
   (implies (init_pdts-pre s)
            (equal (g :cr0 (init_pdts-modify s))
                   (G :cr0 S))))

 (defthm |(g :eip (init_pdts-modify s))|
   (implies (init_pdts-pre s)
            (equal (g :eip (init_pdts-modify s))
                   (R32 (G :ESP S) S))))

 (defthm |(g :ebp (init_pdts-modify s))|
   (implies (init_pdts-pre s)
            (equal (g :ebp (init_pdts-modify s))
                   (G :EBP S))))

 (defthm |(g :esp (init_pdts-modify s))|
   (implies (init_pdts-pre s)
            (equal (g :esp (init_pdts-modify s))
                   (+ 4 (G :ESP S)))))

 (defthm |(r32 addr (init_pdts-modify s))|
   (implies (and (init_pdts-pre s)
                 (n32p addr)
                 (n32p (+ 3 addr))
                 (disjointp (list (range addr 0 4)
                                  (range (g :esp s) -56 56)
                                  (range (r32 (r32 (+ 4 (g :esp s)) s) s) 0 (* 512 8))
                                  (range (r32 (+ 4 (r32 (+ 4 (g :esp s)) s)) s) 0 (* 512 8))
                                  (range (r32 (+ 8 (r32 (+ 4 (g :esp s)) s)) s) 0 (* 512 8))
                                  (range (r32 (+ 12 (r32 (+ 4 (g :esp s)) s)) s) 0 (* 512 8)))))
            (equal (r32 addr (init_pdts-modify s))
                   (r32 addr s))))

 (defthm |(r32 addr (init_pdts-modify s)) --- written to 1|
   (implies (and (init_pdts-pre s)
                 (integerp i-prime)
                 (<= 0 i-prime)
                 (<= i-prime 3)
                 (integerp j-prime)
                 (<= 0 j-prime)
                 (<= j-prime 511))
            (equal (r32 (+ (* 8 j-prime)
                           (R32 (+ (* 4 i-prime)
                                   (R32 (+ 4 (G :ESP S)) S))
                                S))
                        (init_pdts-modify s))
                   (LOGIOR 231
                           (+ (* 512 I-PRIME 2097152)
                              (* 2097152 J-PRIME)))))
   :hints (("Goal" :cases ((equal i-prime 0)
                           (equal i-prime 1)
                           (equal i-prime 2)
                           (equal i-prime 3)))
           ("Subgoal 4" :in-theory (disable |(r32 addr (init_pdts-modify-outer-loop-1 i s)) --- written to 1|)
            :use ((:instance |(r32 addr (init_pdts-modify-outer-loop-1 i s)) --- written to 1|
                             (i-prime 0)
                             (i 3))))))

 (defthm |(r32 addr (init_pdts-modify s)) --- written to 2|
   (implies (and (init_pdts-pre s)
                 (integerp i-prime)
                 (<= 0 i-prime)
                 (<= i-prime 3)
                 (integerp j-prime)
                 (<= 0 j-prime)
                 (<= j-prime 511))
            (equal (r32 (+ 4
                           (* 8 j-prime)
                           (R32 (+ (* 4 i-prime)
                                   (R32 (+ 4 (G :ESP S)) S))
                                S))
                        (init_pdts-modify s))
                   0))
   :hints (("Goal" :cases ((equal i-prime 0)
                           (equal i-prime 1)
                           (equal i-prime 2)
                           (equal i-prime 3)))
           ("Subgoal 4" :in-theory (disable |(r32 addr (init_pdts-modify-outer-loop-1 i s)) --- written to 2|)
            :use ((:instance |(r32 addr (init_pdts-modify-outer-loop-1 i s)) --- written to 2|
                             (i-prime 0)
                             (i 3))))))

 )

(defun init_pdts-assertion (s0 s1)
  (cond ((not (in-sub s1))
         ;; exit
         (equal s1 (init_pdts-modify s0)))
        ((equal (g :eip s1)
                (+ *INIT_PDTS* (snpt-code-location)))
         ;; start
         (and (init_pdts-pre s1)
              (equal s1 s0)))
        ((equal (g :eip s1)
                (+ *L7* (snpt-code-location)))
         ;; outer loop
         (and (init_pdts-pre s0)
              (init_pdts-outer-loop-pre s1)
              (let ((i (r32 (+ -32 (g :ebp s1)) s1))
                    (j (r32 (+ -28 (g :ebp s1)) s1))
                    (cf (g :f-cf s1))
                    (of (g :f-of s1))
                    (sf (g :f-sf s1))
                    (zf (g :f-zf s1))
                    (imme1 (g :imme1 s1))
                    (valu1 (g :valu1 s1)))
                (equal s1 (init_pdts-modify-outer-loop i j cf of sf zf imme1 valu1 s0)))))
        ((equal (g :eip s1)
                (+ *L9* (snpt-code-location)))
         ;; inner loop
         (and (init_pdts-pre s0)
              (init_pdts-inner-loop-pre s1)
              (let ((i (r32 (+ -32 (g :ebp s1)) s1))
                    (j (r32 (+ -28 (g :ebp s1)) s1))
                    (cf (g :f-cf s1))
                    (of (g :f-of s1))
                    (sf (g :f-sf s1))
                    (zf (g :f-zf s1))
                    (imme1 (g :imme1 s1))
                    (valu1 (g :valu1 s1)))
                (equal s1 (init_pdts-modify-inner-loop i j cf of sf zf imme1 valu1 s0)))))
        (t
         'NIL)))

(ENCAPSULATE
 NIL
 (LOCAL (DEFTHEORY USER-THEORY (CURRENT-THEORY :HERE)))
 (LOCAL
  (ENCAPSULATE
   NIL
   (LOCAL (DEFTHEORY $$$SUBTHEORY (CURRENT-THEORY :HERE)))
   (LOCAL (IN-THEORY (THEORY 'GROUND-ZERO)))
   (DEFUN-NX $$$INSUB (S1)
     (DECLARE (XARGS :NORMALIZE NIL))
     NIL)
   (DEFUN-NX $$$PRESUB (S1) NIL)
   (DEFUN-NX $$$MODIFYSUB (S1)
     (DECLARE (XARGS :NORMALIZE NIL))
     "Should never see this in a proof")
   (DEFTHM $$$NO-MAIN-CUTPOINT-IN-SUB
     (IMPLIES ($$$INSUB S1)
              (NOT (INIT_PDTS-CUTPOINT-P S1)))
     :RULE-CLASSES NIL)
   (DEFTHM $$$IN-SUB-IMPLIES-IN-MAIN
     (IMPLIES ($$$INSUB S1)
              (IN-SUB S1))
     :RULE-CLASSES NIL)
   (DEFTHM $$$PRESUB-IMPLIES-INSUB
     (IMPLIES ($$$PRESUB S1) ($$$INSUB S1))
     :RULE-CLASSES NIL)
   (DEFP $$$STEPS-TO-EXITPOINT-SUB-TAIL (S1 I)
     (IF (NOT ($$$INSUB S1))
         I
         (LET* ((S1 (Y86-STEP S1)))
               ($$$STEPS-TO-EXITPOINT-SUB-TAIL S1 (1+ I)))))
   (DEFUN-NX $$$STEPS-TO-EXITPOINT-SUB (S1)
     (DECLARE (XARGS :NORMALIZE NIL))
     (LET* ((STEPS ($$$STEPS-TO-EXITPOINT-SUB-TAIL S1 0))
            (S1 (Y86 S1 STEPS)))
           (IF (NOT ($$$INSUB S1)) STEPS (OMEGA))))
   (DEFUN-NX $$$NEXT-EXITPOINT-SUB (S1)
     (Y86 S1 ($$$STEPS-TO-EXITPOINT-SUB S1)))
   (DEFUN-SK $$$EXISTS-EXITPOINT-SUB (S1)
     (DECLARE (XARGS :NORMALIZE NIL))
     (EXISTS N
             (LET* ((S1 (Y86 S1 N)))
                   (NOT ($$$INSUB S1)))))
   (DEFTHM $$$CORRECTNESS-OF-SUB
     (IMPLIES (AND ($$$PRESUB S1)
                   ($$$EXISTS-EXITPOINT-SUB S1))
              (AND (LET* ((S1 ($$$NEXT-EXITPOINT-SUB S1)))
                         (NOT ($$$INSUB S1)))
                   (EQUAL ($$$NEXT-EXITPOINT-SUB S1)
                          ($$$MODIFYSUB S1))))
     :RULE-CLASSES NIL)
   (LOCAL (IN-THEORY (THEORY 'GROUND-ZERO)))
   (DEFP $$$NEXT-CUTPOINT-MAIN (S1)
     (IF (OR (INIT_PDTS-CUTPOINT-P S1)
             (NOT (IN-SUB S1)))
         S1
         (LET* ((S1 (IF ($$$PRESUB S1)
                        ($$$MODIFYSUB S1)
                        (Y86-STEP S1))))
               ($$$NEXT-CUTPOINT-MAIN S1))))
   (DEFTHM $$$DEFP-SYMSIM-THEOREM
     (implies (syntaxp (not (equal (fn-symb s1)
                                   'y86-step)))
              (EQUAL ($$$NEXT-CUTPOINT-MAIN S1)
                     (IF (OR (INIT_PDTS-CUTPOINT-P S1)
                             (NOT (IN-SUB S1)))
                         S1
                         (LET* ((S1 (Y86-STEP S1)))
                               ($$$NEXT-CUTPOINT-MAIN S1)))))
     :HINTS (("Goal" :IN-THEORY (ENABLE $$$PRESUB $$$MODIFYSUB))))))
 (LOCAL (DEFTHM $$$PRE-IMPLIES-ASSERTION
          (IMPLIES (INIT_PDTS-PRE S1)
                   (LET ((S0 S1))
                        (INIT_PDTS-ASSERTION S0 S1)))
          :RULE-CLASSES NIL))
 (LOCAL (DEFTHM $$$ASSERTION-MAIN-IMPLIES-POST
          (IMPLIES (AND (INIT_PDTS-ASSERTION S0 S1)
                        (NOT (IN-SUB S1)))
                   (EQUAL S1
                          (LET ((S1 S0)) (INIT_PDTS-MODIFY S1))))
          :RULE-CLASSES NIL))
 (LOCAL (DEFTHM $$$ASSERTION-IMPLIES-CUTPOINT
          (IMPLIES (INIT_PDTS-ASSERTION S0 S1)
                   (OR (INIT_PDTS-CUTPOINT-P S1)
                       (NOT (IN-SUB S1))))
          :RULE-CLASSES NIL))
 (LOCAL (IN-THEORY (THEORY 'GROUND-ZERO)))
 (LOCAL (DEFUN-SK $$$EXISTS-NEXT-CUTPOINT (S1)
          (EXISTS N
                  (LET* ((S1 (Y86 S1 N)))
                        (INIT_PDTS-CUTPOINT-P S1)))))
 (LOCAL (IN-THEORY (UNION-THEORIES (THEORY 'USER-THEORY)
                                   (LIST '$$$DEFP-SYMSIM-THEOREM))))

 (local (include-book "arithmetic-5/top" :dir :system))

 (local
  (in-theory (disable $$$DEFP-SYMSIM-THEOREM)))

 (local
  (defun simulation-default-hint (stable-under-simplificationp clause)
    (if stable-under-simplificationp
        (let ((concl (car (last clause))))
          (cond ((and (equal (fn-symb concl) 'EQUAL)
                      (equal (fn-symb (arg1 concl)) '$$$NEXT-CUTPOINT-MAIN)
                      (not (equal (fn-symb (arg1 (arg1 concl))) 'Y86-STEP)))
                 `(:computed-hint-replacement t
                                              :expand (,(arg1 concl))))
                ((and (equal (fn-symb concl) 'EQUAL)
                      (equal (fn-symb (arg2 concl)) '$$$NEXT-CUTPOINT-MAIN)
                      (not (equal (fn-symb (arg1 (arg2 concl))) 'Y86-STEP)))
                 `(:computed-hint-replacement t
                                              :expand (,(arg2 concl))))
                (t
                 nil)))
      nil)))

 (local
  (set-default-hints '((simulation-default-hint stable-under-simplificationp clause))))

 (local
  (in-theory (enable n32+ n32)))

 (local
  (in-theory (disable cf zf sf of
                      subl-cf
                      sall-cf sall-of
                      shrl-cf shrl-of
                      unpack)))




 (local
  (defthm simulate-main
    (implies (and (cond ((not (in-sub s1))
                         ;; exit
                         t)
                        ((equal (g :eip s1)
                                (+ *INIT_PDTS* (snpt-code-location)))
                         ;; start
                         (and (init_pdts-pre s1)
                              t))
                        ((equal (g :eip s1)
                                (+ *L7* (snpt-code-location)))
                         ;; outer loop
                         (and t
                              (init_pdts-outer-loop-pre s1)
                              t))
                        ((equal (g :eip s1)
                                (+ *L9* (snpt-code-location)))
                         ;; inner loop
                         (and t
                              (init_pdts-inner-loop-pre s1)
                              ;; !!!

                              t))
                        (t
                         'NIL))
                  (in-sub s1))
             (equal ($$$NEXT-CUTPOINT-MAIN (Y86-STEP S1))
                    (cond ((not (in-sub s1))
                           ;; exit
                           t)
                          ((equal (g :eip s1)
                                  (+ *INIT_PDTS* (snpt-code-location)))
                           ;; start
                           (UPDATE-REGS :EBP (+ -4 (G :ESP S1))
                                        :EIP (+ 653 (SNPT-CODE-LOCATION))
                                        :ESP (+ -60 (G :ESP S1))
                                        :F-CF (SUBL-CF 48 (+ -12 (G :ESP S1)))
                                        :F-OF
                                        (OF (N32-TO-I32 (+ -60 (G :ESP S1)))
                                            (+ -48 (N32-TO-I32 (+ -12 (G :ESP S1)))))
                                        :F-SF
                                        (SF (N32-TO-I32 (+ -60 (G :ESP S1))))
                                        :F-ZF (ZF (+ -60 (G :ESP S1)))
                                        :IMME1 0
                                        (UPDATE-MEM (+ -4 (G :ESP S1))
                                                    (G :EBP S1)
                                                    (+ -8 (G :ESP S1))
                                                    (G :ESI S1)
                                                    (+ -12 (G :ESP S1))
                                                    (G :EBX S1)
                                                    (+ -16 (G :ESP S1))
                                                    0 (+ -20 (G :ESP S1))
                                                    2097152 (+ -24 (G :ESP S1))
                                                    0 (+ -28 (G :ESP S1))
                                                    231 (+ -36 (G :ESP S1))
                                                    0 (+ -48 (G :ESP S1))
                                                    0 (+ -52 (G :ESP S1))
                                                    0 S1)))
                          ((and (equal (g :eip s1)
                                       (+ *L7* (snpt-code-location)))
                                (<= (r32 (+ -32 (g :ebp s1)) s1) 3))
                           ;; stay in outer loop
                           (UPDATE-REGS :EAX
                                        (R32 (+ (R32 (+ 8 (G :EBP S1)) S1)
                                                (* 4 (R32 (+ -32 (G :EBP S1)) S1)))
                                             S1)
                                        :EIP (+ 614 (SNPT-CODE-LOCATION))
                                        :F-CF
                                        (CF (+ (R32 (+ 8 (G :EBP S1)) S1)
                                               (* 4 (R32 (+ -32 (G :EBP S1)) S1)))
                                            (+ (R32 (+ 8 (G :EBP S1)) S1)
                                               (* 4 (R32 (+ -32 (G :EBP S1)) S1))))
                                        :F-OF
                                        (OF (N32-TO-I32 (+ (R32 (+ 8 (G :EBP S1)) S1)
                                                           (* 4 (R32 (+ -32 (G :EBP S1)) S1))))
                                            (+ (N32-TO-I32 (R32 (+ 8 (G :EBP S1)) S1))
                                               (* 4 (R32 (+ -32 (G :EBP S1)) S1))))
                                        :F-SF
                                        (SF (N32-TO-I32 (+ (R32 (+ 8 (G :EBP S1)) S1)
                                                           (* 4 (R32 (+ -32 (G :EBP S1)) S1)))))
                                        :F-ZF
                                        (ZF (+ (R32 (+ 8 (G :EBP S1)) S1)
                                               (* 4 (R32 (+ -32 (G :EBP S1)) S1))))
                                        :IMME1
                                        0 :VALU1 (R32 (+ 8 (G :EBP S1)) S1)
                                        (UPDATE-MEM (+ -28 (G :EBP S1))
                                                    0 (+ -36 (G :EBP S1))
                                                    (R32 (+ (R32 (+ 8 (G :EBP S1)) S1)
                                                            (* 4 (R32 (+ -32 (G :EBP S1)) S1)))
                                                         S1)
                                                    S1)))
                          ((and (equal (g :eip s1)
                                       (+ *L7* (snpt-code-location)))
                                (< 3 (r32 (+ -32 (g :ebp s1)) s1)))
                           ;; exit outer loop
                           (UPDATE-REGS   :EBP (R32 (G :EBP S1) S1)
                                          :EBX (R32 (+ 48 (G :ESP S1)) S1)
                                          :EIP (R32 (+ 4 (G :EBP S1)) S1)
                                          :ESI (R32 (+ 52 (G :ESP S1)) S1)
                                          :ESP (+ 8 (G :EBP S1))
                                          :F-CF
                                          (CF (+ 48 (G :ESP S1))
                                              (+ 48 (G :ESP S1)))
                                          :F-OF
                                          (OF (N32-TO-I32 (+ 48 (G :ESP S1)))
                                              (+ 48 (N32-TO-I32 (G :ESP S1))))
                                          :F-SF
                                          (SF (N32-TO-I32 (+ 48 (G :ESP S1))))
                                          :F-ZF (ZF (+ 48 (G :ESP S1)))
                                          :IMME1 3 :VALU1 48 S1))
                          ((and (equal (g :eip s1)
                                       (+ *L9* (snpt-code-location)))
                                (<= (r32 (+ -28 (g :ebp s1)) s1) 511))
                           ;; stay in inner loop
                           (UPDATE-REGS :EAX 2097152
                                        :EBX (R32 (+ -20 (G :EBP S1)) S1)
                                        :ECX (R32 (+ -24 (G :EBP S1)) S1)
                                        :EDX 0 :EIP (+ 614 (SNPT-CODE-LOCATION))
                                        :ESI
                                        (+ (R32 (+ -36 (G :EBP S1)) S1)
                                           (* 8 (R32 (+ -28 (G :EBP S1)) S1)))
                                        :F-CF
                                        (CF (+ 1 (R32 (+ -28 (G :EBP S1)) S1))
                                            (+ 1 (R32 (+ -28 (G :EBP S1)) S1)))
                                        :F-OF
                                        (OF (+ 1 (R32 (+ -28 (G :EBP S1)) S1))
                                            (+ 1 (R32 (+ -28 (G :EBP S1)) S1)))
                                        :F-SF
                                        (SF (+ 1 (R32 (+ -28 (G :EBP S1)) S1)))
                                        :F-ZF
                                        (ZF (+ 1 (R32 (+ -28 (G :EBP S1)) S1)))
                                        :IMME1 1 :VALU1
                                        (+ 1 (R32 (+ -28 (G :EBP S1)) S1))
                                        (UPDATE-MEM (+ -28 (G :EBP S1))
                                                    (+ 1 (R32 (+ -28 (G :EBP S1)) S1))
                                                    (+ -44 (G :EBP S1))
                                                    (if (and (equal (R32 (+ -32 (G :EBP S1)) S1)
                                                                    3)
                                                             (equal (R32 (+ -28 (G :EBP S1)) S1)
                                                                    511))
                                                        1
                                                      0)
                                                    (+ -48 (G :EBP S1))
                                                    (if (and (equal (R32 (+ -32 (G :EBP S1)) S1)
                                                                    3)
                                                             (equal (R32 (+ -28 (G :EBP S1)) S1)
                                                                    511))
                                                        0
                                                      (+ 2097152 (R32 (+ -48 (G :EBP S1)) S1)))
                                                    (+ (R32 (+ -36 (G :EBP S1)) S1)
                                                       (* 8 (R32 (+ -28 (G :EBP S1)) S1)))
                                                    (LOGIOR (R32 (+ -24 (G :EBP S1)) S1)
                                                            (R32 (+ -48 (G :EBP S1)) S1))
                                                    (+ 4 (R32 (+ -36 (G :EBP S1)) S1)
                                                       (* 8 (R32 (+ -28 (G :EBP S1)) S1)))
                                                    (R32 (+ -20 (G :EBP S1)) S1)
                                                    S1)))
                          ((and (equal (g :eip s1)
                                       (+ *L9* (snpt-code-location)))
                                (< 511 (r32 (+ -28 (g :ebp s1)) s1)))
                           ;; exit inner loop
                           (UPDATE-REGS :EIP (+ 653 (SNPT-CODE-LOCATION))
                                        :F-CF
                                        (CF (+ 1 (R32 (+ -32 (G :EBP S1)) S1))
                                            (+ 1 (R32 (+ -32 (G :EBP S1)) S1)))
                                        :F-OF
                                        (OF (+ 1 (R32 (+ -32 (G :EBP S1)) S1))
                                            (+ 1 (R32 (+ -32 (G :EBP S1)) S1)))
                                        :F-SF
                                        (SF (+ 1 (R32 (+ -32 (G :EBP S1)) S1)))
                                        :F-ZF
                                        (ZF (+ 1 (R32 (+ -32 (G :EBP S1)) S1)))
                                        :IMME1 1 :VALU1
                                        (+ 1 (R32 (+ -32 (G :EBP S1)) S1))
                                        (UPDATE-MEM (+ -32 (G :EBP S1))
                                                    (+ 1 (R32 (+ -32 (G :EBP S1)) S1))
                                                    S1)))
                          (t
                           'NIL))))
    :hints (("Goal" :in-theory (disable MOD-BOUNDS-1
                                        N32+-WHEN-WORD-ALIGNED
                                        |(word-aligned-p x)|
                                        INIT_PDPT-LOADED-THM-32
                                        CREATE_NESTED_PT-LOADED-THM-32
                                        SEC_NOT_PRESENT-LOADED-THM-32
                                        |(mod (+ x y) z) where (<= 0 z)|
                                        CANCEL-MOD-+
                                        )
             :do-not '(generalize eliminate-destructors fertilize)))
    :otf-flg t))

 (local
  (set-default-hints nil))

 (local
  (in-theory (disable |(y86-step st)|
                      |(logior 1 x)|)))

 (local
  (defun assertion-invariant-default-hint-1 (hyps)
    (cond ((endp hyps)
           (mv nil nil))                ; should be error
          ((and (equal (fn-symb (car hyps)) 'NOT)
                (equal (fn-symb (arg1 (car hyps))) 'EQUAL)
                (equal (fn-symb (arg1 (arg1 (car hyps)))) 'S)
                (equal (arg2 (arg1 (car hyps))) 'S1))
           (mv (cdr hyps) (arg1 (arg1 (car hyps)))))
          ((and (equal (fn-symb (car hyps)) 'NOT)
                (equal (fn-symb (arg1 (car hyps))) 'EQUAL)
                (equal (fn-symb (arg2 (arg1 (car hyps)))) 'S)
                (equal (arg1 (arg1 (car hyps))) 'S1))
           (mv (cdr hyps) (arg2 (arg1 (car hyps)))))
          (t
           (mv-let (new-hyps s1-subst)
                   (assertion-invariant-default-hint-1 (cdr hyps))
                   (mv (cons (car hyps) new-hyps)
                       s1-subst))))))

 (local
  (defun assertion-invariant-default-hint (stable-under-simplificationp clause world)
    (declare (xargs :mode :program))
    (if stable-under-simplificationp
        (b* ((concl (car (last clause)))
             ((mv new-hyps s1-subst)
              (assertion-invariant-default-hint-1 (butlast clause 1)))
             (concl-vars (all-vars concl))
             (new-concl `((LAMBDA ,concl-vars ,concl) ,@(subst s1-subst 's1 concl-vars)))
             (instance (prettyify-clause (append new-hyps
                                                 (list new-concl))
                                         nil world)))
            `(:use ((:instance
                     (:theorem ,instance)))
                   ;; :expand ((INIT_PDTS-MODIFY-LOOP-1 (R32 (+ -20 (G :EBP S1)) S1)
                   ;;                                  S0))
                   ))
      nil)))


 (local
  (set-default-hints '((assertion-invariant-default-hint stable-under-simplificationp
                                                         clause
                                                         world))))


;;; !!!Grossly slow!!!
;;; 2300+ subgoals, 22+ minutes
;;; now 4150 seconds


 (LOCAL (DEFTHM $$$ASSERTION-INVARIANT-OVER-CUTPOINTS
          (IMPLIES (AND (INIT_PDTS-ASSERTION S0 S1)
                        (IN-SUB S1)
                        (LET* ((S1 (Y86 S1 N)))
                              (NOT (IN-SUB S1))))
                   (LET* ((S1 (Y86-STEP S1))
                          (S1 ($$$NEXT-CUTPOINT-MAIN S1)))
                         (INIT_PDTS-ASSERTION S0 S1)))
          :RULE-CLASSES NIL
          :HINTS (("Goal" :in-theory (disable INIT_PDTS-LOADED-THM-32
                                              INIT_PDPT-LOADED-THM-32
                                              CREATE_NESTED_PT-LOADED-THM-32
                                              SEC_NOT_PRESENT-LOADED-THM-32)
                   :do-not '(generalize eliminate-destructors fertilize)))
          :otf-flg t))

 (local
  (set-default-hints nil))

 (LOCAL (IN-THEORY (THEORY 'GROUND-ZERO)))
 (DEFP EXITSTEPS-TAIL (S1 I)
   (IF (NOT (IN-SUB S1))
       I
       (LET* ((S1 (Y86-STEP S1)))
             (EXITSTEPS-TAIL S1 (1+ I)))))
 (DEFUN EXITSTEPS (S1)
   (LET* ((STEPS (EXITSTEPS-TAIL S1 0))
          (S1 (Y86 S1 STEPS)))
         (IF (NOT (IN-SUB S1))
             STEPS (OMEGA))))
 (DEFUN-SK EXISTS-NEXT-EXITPOINT (S1)
   (EXISTS N
           (LET* ((S1 (Y86 S1 N)))
                 (NOT (IN-SUB S1)))))
 (DEFUN NEXT-EXITPOINT (S1)
   (LET* ((STEPS (EXITSTEPS S1)))
         (Y86 S1 STEPS)))
 (LOCAL (IN-THEORY (THEORY 'MINIMAL-THEORY)))
 (DEFTHM
   INIT_PDTS-CORRECT
   (IMPLIES (AND (INIT_PDTS-PRE S1)
                 (EXISTS-NEXT-EXITPOINT S1))
            (AND (LET ((S1 (NEXT-EXITPOINT S1)))
                      (NOT (IN-SUB S1)))
                 (EQUAL (NEXT-EXITPOINT S1)
                        (INIT_PDTS-MODIFY S1))))
   :OTF-FLG T
   :RULE-CLASSES NIL
   :HINTS
   (("Goal"
     :USE
     ((:INSTANCE
       (:FUNCTIONAL-INSTANCE
        |epc composite partial correctness|
        (EPC-NEXT (LAMBDA (S)
                          (LET ((S1 S)) (Y86-STEP S1))))
        (EPC-RUN (LAMBDA (S N) (Y86 S N)))
        (EXISTS-EPC-NEXT-CUTPOINT
         (LAMBDA (S)
                 (LET ((S1 S))
                      ($$$EXISTS-NEXT-CUTPOINT S1))))
        (EXISTS-EPC-NEXT-CUTPOINT-WITNESS
         (LAMBDA (S)
                 (LET ((S1 S))
                      ($$$EXISTS-NEXT-CUTPOINT-WITNESS S1))))
        (EPC-PRE-SUB (LAMBDA (S)
                             (LET ((S1 S)) ($$$PRESUB S1))))
        (EPC-IN-SUB (LAMBDA (S)
                            (LET ((S1 S)) ($$$INSUB S1))))
        (EPC-EXISTS-EXITPOINT-SUB
         (LAMBDA (S)
                 (LET ((S1 S))
                      ($$$EXISTS-EXITPOINT-SUB S1))))
        (EPC-EXISTS-EXITPOINT-SUB-WITNESS
         (LAMBDA (S)
                 (LET ((S1 S))
                      ($$$EXISTS-EXITPOINT-SUB-WITNESS S1))))
        (EPC-STEPS-TO-EXITPOINT-TAIL-SUB
         (LAMBDA (S I)
                 (LET ((S1 S))
                      ($$$STEPS-TO-EXITPOINT-SUB-TAIL S1 I))))
        (EPC-MODIFY-SUB (LAMBDA (S)
                                (LET ((S1 S)) ($$$MODIFYSUB S1))))
        (EPC-NEXT-EXITPOINT-SUB (LAMBDA (S)
                                        (LET ((S1 S))
                                             ($$$NEXT-EXITPOINT-SUB S1))))
        (EPC-STEPS-TO-EXITPOINT-SUB
         (LAMBDA (S)
                 (LET ((S1 S))
                      ($$$STEPS-TO-EXITPOINT-SUB S1))))
        (EPC-PRE-MAIN (LAMBDA (S)
                              (LET ((S1 S)) (INIT_PDTS-PRE S1))))
        (EPC-CUTPOINT-MAIN (LAMBDA (S)
                                   (LET ((S1 S))
                                        (INIT_PDTS-CUTPOINT-P S1))))
        (EPC-EXISTS-EXITPOINT-MAIN
         (LAMBDA (S)
                 (LET ((S1 S))
                      (EXISTS-NEXT-EXITPOINT S1))))
        (EPC-EXISTS-EXITPOINT-MAIN-WITNESS
         (LAMBDA (S)
                 (LET ((S1 S))
                      (EXISTS-NEXT-EXITPOINT-WITNESS S1))))
        (EPC-NEXT-EXITPOINT-MAIN
         (LAMBDA (S)
                 (LET ((S1 S)) (NEXT-EXITPOINT S1))))
        (EPC-EXITSTEPS-MAIN (LAMBDA (S)
                                    (LET ((S1 S)) (EXITSTEPS S1))))
        (EPC-EXITSTEPS-MAIN-TAIL
         (LAMBDA (S I)
                 (LET ((S1 S)) (EXITSTEPS-TAIL S1 I))))
        (EPC-IN-MAIN (LAMBDA (S)
                             (LET ((S1 S)) (IN-SUB S1))))
        (EPC-NEXT-EPC-CUTPOINT-MAIN
         (LAMBDA (S)
                 (LET ((S1 S))
                      ($$$NEXT-CUTPOINT-MAIN S1))))
        (EPC-ASSERTION-MAIN (LAMBDA (S0 S)
                                    (LET ((S0 S0) (S1 S))
                                         (INIT_PDTS-ASSERTION S0 S1))))
        (EPC-MODIFY-MAIN (LAMBDA (S)
                                 (LET ((S1 S)) (INIT_PDTS-MODIFY S1)))))
       (S S1))))
    ("Subgoal 17" :USE ((:INSTANCE $$$ASSERTION-INVARIANT-OVER-CUTPOINTS
                                   (S0 S0)
                                   (S1 S))))
    ("Subgoal 16" :USE ((:INSTANCE $$$ASSERTION-MAIN-IMPLIES-POST (S0 S0)
                                   (S1 S))))
    ("Subgoal 15" :USE ((:INSTANCE $$$PRE-IMPLIES-ASSERTION (S1 S))))
    ("Subgoal 14" :USE ((:INSTANCE $$$ASSERTION-IMPLIES-CUTPOINT (S0 S0)
                                   (S1 S))))
    ("Subgoal 13" :USE ((:INSTANCE $$$PRESUB-IMPLIES-INSUB (S1 S))))
    ("Subgoal 12" :USE ((:INSTANCE $$$IN-SUB-IMPLIES-IN-MAIN (S1 S))))
    ("Subgoal 11" :USE ((:INSTANCE $$$NO-MAIN-CUTPOINT-IN-SUB (S1 S))))
    ("Subgoal 10" :USE ((:INSTANCE (:DEFINITION $$$EXISTS-NEXT-CUTPOINT)
                                   (S1 S))))
    ("Subgoal 9" :USE ((:INSTANCE $$$EXISTS-NEXT-CUTPOINT-SUFF (S1 S))))
    ("Subgoal 8" :USE ((:INSTANCE $$$NEXT-CUTPOINT-MAIN$DEF (S1 S))))

    ("Subgoal 7" :USE ((:INSTANCE $$$CORRECTNESS-OF-SUB (S1 S))))
    ("Subgoal 6" :USE ((:INSTANCE $$$STEPS-TO-EXITPOINT-SUB-TAIL$DEF
                                   (S1 S))))
    ("Subgoal 5" :USE ((:INSTANCE (:DEFINITION $$$EXISTS-EXITPOINT-SUB)
                                   (S1 S))))
    ("Subgoal 4" :USE ((:INSTANCE $$$EXISTS-EXITPOINT-SUB-SUFF (S1 S))))
    ("Subgoal 3" :USE ((:INSTANCE (:DEFINITION $$$NEXT-EXITPOINT-SUB)
                                  (S1 S))))
    ("Subgoal 2" :USE ((:INSTANCE (:DEFINITION $$$STEPS-TO-EXITPOINT-SUB)
                                  (S1 S))))
    ("Subgoal 1" :IN-THEORY (ENABLE Y86))))
 )

#||
(defsimulate+
  y86-step
  :run y86
  :inmain in-sub
  :cutpoint init_pdts-cutpoint-p
  :assertion-params (s0 s1)
  :precondition init_pdts-pre
  :assertion init_pdts-assertion
  :modify init_pdts-modify

  :exitsteps exitsteps
  :exists-next-exitpoint exists-next-exitpoint
  :next-exitpoint next-exitpoint

  :correctness-theorem init_pdts-correct)
||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; sec_not_present

;;; mark those portions of memory occupied by sec_visor as not
;;; present.

(defun in-sec_not_present (s)
  (let ((eip (g :eip s)))
    (and (<= (+ *SEC_NOT_PRESENT* (snpt-code-location)) eip)
         (< eip (+ *INIT_PDTS* (snpt-code-location))))))

;;; but we need to have only one in-sub for everything
;;; repeat from init_pdpt
(defun in-sub (s)
  (let ((eip (g :eip s)))
    (and (<= (+ *SEC_NOT_PRESENT* (snpt-code-location)) eip)
         (< eip (+ *CREATE_NESTED_PT* (snpt-code-location))))))

(defun sec_not_present-cutpoint-p (s)
  (let ((eip (g :eip s)))
    (or (equal eip (+ *SEC_NOT_PRESENT* (snpt-code-location))) ; start
        (equal eip (+ *L2* (snpt-code-location)))              ; loop test
        (not (in-sub s)))))                        ; exit

(defun sec_not_present-pre (s)
  (and (good-state-p s)
       (equal (g :eip s) (+ *SEC_NOT_PRESENT* (snpt-code-location)))
       (not (paging-p s))
       (disjointp
        (list (range (snpt-code-location) 0 993)              ; code
              (range (g :esp s) -56 76)                       ; stack
              (range (r32 (+ 4 (g :esp s)) s) 0 (* 4 8))      ; pdpt
              (range (logand (r32 (+ (r32 (+ 4 (g :esp s)) s) ; pdt
                                     (* 8 (ash (r32 (+ 8 (g :esp s)) s) -30)))
                                  s)
                             (lognot (+ -1 (expt 2 12))))
                     0
                     (* 512 8))))
       ;; all stack addresses are "good" --- the stack does not wrap around memory
       (n32p (+ -60 (g :esp s)))
       (n32p (+ 19 (g :esp s)))
       ;; addresses in pdt pointer array are "good"
       (n32p (+ 31 (r32 (+ 4 (g :esp s)) s)))
       ;; visor_start + visor_size fits into 32 bits
       (n32p (+ (R32 (+ 8 (G :ESP S)) S)
                (R32 (+ 12 (G :ESP S)) S)))
       ;; all of visor's memory lies within one PDT
       (equal (ash (+ (R32 (+ 8 (G :ESP S)) S)
                      (R32 (+ 12 (G :ESP S)) S))
                   -30)
              (ash (R32 (+ 8 (G :ESP S)) S)
                   -30))
       ;; 0 < visor_size
       (< 0 (R32 (+ 12 (G :ESP S)) S))
       ;; addresses in the pdt are "good"
       (n32p (+ 4095 (logand (r32 (+ (r32 (+ 4 (g :esp s)) s)
                                     (* 8 (ash (r32 (+ 8 (g :esp s)) s) -30)))
                                  s)
                             (lognot (+ -1 (expt 2 12))))))
       ;; we return to create_nested_pt
       (< (+ *CREATE_NESTED_PT* (snpt-code-location)) (R32 (g :esp s) S))
       ;; A few more hyps found to be usefull --- about visor_start
       ;; and visor_size
       (not (EQUAL (ASH (LOGAND 1071644672
                                (+ (R32 (+ 8 (G :ESP S)) S)
                                   (R32 (+ 12 (G :ESP S)) S)))
                        -21)
                   (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S)) S))
                        -21)))
       (<= 1
           (ASH (LOGAND 1071644672
                        (+ (R32 (+ 8 (G :ESP S)) S)
                           (R32 (+ 12 (G :ESP S)) S)))
                -21))
       (n32p (+ 7 (* 8
                     (+ -1
                        (ASH (LOGAND 1071644672
                                     (+ (R32 (+ 8 (G :ESP S)) S)
                                        (R32 (+ 12 (G :ESP S)) S)))
                             -21)))
                (LOGAND 4294963200
                        (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                (* 8
                                   (ASH (R32 (+ 8 (G :ESP S)) S)
                                        -30)))
                             S))))))

(defun sec_not_present-loop-pre (s0 s)
  (and (good-state-p s)
       (equal (g :eip s) (+ *L2* (snpt-code-location)))
       (not (paging-p s))
       (disjointp
        (list (range (snpt-code-location) 0 993)               ; code
              (range (+ 4 (g :ebp s)) -56 76)                  ; stack
              (range (r32 (+ 4 (+ 4 (g :ebp s))) s) 0 (* 4 8)) ; pdpt
              (range (logand (r32 (+ (r32 (+ 4 (+ 4 (g :ebp s))) s)      ; pdt
                                     (* 8 (ash (r32 (+ 8 (+ 4 (g :ebp s))) s) -30)))
                                  s)
                                  (lognot (+ -1 (expt 2 12))))
                     0
                     (* 512 8))))
       ;; all stack addresses are "good" --- the stack does not wrap around memory
       (n32p (+ -60 (+ 4 (g :ebp s))))
       (n32p (+ 19 (+ 4 (g :ebp s))))
       ;; addresses in pdt pointer array are "good"
       (n32p (+ 31 (r32 (+ 4 (+ 4 (g :ebp s))) s)))
       ;; visor_start + visor_size fits into 32 bits
       (n32p (+ (R32 (+ 8 (+ 4 (g :ebp s))) S)
                (R32 (+ 12 (+ 4 (g :ebp s))) S)))
       ;; 0 < visor_size
       (< 0 (R32 (+ 12 (+ 4 (g :ebp s))) S))
       ;; addresses in the pdt are "good"
       (n32p (+ 4095 (logand (r32 (+ (r32 (+ 4 (+ 4 (g :ebp s))) s)
                                     (* 8 (ash (r32 (+ 8 (+ 4 (g :ebp s))) s) -30)))
                                  s)
                             (lognot (+ -1 (expt 2 12))))))
       ;; we return to create_nested_pt
       (< (+ *CREATE_NESTED_PT* (snpt-code-location)) (R32 (+ 4 (g :ebp s)) S))
       ;; the alignment of :esp and :ebp --- why do we need this?
       (equal (g :esp s) (+ -48 (g :ebp s)))
       ;;; input parameters unchanged
       (equal (R32 (+ 8 (G :EBP S)) S)
              (R32 (+ 4 (G :ESP S0)) S0))
       (equal (R32 (+ 12 (G :EBP S)) S)
              (R32 (+ 8 (G :ESP S0)) S0))
       (equal (R32 (+ 16 (G :EBP S)) S)
              (R32 (+ 12 (G :ESP S0)) S0))
       ;; end
       (equal (r32 (+ -24 (+ 4 (g :ebp s))) s)
              (ASH (LOGAND 1071644672
                           (+ (R32 (+ 8 (+ 4 (g :ebp s))) S)
                              (R32 (+ 12 (+ 4 (g :ebp s))) S)))
                   -21))
       ;; start
       (equal (r32 (+ -28 (+ 4 (g :ebp s))) s)
              (ASH (LOGAND 1071644672 (R32 (+ 8 (+ 4 (g :ebp s))) S))
                   -21))
       ;; pdt
       (equal (r32 (+ -32 (+ 4 (g :ebp s))) s)
              (LOGAND 4294963200
                      (R32 (+ (* 8 (ASH (R32 (+ 8 (+ 4 (g :ebp s))) S) -30))
                              (R32 (+ 4 (+ 4 (g :ebp s))) S))
                           S)))
       ;; we are in the loop, start <= i <= end
       (<= (r32 (+ -28 (+ 4 (g :ebp s))) s) (r32 (+ -20 (+ 4 (g :ebp s))) s))
       (<= (r32 (+ -20 (+ 4 (g :ebp s))) s) (r32 (+ -24 (+ 4 (g :ebp s))) s))
       ;; end <= 512
       (<= (r32 (+ -24 (+ 4 (g :ebp s))) s) 512)
       ;; pdt points to a pdt
       (equal (r32 (+ -32 (+ 4 (g :ebp s))) s)
              (logand (r32 (+ (r32 (+ 4 (+ 4 (g :ebp s))) s)
                              (* 8 (ash (r32 (+ 8 (+ 4 (g :ebp s))) s) -30)))
                           s)
                      (lognot (+ -1 (expt 2 12)))))))

;;; !!! Perhaps we should be counting up from start to end, as the C
;;; !!! code does.

(defun sec_not_present-modify-loop-1 (i s)
  (declare (xargs :measure (nfix (+ i
                                    (- (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S)) S))
                                            -21))))))
  (cond ((or (not (integerp i))
             (< i 0)
             (not (integerp (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S)) S))
                                 -21)))
             (< i
                (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S)) S))
                     -21))
             ;; equal end start)
             (equal (ASH (LOGAND 1071644672
                                 (+ (R32 (+ 8 (G :ESP S)) S)
                                    (R32 (+ 12 (G :ESP S)) S)))
                         -21)
                    (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S)) S))
                         -21)))
         s)
        ((equal i
                (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S)) S))
                     -21))
         (update-mem (+ (* 8 i)
                        (LOGAND 4294963200
                                (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                        (R32 (+ 4 (G :ESP S)) S))
                                     S)))
                     0
                     (+ 4
                        (* 8 i)
                        (LOGAND 4294963200
                                (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                        (R32 (+ 4 (G :ESP S)) S))
                                     S)))
                     0
                     s))
        (t
         (update-mem (+ (* 8 i)
                        (LOGAND 4294963200
                                (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                        (R32 (+ 4 (G :ESP S)) S))
                                     S)))
                     0
                     (+ 4
                        (* 8 i)
                        (LOGAND 4294963200
                                (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                        (R32 (+ 4 (G :ESP S)) S))
                                     S)))
                     0
                     (sec_not_present-modify-loop-1 (+ -1 i) s)))))



(defthm |(paging-p (sec_not_present-modify-loop-1 i s))|
  (equal (paging-p (sec_not_present-modify-loop-1 i s))
         (paging-p s)))

(defthm |(va-to-pa addr (sec_not_present-modify-loop-1 i s))|
  (implies (not (paging-p s))
           (equal (va-to-pa addr (sec_not_present-modify-loop-1 i s))
                  (va-to-pa addr s))))

(defthm |(good-32-address-p addr (sec_not_present-modify-loop-1 i s))|
  (implies (not (paging-p s))
           (equal (good-32-address-p addr (sec_not_present-modify-loop-1 i s))
                  (good-32-address-p addr s)))
  :hints (("Goal" :in-theory (enable good-32-address-p))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm |(G field (sec_not_present-modify-loop-1 i s))|
   (implies (not (equal field :mem))
            (equal (G field (sec_not_present-modify-loop-1 i s))
                   (g field s))))

 (defthm |(y86-p (sec_not_present-modify-loop-1 i s))|
   (implies (and (y86-p s)
                 (integerp i)
                 (n32p (+ 4 (* 8 I)
                          (LOGAND 4294963200
                                  (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                          (* 8
                                             (ASH (R32 (+ 8 (G :ESP S)) S)
                                                    -30)))
                                       S)))))
            (y86-p  (sec_not_present-modify-loop-1 i s)))
   :hints (("Goal" :in-theory (enable y86-p
                                      Y86-REGISTER-GUARD
                                      Y86-SUPERVISOR-GUARD
                                      Y86-FLAGS-GUARD
                                      Y86-MISC-GUARD
                                      ))))

 (defthm |(memoryp (g :mem (sec_not_present-modify-loop-1 i s)))|
   (implies (and (y86-p s)
                 (integerp i)
                 (n32p (+ 4 (* 8 I)
                          (LOGAND 4294963200
                                  (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                          (* 8
                                             (ASH (R32 (+ 8 (G :ESP S)) S)
                                                    -30)))
                                       S)))))
            (memoryp (g :mem (sec_not_present-modify-loop-1 i s)))))


 (defthm |(good-state-p (sec_not_present-modify-loop-1 i s))|
   (implies (and (good-state-p s)
                 (not (paging-p s))
                 (integerp i)
                 (<= 0 i)
                 (< i 512)
                 (n32p (+ 4 (* 8 I)
                          (LOGAND 4294963200
                                  (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                          (* 8
                                             (ASH (R32 (+ 8 (G :ESP S)) S)
                                                    -30)))
                                       S))))
                 (disjointp (LIST (range (snpt-code-location) 0 993)
                                  (RANGE
                                   (LOGAND 4294963200
                                           (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                                   (* 8
                                                      (ASH (R32 (+ 8 (G :ESP S)) S)
                                                           -30)))
                                                S))
                                   0 (* 512 8)))))
            (good-state-p (sec_not_present-modify-loop-1 i s)))
   :hints (("Goal" :do-not '(generalize eliminate-destructors))))

 (defthm |(r32 addr (sec_not_present-modify-loop-1 i s))|
   (implies (and (y86-p s)
                 (not (paging-p s))
                 (integerp i)

                 (n32p addr)
                 (n32p (+ 3 addr))
                 (n32p (+ 7 (* 8 I)
                          (LOGAND 4294963200
                                  (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                          (* 8
                                             (ASH (R32 (+ 8 (G :ESP S)) S)
                                                  -30)))
                                       S))))
                 (disjointp (list (range addr 0 4)
                                  ;; (range (+ (R32 (+ 4 (G :ESP S)) S)
                                  ;;          (* 8
                                  ;;              (ASH (R32 (+ 8 (G :ESP S)) S)
                                  ;;                   -30)))
                                  ;;        0 4)
                                  (range (LOGAND 4294963200
                                                 (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                                         (* 8
                                                            (ASH (R32 (+ 8 (G :ESP S)) S)
                                                                 -30)))
                                                      S))
                                         (* 8 (ASH (LOGAND 1071644672
                                                           (R32 (+ 8 (G :ESP S)) S))
                                                   -21))
                                         (+ 8
                                            (* 8
                                               (max 0
                                                    (- i (ASH (LOGAND 1071644672
                                                                      (R32 (+ 8 (G :ESP S)) S))
                                                              -21)))))))))
            (equal (r32 addr (sec_not_present-modify-loop-1 i s))
                   (r32 addr s)))
   :hints (("Goal" :do-not '(generalize)
            :in-theory (disable the-floor-above the-floor-below))
           ("Subgoal *1/7" :use ((:instance |(memoryp (g :mem (sec_not_present-modify-loop-1 i s)))|
                                            (i (+ -1 i))
                                            (s s))))))

 (defthm |(r32 addr (sec_not_present-modify-loop-1 i s)) --- written to 1|
   (implies (and (y86-p s)
                 (not (paging-p s))
                 (integerp i)
                 (<= 0 i)
                 (not (EQUAL (ASH (LOGAND 1071644672
                                          (+ (R32 (+ 8 (G :ESP S)) S)
                                             (R32 (+ 12 (G :ESP S)) S)))
                                  -21)
                             (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S)) S))
                                  -21)))
                 (n32p (+ 7 (* 8 I)
                          (LOGAND 4294963200
                                  (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                          (* 8
                                             (ASH (R32 (+ 8 (G :ESP S)) S)
                                                  -30)))
                                       S))))
                 (integerp i-prime)
                 (<= (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S)) S))
                          -21)
                     i-prime)
                 (<= i-prime i))
            (equal (r32 (+ (* 8 i-prime)
                           (LOGAND 4294963200
                                   (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                           (R32 (+ 4 (G :ESP S)) S))
                                        S)))
                        (sec_not_present-modify-loop-1 i s))
                   0))
   :hints (("Goal" :do-not '(generalize))
           ("Subgoal *1/7" :cases ((equal i i-prime))
                           :use ((:instance |(memoryp (g :mem (sec_not_present-modify-loop-1 i s)))|
                                             (i (+ -1 i))
                                             (s s))))
           ("Subgoal *1/6" :use ((:instance |(memoryp (g :mem (sec_not_present-modify-loop-1 i s)))|
                                             (i (+ -1 i))
                                             (s s))))
           ("Subgoal *1/2" :cases ((equal i i-prime)))))

 (defthm |(r32 addr (sec_not_present-modify-loop-1 i s)) --- written to 2|
   (implies (and (y86-p s)
                 (not (paging-p s))
                 (integerp i)
                 (<= 0 i)
                 (not (EQUAL (ASH (LOGAND 1071644672
                                          (+ (R32 (+ 8 (G :ESP S)) S)
                                             (R32 (+ 12 (G :ESP S)) S)))
                                  -21)
                             (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S)) S))
                                  -21)))
                 (n32p (+ 7 (* 8 I)
                          (LOGAND 4294963200
                                  (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                          (* 8
                                             (ASH (R32 (+ 8 (G :ESP S)) S)
                                                  -30)))
                                       S))))
                 (integerp i-prime)
                 (<= (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S)) S))
                          -21)
                     i-prime)
                 (<= i-prime i))
            (equal (r32 (+ 4
                           (* 8 i-prime)
                           (LOGAND 4294963200
                                   (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                           (R32 (+ 4 (G :ESP S)) S))
                                        S)))
                        (sec_not_present-modify-loop-1 i s))
                   0))
   :hints (("Goal" :do-not '(generalize))
           ("Subgoal *1/7" :cases ((equal i i-prime))
                           :use ((:instance |(memoryp (g :mem (sec_not_present-modify-loop-1 i s)))|
                                             (i (+ -1 i))
                                             (s s))))
           ("Subgoal *1/6" :use ((:instance |(memoryp (g :mem (sec_not_present-modify-loop-1 i s)))|
                                             (i (+ -1 i))
                                             (s s))))
           ("Subgoal *1/2" :cases ((equal i i-prime)))))

 (defthm |(sec_not_present-modify-loop-1 i (w32 addr val s))|
   (implies (and (y86-p s)
                 (not (paging-p s))
                 (integerp i)
                 (n32p addr)
                 (n32p (+ 3 addr))
                 (n32p (+ 15 (g :ESP S)))
                 (n32p (+ 3
                          (R32 (+ 4 (G :ESP S)) S)
                          (* 8
                             (FLOOR (R32 (+ 8 (G :ESP S)) S)
                                    1073741824))))
                 (n32p (+ 7 (* 8 I)
                          (LOGAND 4294963200
                                  (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                          (* 8
                                             (ASH (R32 (+ 8 (G :ESP S)) S)
                                                  -30)))
                                       S))))
                 (disjointp (list (range addr 0 4)
                                  (range (+ 4 (G :ESP S)) 0 12)
                                  (range (+ (R32 (+ 4 (G :ESP S)) S)
                                            (* 8
                                               (ASH (R32 (+ 8 (G :ESP S)) S)
                                                    -30)))
                                         0 4)
                                  (range (LOGAND 4294963200
                                                 (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                                         (* 8
                                                            (ASH (R32 (+ 8 (G :ESP S)) S)
                                                                 -30)))
                                                      S))
                                         0 (+ 8 (* 8 i))))))
            (equal (sec_not_present-modify-loop-1 i (w32 addr val s))
                   (w32 addr val (sec_not_present-modify-loop-1 i s))))
   :hints (("Goal" :do-not '(generalize))
           ("Subgoal *1/6" :use ((:instance |(memoryp (g :mem (sec_not_present-modify-loop-1 i s)))|
                                             (i (+ -1 i))
                                             (s s))))))
)


(defun sec_not_present-modify-loop (i cf of sf zf imme1 valu1 s)
  (declare (ignore imme1))
  (if (equal i
             (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S)) S))  ; start
                  -21))
      (UPDATE-REGS :EAX (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S)) S))
                             -21)
                   :EBP (+ -4 (G :ESP S))
                   :EDX (R32 (+ 4
                                (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                (R32 (+ 4 (G :ESP S)) S))
                             S)
                   :EIP (+ 313 (SNPT-CODE-LOCATION))
                   :ESP (+ -52 (G :ESP S))
                   :F-CF cf
                   :F-OF of
                   :F-SF sf
                   :F-ZF zf
;;;                   :IMME1 imme1
                   :IMME1 21
                   :VALU1 valu1
                   (UPDATE-MEM (+ -4 (G :ESP S))
                               (G :EBP S)

                               (+ -8 (G :ESP S))
                               4294967295

                               (+ -12 (G :ESP S))
                               4294963200

                               (+ -16 (G :ESP S))
                               (ASH (R32 (+ 8 (G :ESP S)) S) -30)

                               (+ -20 (G :ESP S))
                               i

                               (+ -24 (G :ESP S))
                               (ASH (LOGAND 1071644672
                                            (+ (R32 (+ 8 (G :ESP S)) S)
                                               (R32 (+ 12 (G :ESP S)) S)))
                                    -21)

                               (+ -28 (G :ESP S))
                               (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S)) S))
                                    -21)

                               (+ -32 (G :ESP S))
                               (LOGAND 4294963200
                                       (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                               (R32 (+ 4 (G :ESP S)) S))
                                            S))

                               (+ -36 (G :ESP S))
                               (LOGAND 4294963200
                                       (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                               (R32 (+ 4 (G :ESP S)) S))
                                            S))

                               (+ -40 (G :ESP S))
                               (R32 (+ 4
                                       (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                       (R32 (+ 4 (G :ESP S)) S))
                                    S)

                               (+ -44 (G :ESP S))
                               (LOGAND 4294963200
                                       (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                               (R32 (+ 4 (G :ESP S)) S))
                                            S))

                               (+ -48 (G :ESP S))
                               (R32 (+ 4
                                       (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                       (R32 (+ 4 (G :ESP S)) S))
                                    S)

                               (+ -52 (G :ESP S))
                               (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                       (R32 (+ 4 (G :ESP S)) S))
                                    S)

                               S))
    (let ((i (+ -1 i)))
    (UPDATE-REGS :EAX (+ (LOGAND 4294963200
                                 (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                         (R32 (+ 4 (G :ESP S)) S))
                                      S))
;;; !!!
;;; logand or below???
;;;                         (R32 (+ -28 (+ -4 (G :ESP S))) S)
                         (* 8 i))
                 :EBP (+ -4 (G :ESP S))
                 :EDX (R32 (+ 4
                              (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                              (R32 (+ 4 (G :ESP S)) S))
                           S)
                 :EIP (+ 313 (SNPT-CODE-LOCATION))
                 :ESP (+ -52 (G :ESP S))
                 :F-CF cf
                 :F-OF of
                 :F-SF sf
                 :F-ZF zf
;;;                 :IMME1 imme1
                 :IMME1 1
                 :VALU1 valu1
                 (UPDATE-MEM (+ -4 (G :ESP S))
                             (G :EBP S)

                             (+ -8 (G :ESP S))
                             4294967295

                             (+ -12 (G :ESP S))
                             4294963200

                             (+ -16 (G :ESP S))
                             (ASH (R32 (+ 8 (G :ESP S)) S) -30)

                             (+ -20 (G :ESP S))
                             (+ 1 i)

                             (+ -24 (G :ESP S))
                             (ASH (LOGAND 1071644672
                                          (+ (R32 (+ 8 (G :ESP S)) S)
                                             (R32 (+ 12 (G :ESP S)) S)))
                                  -21)

                             (+ -28 (G :ESP S))
                             (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S)) S))
                                  -21)

                             (+ -32 (G :ESP S))
                             (LOGAND 4294963200
                                     (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                             (R32 (+ 4 (G :ESP S)) S))
                                          S))

                             (+ -36 (G :ESP S))
                             (LOGAND 4294963200
                                     (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                             (R32 (+ 4 (G :ESP S)) S))
                                          S))

                             (+ -40 (G :ESP S))
                             (R32 (+ 4
                                     (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                     (R32 (+ 4 (G :ESP S)) S))
                                  S)

                             (+ -44 (G :ESP S))
                             (LOGAND 4294963200
                                     (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                             (R32 (+ 4 (G :ESP S)) S))
                                          S))

                             (+ -48 (G :ESP S))
                             (R32 (+ 4
                                     (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                     (R32 (+ 4 (G :ESP S)) S))
                                  S)

                             (+ -52 (G :ESP S))
                             (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                     (R32 (+ 4 (G :ESP S)) S))
                                  S)

                             (sec_not_present-modify-loop-1 i S))))))

(defun sec_not_present-modify (s)
  (let ((i (+ -1 (ASH (LOGAND 1071644672
                              (+ (R32 (+ 8 (G :ESP S)) S)
                                 (R32 (+ 12 (G :ESP S)) S)))
                      -21))))
  (UPDATE-REGS :EAX (+ 1 i)
                 :EBP (G :EBP S)
                 :EDX (R32 (+ 4
                              (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                              (R32 (+ 4 (G :ESP S)) S))
                           S)
                 :EIP (R32 (G :ESP S) S)
                 :ESP (+ 4 (G :ESP S))
                 :F-CF (subl-cf (+ 1 i) (+ 1 i))
                 :F-OF 0
                 :F-SF 0
                 :F-ZF 1
;;;                 :IMME1 1
                 :IMME1 (if (< (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S)) S))
                                    -21)  ;; i --- at first loop test
                               (ASH (LOGAND 1071644672
                                            (+ (R32 (+ 8 (G :ESP S)) S)
                                               (R32 (+ 12 (G :ESP S)) S)))
                                    -21))  ;; end
                            ;; we passed through the loop at least once
                            1
                          ;; we never entered the loop
                          21)
                 :VALU1 (+ 1 i)
                 (UPDATE-MEM (+ -4 (G :ESP S))
                             (G :EBP S)

                             (+ -8 (G :ESP S))
                             4294967295

                             (+ -12 (G :ESP S))
                             4294963200

                             (+ -16 (G :ESP S))
                             (ASH (R32 (+ 8 (G :ESP S)) S) -30)

                             (+ -20 (G :ESP S))
                             (+ 1 i)

                             (+ -24 (G :ESP S))
                             (ASH (LOGAND 1071644672
                                          (+ (R32 (+ 8 (G :ESP S)) S)
                                             (R32 (+ 12 (G :ESP S)) S)))
                                  -21)

                             (+ -28 (G :ESP S))
                             (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S)) S))
                                  -21)

                             (+ -32 (G :ESP S))
                             (LOGAND 4294963200
                                     (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                             (R32 (+ 4 (G :ESP S)) S))
                                          S))

                             (+ -36 (G :ESP S))
                             (LOGAND 4294963200
                                     (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                             (R32 (+ 4 (G :ESP S)) S))
                                          S))

                             (+ -40 (G :ESP S))
                             (R32 (+ 4
                                     (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                     (R32 (+ 4 (G :ESP S)) S))
                                  S)

                             (+ -44 (G :ESP S))
                             (LOGAND 4294963200
                                     (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                             (R32 (+ 4 (G :ESP S)) S))
                                          S))

                             (+ -48 (G :ESP S))
                             (R32 (+ 4
                                     (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                     (R32 (+ 4 (G :ESP S)) S))
                                  S)

                             (+ -52 (G :ESP S))
                             (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                     (R32 (+ 4 (G :ESP S)) S))
                                  S)

                             (sec_not_present-modify-loop-1 i S)))))



(defthm |(paging-p (sec_not_present-modify s))|
  (equal (paging-p (sec_not_present-modify s))
         (paging-p s)))

(defthm |(va-to-pa addr (sec_not_present-modify s))|
  (implies (not (paging-p s))
           (equal (va-to-pa addr (sec_not_present-modify s))
                  (va-to-pa addr s))))

(defthm |(good-32-address-p addr (sec_not_present-modify s))|
  (implies (not (paging-p s))
           (equal (good-32-address-p addr (sec_not_present-modify s))
                  (good-32-address-p addr s)))
  :hints (("Goal" :in-theory (enable good-32-address-p))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (local
  (encapsulate
   ()

   (local (include-book "arithmetic-5/top" :dir :system))

   (local
    (SET-DEFAULT-HINTS
     '((NONLINEARP-DEFAULT-HINT++ ID
                                  STABLE-UNDER-SIMPLIFICATIONP HIST NIL))))

   (defthm crock-100
     (implies (n32p x)
              (and (<= 0 (ash x -30))
                   (< (ash x -30) 4)))
     :rule-classes :linear)

   (defthm crock-101
     (implies (and (n32p x)
                   (integerp i)
                   (< i 0))
              (n32p (ash x i))))

   (defthm crock-102
     (implies (and (integerp i)
                   (<= 0 i)
                   (< i 512))
              (and (<= 0 (ash i 3))
                   (<= (ash i 3) 4088)))
     :rule-classes :linear)

   (defthm crock-103
     (implies (integerp x)
              (equal (ash x 3)
                     (* 8 x))))

   (defthm crock-200
     (implies (and (integerp x)
                   (n32p x))
              (equal (logand -4096 x)
                     (logand 4294963200 x)))
     :hints (("Goal" :use ((:instance
                            (:theorem
                             (equal (logand (logand x y) z)
                                    (logand x (logand y z))))
                            (x -4096)
                            (y (+ -1 (expt 2 32)))
                            (z x))))))

   (defthm crock-203
     (implies (and (integerp x)
                   (<= 0 x))
              (<= (ASH (LOGAND 1071644672
                               x)
                       -21)
                  512))
     :rule-classes :linear)

   (defthm crock-2000
     (implies (and (integerp x)
                   (<= 0 x))
              (<= 0
                  (ASH (LOGAND 1071644672
                               x)
                       -21))))

   (local
    (defthm crock-2001-3
      (implies (and (integerp x)
                    (<= 0 x))
               (equal (ASH (LOGAND 1071644672 x)
                           -21)
                      (ASH (logand (+ -1 (expt 2 30)) x)
                           -21)))
      :hints (("Goal" :use ((:instance logand-mask-shifted-2
                                       (n1 21)
                                       (n2 9)
                                       (c 1071644672)))))))

   (defthm crock-2001
     (implies (and (n32p x)
                   (n32p y)
                   (equal (ash (+ x y) -30)
                          (ash x -30)))
              (<= (ASH (LOGAND 1071644672 x)
                       -21)
                  (ASH (LOGAND 1071644672
                               (+ x
                                  y))
                       -21))))

   ))

  (defthm |(y86-p (sec_not_present-modify s))|
   (implies (and (sec_not_present-pre s)
                 )
            (y86-p  (sec_not_present-modify s)))
   :hints (("Goal" :in-theory (e/d (y86-p
                                      Y86-REGISTER-GUARD
                                      Y86-SUPERVISOR-GUARD
                                      Y86-FLAGS-GUARD
                                      Y86-MISC-GUARD)
                                   (|(y86-p (sec_not_present-modify-loop-1 i s))|
                                    ash-to-floor))
                    :use ((:instance |(y86-p (sec_not_present-modify-loop-1 i s))|
                                     (i (+ -1
                                           (ASH (LOGAND 1071644672
                                                        (+ (R32 (+ 8 (G :ESP S)) S)
                                                           (R32 (+ 12 (G :ESP S)) S)))
                                                -21)))
                                     (s s))))))

  (defthm |(memoryp (g :mem (sec_not_present-modify s)))|
   (implies (and (sec_not_present-pre s)
                 )
            (memoryp (g :mem (sec_not_present-modify s))))
   :hints (("Goal" :in-theory (e/d ()
                                   (|(memoryp (g :mem (sec_not_present-modify-loop-1 i s)))|
                                    ash-to-floor))
                    :use ((:instance |(memoryp (g :mem (sec_not_present-modify-loop-1 i s)))|
                                     (i (+ -1
                                           (ASH (LOGAND 1071644672
                                                        (+ (R32 (+ 8 (G :ESP S)) S)
                                                           (R32 (+ 12 (G :ESP S)) S)))
                                                -21)))
                                     (s s))))))

  (defthm |(good-state-p (sec_not_present-modify s))|
    (implies (and (sec_not_present-pre s)
                  )
             (good-state-p (sec_not_present-modify s)))
    :hints (("Goal" :in-theory (e/d ()
                                    (|(good-state-p (sec_not_present-modify-loop-1 i s))|
                                     ash-to-floor))
             :use ((:instance |(good-state-p (sec_not_present-modify-loop-1 i s))|
                              (i (+ -1
                                    (ASH (LOGAND 1071644672
                                                 (+ (R32 (+ 8 (G :ESP S)) S)
                                                    (R32 (+ 12 (G :ESP S)) S)))
                                         -21)))
                              (s s))))))

 (defthm |(memoryp (g :mem (sec_not_present-modify s)))|
   (implies (sec_not_present-pre s)
            (memoryp (g :mem (sec_not_present-modify s)))))

 (defthm |(g :cr0 (sec_not_present-modify s))|
   (implies (sec_not_present-pre s)
            (equal (g :cr0 (sec_not_present-modify s))
                   (G :cr0 S))))

 (defthm |(g :eip (sec_not_present-modify s))|
   (implies (sec_not_present-pre s)
            (equal (g :eip (sec_not_present-modify s))
                   (R32 (G :ESP S) S))))

 (defthm |(g :ebp (sec_not_present-modify s))|
   (implies (sec_not_present-pre s)
            (equal (g :ebp (sec_not_present-modify s))
                   (G :EBP S))))

 (defthm |(g :esp (sec_not_present-modify s))|
   (implies (sec_not_present-pre s)
            (equal (g :esp (sec_not_present-modify s))
                   (+ 4 (G :ESP S)))))

 (defthm |(r32 addr (sec_not_present-modify s))|
   (implies (and (sec_not_present-pre s)
                 (n32p addr)
                 (n32p (+ 3 addr))

                 (disjointp (list (range addr 0 4)
                                  (range (g :esp s) -56 56)
                                  (range (LOGAND 4294963200
                                                 (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                                         (* 8
                                                            (ASH (R32 (+ 8 (G :ESP S)) S)
                                                                 -30)))
                                                      S))
                                         (* 8
                                            (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S)) S))
                                                 -21))
                                         (+ 8
                                            (* 8 (MAX
                                                  0
                                                  (- (+ -1
                                                        (ASH (LOGAND 1071644672
                                                                     (+ (R32 (+ 8 (G :ESP S)) S)
                                                                        (R32 (+ 12 (G :ESP S)) S)))
                                                             -21))
                                                     (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S)) S))
                                                          -21)))))))))
            (equal (r32 addr (sec_not_present-modify s))
                   (r32 addr s)))
   :hints (("Goal" :in-theory (e/d ()
                                   (|(r32 addr (sec_not_present-modify-loop-1 i s))|
                                    ash-to-floor))
            :do-not '(generalize)
            :use ((:instance |(r32 addr (sec_not_present-modify-loop-1 i s))|
                             (i (+ -1
                                   (ASH (LOGAND 1071644672
                                                (+ (R32 (+ 8 (G :ESP S)) S)
                                                   (R32 (+ 12 (G :ESP S)) S)))
                                        -21)))
                             (s s)))))
   :otf-flg t)

 ;;; too many hyps!
 (defthm |(r32 addr (sec_not_present-modify s)) --- written to 1|
   (implies (and (sec_not_present-pre s)

                 (integerp i-prime)
                 (n32p (+ (* 8 I-PRIME)
                          (LOGAND 4294963200
                                  (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                          (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30)))
                                       S))))
                 (n32p (+ 3
                          (* 8 I-PRIME)
                          (LOGAND 4294963200
                                  (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                          (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30)))
                                       S))))
                 (<= (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S)) S))
                          -21)
                     i-prime)
                 (<= i-prime
                     (+ -1
                        (ASH (LOGAND 1071644672
                                     (+ (R32 (+ 8 (G :ESP S)) S)
                                        (R32 (+ 12 (G :ESP S)) S)))
                             -21)))
                 (disjointp (list (range (+ (* 8 I-PRIME)
                                            (LOGAND 4294963200
                                                    (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                                            (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30)))
                                                         S)))
                                         0
                                         4)
                                  (range (g :esp s) -56 56))))
            (equal (r32 (+ (* 8 i-prime)
                           (LOGAND 4294963200
                                   (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                           (R32 (+ 4 (G :ESP S)) S))
                                        S)))
                        (sec_not_present-modify s))
                   0))
   :hints (("Goal" :in-theory (e/d ()
                                   (|(r32 addr (sec_not_present-modify-loop-1 i s)) --- written to 1|
                                    ash-to-floor))
            :do-not '(generalize)
            :use ((:instance |(r32 addr (sec_not_present-modify-loop-1 i s)) --- written to 1|
                             (i (+ -1
                                   (ASH (LOGAND 1071644672
                                                (+ (R32 (+ 8 (G :ESP S)) S)
                                                   (R32 (+ 12 (G :ESP S)) S)))
                                        -21)))
                             (s s)))))
   :otf-flg t)

 ;;; too many hyps!
 (defthm |(r32 addr (sec_not_present-modify s)) --- written to 2|
   (implies (and (sec_not_present-pre s)

                 (integerp i-prime)
                 (n32p (+ (* 8 I-PRIME)
                          (LOGAND 4294963200
                                  (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                          (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30)))
                                       S))))
                 (n32p (+ 7
                          (* 8 I-PRIME)
                          (LOGAND 4294963200
                                  (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                          (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30)))
                                       S))))
                 (<= (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S)) S))
                          -21)
                     i-prime)
                 (<= i-prime
                     (+ -1
                        (ASH (LOGAND 1071644672
                                     (+ (R32 (+ 8 (G :ESP S)) S)
                                        (R32 (+ 12 (G :ESP S)) S)))
                             -21)))
                 (disjointp (list (range (+ 4
                                            (* 8 I-PRIME)
                                            (LOGAND 4294963200
                                                    (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                                            (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30)))
                                                         S)))
                                         0
                                         4)
                                  (range (g :esp s) -56 56))))
            (equal (r32 (+ 4
                           (* 8 i-prime)
                           (LOGAND 4294963200
                                   (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S)) S) -30))
                                           (R32 (+ 4 (G :ESP S)) S))
                                        S)))
                        (sec_not_present-modify s))
                   0))
   :hints (("Goal" :in-theory (e/d ()
                                   (|(r32 addr (sec_not_present-modify-loop-1 i s)) --- written to 2|
                                    ash-to-floor))
            :do-not '(generalize)
            :use ((:instance |(r32 addr (sec_not_present-modify-loop-1 i s)) --- written to 2|
                             (i (+ -1
                                   (ASH (LOGAND 1071644672
                                                (+ (R32 (+ 8 (G :ESP S)) S)
                                                   (R32 (+ 12 (G :ESP S)) S)))
                                        -21)))
                             (s s)))))
   :otf-flg t)
 )

(defun sec_not_present-assertion (s0 s1)
  (cond ((not (in-sub s1))
         ;; exit
         (equal s1 (sec_not_present-modify s0)))
        ((equal (g :eip s1)
                (+ *SEC_NOT_PRESENT* (snpt-code-location)))
         ;; start
         (and (sec_not_present-pre s1)
              (equal s1 s0)))
        ((equal (g :eip s1)
                (+ *L2* (snpt-code-location)))
         ;; loop
         (and (sec_not_present-pre s0)
              (sec_not_present-loop-pre s0 s1)
              (let ((i (r32 (+ -16 (g :ebp s1)) s1))
                    (cf (g :f-cf s1))
                    (of (g :f-of s1))
                    (sf (g :f-sf s1))
                    (zf (g :f-zf s1))
                    (imme1 (g :imme1 s1))
                    (valu1 (g :valu1 s1)))
                (equal s1 (sec_not_present-modify-loop i cf of sf zf imme1 valu1 s0)))))))



(ENCAPSULATE
 NIL

 ;; We need a few extra facts about ash
 (local
  (encapsulate
   ()

   (local (include-book "arithmetic-5/top" :dir :system))

   (local
    (SET-DEFAULT-HINTS
     '((NONLINEARP-DEFAULT-HINT++ ID
                                  STABLE-UNDER-SIMPLIFICATIONP HIST NIL))))

   (defthm crock-100
     (implies (n32p x)
              (and (<= 0 (ash x -30))
                   (< (ash x -30) 4)))
     :rule-classes :linear)

   (defthm crock-101
     (implies (and (n32p x)
                   (integerp i)
                   (< i 0))
              (n32p (ash x i))))

   (defthm crock-102
     (implies (and (integerp i)
                   (<= 0 i)
                   (< i 512))
              (and (<= 0 (ash i 3))
                   (<= (ash i 3) 4088)))
     :rule-classes :linear)

   (defthm crock-103
     (implies (integerp x)
              (equal (ash x 3)
                     (* 8 x))))

   (defthm crock-200
     (implies (and (integerp x)
                   (n32p x))
              (equal (logand -4096 x)
                     (logand 4294963200 x)))
     :hints (("Goal" :use ((:instance
                            (:theorem
                             (equal (logand (logand x y) z)
                                    (logand x (logand y z))))
                            (x -4096)
                            (y (+ -1 (expt 2 32)))
                            (z x))))))

   (defthm crock-203
     (implies (and (integerp x)
                   (<= 0 x))
              (<= (ASH (LOGAND 1071644672
                               x)
                       -21)
                  512)))

   (defthm crock-2000
     (implies (and (integerp x)
                   (<= 0 x))
              (<= 0
                  (ASH (LOGAND 1071644672
                               x)
                       -21))))

   (local
    (defthm crock-2001-3
      (implies (and (integerp x)
                    (<= 0 x))
               (equal (ASH (LOGAND 1071644672 x)
                           -21)
                      (ASH (logand (+ -1 (expt 2 30)) x)
                           -21)))
      :hints (("Goal" :use ((:instance logand-mask-shifted-2
                                       (n1 21)
                                       (n2 9)
                                       (c 1071644672)))))))

   (defthm crock-2001
     (implies (and (n32p x)
                   (n32p y)
                   (equal (ash (+ x y) -30)
                          (ash x -30)))
              (<= (ASH (LOGAND 1071644672 x)
                       -21)
                  (ASH (LOGAND 1071644672
                               (+ x
                                  y))
                       -21))))

   ))

 (LOCAL (DEFTHEORY USER-THEORY (CURRENT-THEORY :HERE)))
 (LOCAL
  (ENCAPSULATE
   NIL
   (LOCAL (DEFTHEORY $$$SUBTHEORY (CURRENT-THEORY :HERE)))
   (LOCAL (IN-THEORY (THEORY 'GROUND-ZERO)))
   (DEFUN-NX $$$INSUB (S1)
     (DECLARE (XARGS :NORMALIZE NIL))
     NIL)
   (DEFUN-NX $$$PRESUB (S1) NIL)
   (DEFUN-NX $$$MODIFYSUB (S1)
     (DECLARE (XARGS :NORMALIZE NIL))
     "Should never see this in a proof")
   (DEFTHM $$$NO-MAIN-CUTPOINT-IN-SUB
     (IMPLIES ($$$INSUB S1)
              (NOT (SEC_NOT_PRESENT-CUTPOINT-P S1)))
     :RULE-CLASSES NIL)
   (DEFTHM $$$IN-SUB-IMPLIES-IN-MAIN
     (IMPLIES ($$$INSUB S1)
              (IN-SUB S1))
     :RULE-CLASSES NIL)
   (DEFTHM $$$PRESUB-IMPLIES-INSUB
     (IMPLIES ($$$PRESUB S1) ($$$INSUB S1))
     :RULE-CLASSES NIL)
   (DEFP $$$STEPS-TO-EXITPOINT-SUB-TAIL (S1 I)
     (IF (NOT ($$$INSUB S1))
         I
         (LET* ((S1 (Y86-STEP S1)))
               ($$$STEPS-TO-EXITPOINT-SUB-TAIL S1 (1+ I)))))
   (DEFUN-NX $$$STEPS-TO-EXITPOINT-SUB (S1)
     (DECLARE (XARGS :NORMALIZE NIL))
     (LET* ((STEPS ($$$STEPS-TO-EXITPOINT-SUB-TAIL S1 0))
            (S1 (Y86 S1 STEPS)))
           (IF (NOT ($$$INSUB S1)) STEPS (OMEGA))))
   (DEFUN-NX $$$NEXT-EXITPOINT-SUB (S1)
     (Y86 S1 ($$$STEPS-TO-EXITPOINT-SUB S1)))
   (DEFUN-SK $$$EXISTS-EXITPOINT-SUB (S1)
     (DECLARE (XARGS :NORMALIZE NIL))
     (EXISTS N
             (LET* ((S1 (Y86 S1 N)))
                   (NOT ($$$INSUB S1)))))
   (DEFTHM $$$CORRECTNESS-OF-SUB
     (IMPLIES (AND ($$$PRESUB S1)
                   ($$$EXISTS-EXITPOINT-SUB S1))
              (AND (LET* ((S1 ($$$NEXT-EXITPOINT-SUB S1)))
                         (NOT ($$$INSUB S1)))
                   (EQUAL ($$$NEXT-EXITPOINT-SUB S1)
                          ($$$MODIFYSUB S1))))
     :RULE-CLASSES NIL)
   (LOCAL (IN-THEORY (THEORY 'GROUND-ZERO)))
   (DEFP $$$NEXT-CUTPOINT-MAIN (S1)
     (IF (OR (SEC_NOT_PRESENT-CUTPOINT-P S1)
             (NOT (IN-SUB S1)))
         S1
         (LET* ((S1 (IF ($$$PRESUB S1)
                        ($$$MODIFYSUB S1)
                        (Y86-STEP S1))))
               ($$$NEXT-CUTPOINT-MAIN S1))))
   (DEFTHM $$$DEFP-SYMSIM-THEOREM
     (implies (syntaxp (not (equal (fn-symb s1)
                                   'y86-step)))
              (EQUAL ($$$NEXT-CUTPOINT-MAIN S1)
                     (IF (OR (SEC_NOT_PRESENT-CUTPOINT-P S1)
                             (NOT (IN-SUB S1)))
                         S1
                         (LET* ((S1 (Y86-STEP S1)))
                               ($$$NEXT-CUTPOINT-MAIN S1)))))
     :HINTS (("Goal" :IN-THEORY (ENABLE $$$PRESUB $$$MODIFYSUB))))))
 (LOCAL (DEFTHM $$$PRE-IMPLIES-ASSERTION
          (IMPLIES (SEC_NOT_PRESENT-PRE S1)
                   (LET ((S0 S1))
                        (SEC_NOT_PRESENT-ASSERTION S0 S1)))

          :hints (("Goal" :in-theory (disable SEC_NOT_PRESENT-MODIFY)))

          :RULE-CLASSES NIL))
 (LOCAL (DEFTHM $$$ASSERTION-MAIN-IMPLIES-POST
          (IMPLIES (AND (SEC_NOT_PRESENT-ASSERTION S0 S1)
                        (NOT (IN-SUB S1)))
                   (EQUAL S1
                          (LET ((S1 S0))
                               (SEC_NOT_PRESENT-MODIFY S1))))

          :hints (("Goal" :in-theory (disable SEC_NOT_PRESENT-MODIFY
                                              SEC_NOT_PRESENT-LOOP-PRE
                                              SEC_NOT_PRESENT-MODIFY-LOOP
                                              SEC_NOT_PRESENT-PRE)))

          :RULE-CLASSES NIL))
 (LOCAL (DEFTHM $$$ASSERTION-IMPLIES-CUTPOINT
          (IMPLIES (SEC_NOT_PRESENT-ASSERTION S0 S1)
                   (OR (SEC_NOT_PRESENT-CUTPOINT-P S1)
                       (NOT (IN-SUB S1))))

          :hints (("Goal" :in-theory (disable SEC_NOT_PRESENT-MODIFY
                                              SEC_NOT_PRESENT-LOOP-PRE
                                              SEC_NOT_PRESENT-MODIFY-LOOP
                                              SEC_NOT_PRESENT-PRE)))

          :RULE-CLASSES NIL))
 (LOCAL (IN-THEORY (THEORY 'GROUND-ZERO)))
 (LOCAL (DEFUN-SK $$$EXISTS-NEXT-CUTPOINT (S1)
          (EXISTS N
                  (LET* ((S1 (Y86 S1 N)))
                        (SEC_NOT_PRESENT-CUTPOINT-P S1)))))
 (LOCAL (IN-THEORY (UNION-THEORIES (THEORY 'USER-THEORY)
                                   (LIST '$$$DEFP-SYMSIM-THEOREM))))



 (local (include-book "arithmetic-5/top" :dir :system))

 (local
  (in-theory (disable $$$DEFP-SYMSIM-THEOREM)))

 (local
  (defun simulation-default-hint (stable-under-simplificationp clause)
    (if stable-under-simplificationp
        (let ((concl (car (last clause))))
          (cond ((and (equal (fn-symb concl) 'EQUAL)
                      (equal (fn-symb (arg1 concl)) '$$$NEXT-CUTPOINT-MAIN)
                      (not (equal (fn-symb (arg1 (arg1 concl))) 'Y86-STEP)))
                 `(:computed-hint-replacement t
                                              :expand (,(arg1 concl))))
                ((and (equal (fn-symb concl) 'EQUAL)
                      (equal (fn-symb (arg2 concl)) '$$$NEXT-CUTPOINT-MAIN)
                      (not (equal (fn-symb (arg1 (arg2 concl))) 'Y86-STEP)))
                 `(:computed-hint-replacement t
                                              :expand (,(arg2 concl))))
                (t
                 nil)))
      nil)))

 (local
  (set-default-hints '((simulation-default-hint stable-under-simplificationp clause))))

 (local
  (in-theory (enable n32+ n32)))

 (local
  (in-theory (disable cf zf sf of
                      subl-cf
                      sall-cf sall-of
                      shrl-cf shrl-of
                      unpack)))

;;; new version to handle free vars in simulate-main

 (local
  (defthm simulate-main-start
    (implies (and (equal (g :eip s1)
                         (+ *SEC_NOT_PRESENT* (snpt-code-location)))
                  ;; start
                  (sec_not_present-pre s1)
                  (in-sub s1))
             (equal ($$$NEXT-CUTPOINT-MAIN (Y86-STEP S1))
                    ;; start
                    (UPDATE-REGS
                     :EAX
                     (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S1)) S1))
                          -21)
                     :EBP (+ -4 (G :ESP S1))
                     :EDX
                     (R32 (+ 4
                             (* 8 (ASH (R32 (+ 8 (G :ESP S1)) S1) -30))
                             (R32 (+ 4 (G :ESP S1)) S1))
                          S1)
                     :EIP (+ 313 (SNPT-CODE-LOCATION))
                     :ESP (+ -52 (G :ESP S1))
                     :F-CF
                     (SHRL-CF 21
                              (LOGAND 1071644672
                                      (+ (R32 (+ 8 (G :ESP S1)) S1)
                                         (R32 (+ 12 (G :ESP S1)) S1))))
                     :F-OF
                     (SHRL-OF (LOGAND 1071644672
                                      (+ (R32 (+ 8 (G :ESP S1)) S1)
                                         (R32 (+ 12 (G :ESP S1)) S1))))
                     :F-SF
                     (SF (ASH (LOGAND 1071644672
                                      (+ (R32 (+ 8 (G :ESP S1)) S1)
                                         (R32 (+ 12 (G :ESP S1)) S1)))
                              -21))
                     :F-ZF
                     (ZF (ASH (LOGAND 1071644672
                                      (+ (R32 (+ 8 (G :ESP S1)) S1)
                                         (R32 (+ 12 (G :ESP S1)) S1)))
                              -21))
                     :IMME1
                     21 :VALU1 (R32 (+ 12 (G :ESP S1)) S1)
                     (UPDATE-MEM (+ -4 (G :ESP S1))
                                 (G :EBP S1)
                                 (+ -8 (G :ESP S1))
                                 4294967295 (+ -12 (G :ESP S1))
                                 4294963200 (+ -16 (G :ESP S1))
                                 (ASH (R32 (+ 8 (G :ESP S1)) S1) -30) (+ -20 (G :ESP S1))
                                 (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S1)) S1))
                                      -21)
                                 (+ -24 (G :ESP S1))
                                 (ASH (LOGAND 1071644672
                                              (+ (R32 (+ 8 (G :ESP S1)) S1)
                                                 (R32 (+ 12 (G :ESP S1)) S1)))
                                      -21)
                                 (+ -28 (G :ESP S1))
                                 (ASH (LOGAND 1071644672 (R32 (+ 8 (G :ESP S1)) S1))
                                      -21)
                                 (+ -32 (G :ESP S1))
                                 (LOGAND 4294963200
                                         (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S1)) S1) -30))
                                                 (R32 (+ 4 (G :ESP S1)) S1))
                                              S1))
                                 (+ -36 (G :ESP S1))
                                 (LOGAND 4294963200
                                         (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S1)) S1) -30))
                                                 (R32 (+ 4 (G :ESP S1)) S1))
                                              S1))
                                 (+ -40 (G :ESP S1))
                                 (R32 (+ 4
                                         (* 8 (ASH (R32 (+ 8 (G :ESP S1)) S1) -30))
                                         (R32 (+ 4 (G :ESP S1)) S1))
                                      S1)
                                 (+ -44 (G :ESP S1))
                                 (LOGAND 4294963200
                                         (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S1)) S1) -30))
                                                 (R32 (+ 4 (G :ESP S1)) S1))
                                              S1))
                                 (+ -48 (G :ESP S1))
                                 (R32 (+ 4
                                         (* 8 (ASH (R32 (+ 8 (G :ESP S1)) S1) -30))
                                         (R32 (+ 4 (G :ESP S1)) S1))
                                      S1)
                                 (+ -52 (G :ESP S1))
                                 (R32 (+ (* 8 (ASH (R32 (+ 8 (G :ESP S1)) S1) -30))
                                         (R32 (+ 4 (G :ESP S1)) S1))
                                      S1)
                                 S1))))
    :hints (("Goal" :in-theory (disable MOD-BOUNDS-1
                                        N32+-WHEN-WORD-ALIGNED
                                        |(word-aligned-p x)|
                                        INIT_PDTS-LOADED-THM-32
                                        INIT_PDPT-LOADED-THM-32
                                        CREATE_NESTED_PT-LOADED-THM-32
                                        |(mod (+ x y) z) where (<= 0 z)|
                                        CANCEL-MOD-+

                                        ash-to-floor
                                        )
             :do-not '(generalize eliminate-destructors fertilize))

            )
    :otf-flg t))

 (local
  (defthm simulate-main-loop-loop
    (implies (and (equal (g :eip s1)
                         (+ *L2* (snpt-code-location)))
                  ;; loop
                  (sec_not_present-loop-pre s0 s1)
                  (in-sub s1))
             (equal ($$$NEXT-CUTPOINT-MAIN (Y86-STEP S1))
                    (if (< (r32 (+ -16 (g :ebp s1)) s1) (r32 (+ -20 (g :ebp s1)) s1))
                        ;; stay in loop
                        (UPDATE-REGS :EAX
                                     (+ (R32 (+ -28 (G :EBP S1)) S1)
                                        (ASH (R32 (+ -16 (G :EBP S1)) S1) 3))
                                     :EIP (+ 313 (SNPT-CODE-LOCATION))
                                     :F-CF
                                     (CF (+ 1 (R32 (+ -16 (G :EBP S1)) S1))
                                         (+ 1 (R32 (+ -16 (G :EBP S1)) S1)))
                                     :F-OF
                                     (OF (+ 1 (R32 (+ -16 (G :EBP S1)) S1))
                                         (+ 1 (R32 (+ -16 (G :EBP S1)) S1)))
                                     :F-SF
                                     (SF (+ 1 (R32 (+ -16 (G :EBP S1)) S1)))
                                     :F-ZF
                                     (ZF (+ 1 (R32 (+ -16 (G :EBP S1)) S1)))
                                     :IMME1 1 :VALU1
                                     (+ 1 (R32 (+ -16 (G :EBP S1)) S1))
                                     (UPDATE-MEM (+ -16 (G :EBP S1))
                                                 (+ 1 (R32 (+ -16 (G :EBP S1)) S1))
                                                 (+ (R32 (+ -28 (G :EBP S1)) S1)
                                                    (ASH (R32 (+ -16 (G :EBP S1)) S1) 3))
                                                 0
                                                 (+ 4 (R32 (+ -28 (G :EBP S1)) S1)
                                                    (ASH (R32 (+ -16 (G :EBP S1)) S1) 3))
                                                 0 S1))
                      ;; exit loop
                      (UPDATE-REGS :EAX (R32 (+ -16 (G :EBP S1)) S1)
                                   :EBP (R32 (G :EBP S1) S1)
                                   :EIP (R32 (+ 4 (G :EBP S1)) S1)
                                   :ESP (+ 8 (G :EBP S1))
                                   :F-CF
                                   (SUBL-CF (R32 (+ -16 (G :EBP S1)) S1)
                                            (R32 (+ -16 (G :EBP S1)) S1))
                                   :F-OF 0 :F-SF 0 :F-ZF
                                   1 :VALU1 (R32 (+ -16 (G :EBP S1)) S1)
                                   S1))))
    :hints (("Goal" :in-theory (disable MOD-BOUNDS-1
                                        N32+-WHEN-WORD-ALIGNED
                                        |(word-aligned-p x)|
                                        INIT_PDTS-LOADED-THM-32
                                        INIT_PDPT-LOADED-THM-32
                                        CREATE_NESTED_PT-LOADED-THM-32
                                        |(mod (+ x y) z) where (<= 0 z)|
                                        CANCEL-MOD-+

                                        ash-to-floor
                                        )
             :do-not '(generalize eliminate-destructors fertilize))

            )
    :otf-flg t))




 (local
  (set-default-hints nil))

 (local
  (in-theory (disable |(y86-step st)|
                      |(logior 1 x)|)))

;;; !!! messy
 (local
  (defun assertion-invariant-default-hint-1 (hyps)
    (cond ((endp hyps)
           (mv nil nil))                ; should be error
          ((and (equal (fn-symb (car hyps)) 'NOT)
                (equal (fn-symb (arg1 (car hyps))) 'EQUAL)
                (equal (fn-symb (arg1 (arg1 (car hyps)))) 'S)
                (equal (arg2 (arg1 (car hyps))) 'S1))
           (mv (cdr hyps) (arg1 (arg1 (car hyps)))))
          ((and (equal (fn-symb (car hyps)) 'NOT)
                (equal (fn-symb (arg1 (car hyps))) 'EQUAL)
                (equal (fn-symb (arg2 (arg1 (car hyps)))) 'S)
                (equal (arg1 (arg1 (car hyps))) 'S1))
           (mv (cdr hyps) (arg2 (arg1 (car hyps)))))
          (t
           (mv-let (new-hyps s1-subst)
                   (assertion-invariant-default-hint-1 (cdr hyps))
                   (mv (cons (car hyps) new-hyps)
                       s1-subst))))))

;;; New version to handle free var in simulate-main



;;; !!!
;;; This doesn't seem to work if I use :dynamic-e/d instead of :in-theory
;;; Why???  Fixed by Matt in devel version??
 (local
  (defun assertion-invariant-default-hint (stable-under-simplificationp clause world step)
    (declare (xargs :mode :program))
    (if stable-under-simplificationp
        (cond ((equal step :one)
               (let ()
                 `(:computed-hint-replacement ((assertion-invariant-default-hint
                                                stable-under-simplificationp
                                                clause
                                                world
                                                :two))
;;;                                             :dynamic-e/d ((SEC_NOT_PRESENT-PRE
;;;                                                            SEC_NOT_PRESENT-LOOP-PRE)
;;;                                                           ()))))
                                              :in-theory (enable SEC_NOT_PRESENT-PRE
                                                                 SEC_NOT_PRESENT-LOOP-PRE))))
              ((equal step :two)
               (prog2$
                (observation-cw
                 'assertion-invariant-default-hint
                 "Step number 2 taken after all.")
                (b* ((concl (car (last clause)))
                     ((mv new-hyps s1-subst)
                      (assertion-invariant-default-hint-1 (butlast clause 1)))
                     (concl-vars (all-vars concl))
                     (new-concl `((LAMBDA ,concl-vars ,concl) ,@(subst s1-subst 's1 concl-vars)))
                     (instance (prettyify-clause (append new-hyps
                                                         (list new-concl))
                                                 nil world)))
                    `(:use ((:instance
                             (:theorem ,instance)))
;;;                   :expand ((INIT_PDPT-MODIFY-LOOP-1 (R32 (+ -20 (G :EBP S1)) S1)
;;;                                                     S0))
                           ))))
              (t
               nil))
      nil)))

 (local
  (in-theory (disable SEC_NOT_PRESENT-PRE
                      SEC_NOT_PRESENT-LOOP-PRE)))



 (local
  (set-default-hints '((assertion-invariant-default-hint stable-under-simplificationp
                                                         clause world :one))))






;;; !!!
;;; added to handle inability to use :dynamic-e/d in computed hint
;;; Should I re-enable them
 (local
  (in-theory (disable MOD-BOUNDS-1
                      N32+-WHEN-WORD-ALIGNED
                      |(word-aligned-p x)|
                      |(mod (+ x y) z) where (<= 0 z)|
                      CANCEL-MOD-+

                      ash-to-floor
                      INIT_PDTS-LOADED-THM-32
                      INIT_PDPT-LOADED-THM-32
                      CREATE_NESTED_PT-LOADED-THM-32
                      SEC_NOT_PRESENT-LOADED-THM-32)))



 (LOCAL (DEFTHM $$$ASSERTION-INVARIANT-OVER-CUTPOINTS
          (IMPLIES (AND (SEC_NOT_PRESENT-ASSERTION S0 S1)
                        (IN-SUB S1)
                        (LET* ((S1 (Y86 S1 N)))
                              (NOT (IN-SUB S1))))
                   (LET* ((S1 (Y86-STEP S1))
                          (S1 ($$$NEXT-CUTPOINT-MAIN S1)))
                         (SEC_NOT_PRESENT-ASSERTION S0 S1)))
          :RULE-CLASSES NIL

          :HINTS (("Goal" :in-theory (disable MOD-BOUNDS-1
                                              N32+-WHEN-WORD-ALIGNED
                                              |(word-aligned-p x)|
                                              |(mod (+ x y) z) where (<= 0 z)|
                                              CANCEL-MOD-+

                                              ash-to-floor
                                              INIT_PDTS-LOADED-THM-32
                                              INIT_PDPT-LOADED-THM-32
                                              CREATE_NESTED_PT-LOADED-THM-32
                                              SEC_NOT_PRESENT-LOADED-THM-32)
                   :do-not '(generalize eliminate-destructors fertilize)))
          :otf-flg t))

 (local
  (set-default-hints nil))

 (LOCAL (IN-THEORY (THEORY 'GROUND-ZERO)))
 (DEFP EXITSTEPS-TAIL (S1 I)
   (IF (NOT (IN-SUB S1))
       I
       (LET* ((S1 (Y86-STEP S1)))
             (EXITSTEPS-TAIL S1 (1+ I)))))
 (DEFUN EXITSTEPS (S1)
   (LET* ((STEPS (EXITSTEPS-TAIL S1 0))
          (S1 (Y86 S1 STEPS)))
         (IF (NOT (IN-SUB S1))
             STEPS (OMEGA))))
 (DEFUN-SK EXISTS-NEXT-EXITPOINT
   (S1)
   (EXISTS N
           (LET* ((S1 (Y86 S1 N)))
                 (NOT (IN-SUB S1)))))
 (DEFUN NEXT-EXITPOINT (S1)
   (LET* ((STEPS (EXITSTEPS S1)))
         (Y86 S1 STEPS)))
 (LOCAL (IN-THEORY (THEORY 'MINIMAL-THEORY)))
 (DEFTHM
   SEC_NOT_PRESENT-CORRECT
   (IMPLIES (AND (SEC_NOT_PRESENT-PRE S1)
                 (EXISTS-NEXT-EXITPOINT S1))
            (AND (LET ((S1 (NEXT-EXITPOINT S1)))
                      (NOT (IN-SUB S1)))
                 (EQUAL (NEXT-EXITPOINT S1)
                        (SEC_NOT_PRESENT-MODIFY S1))))
   :OTF-FLG T
   :RULE-CLASSES NIL
   :HINTS
   (("Goal"
     :USE
     ((:INSTANCE
       (:FUNCTIONAL-INSTANCE
        |epc composite partial correctness|
        (EPC-NEXT (LAMBDA (S)
                          (LET ((S1 S)) (Y86-STEP S1))))
        (EPC-RUN (LAMBDA (S N) (Y86 S N)))
        (EXISTS-EPC-NEXT-CUTPOINT
         (LAMBDA (S)
                 (LET ((S1 S))
                      ($$$EXISTS-NEXT-CUTPOINT S1))))
        (EXISTS-EPC-NEXT-CUTPOINT-WITNESS
         (LAMBDA (S)
                 (LET ((S1 S))
                      ($$$EXISTS-NEXT-CUTPOINT-WITNESS S1))))
        (EPC-PRE-SUB (LAMBDA (S)
                             (LET ((S1 S)) ($$$PRESUB S1))))
        (EPC-IN-SUB (LAMBDA (S)
                            (LET ((S1 S)) ($$$INSUB S1))))
        (EPC-EXISTS-EXITPOINT-SUB
         (LAMBDA (S)
                 (LET ((S1 S))
                      ($$$EXISTS-EXITPOINT-SUB S1))))
        (EPC-EXISTS-EXITPOINT-SUB-WITNESS
         (LAMBDA (S)
                 (LET ((S1 S))
                      ($$$EXISTS-EXITPOINT-SUB-WITNESS S1))))
        (EPC-STEPS-TO-EXITPOINT-TAIL-SUB
         (LAMBDA (S I)
                 (LET ((S1 S))
                      ($$$STEPS-TO-EXITPOINT-SUB-TAIL S1 I))))
        (EPC-MODIFY-SUB (LAMBDA (S)
                                (LET ((S1 S)) ($$$MODIFYSUB S1))))
        (EPC-NEXT-EXITPOINT-SUB (LAMBDA (S)
                                        (LET ((S1 S))
                                             ($$$NEXT-EXITPOINT-SUB S1))))
        (EPC-STEPS-TO-EXITPOINT-SUB
         (LAMBDA (S)
                 (LET ((S1 S))
                      ($$$STEPS-TO-EXITPOINT-SUB S1))))
        (EPC-PRE-MAIN (LAMBDA (S)
                              (LET ((S1 S))
                                   (SEC_NOT_PRESENT-PRE S1))))
        (EPC-CUTPOINT-MAIN (LAMBDA (S)
                                   (LET ((S1 S))
                                        (SEC_NOT_PRESENT-CUTPOINT-P S1))))
        (EPC-EXISTS-EXITPOINT-MAIN
         (LAMBDA (S)
                 (LET ((S1 S))
                      (EXISTS-NEXT-EXITPOINT S1))))
        (EPC-EXISTS-EXITPOINT-MAIN-WITNESS
         (LAMBDA (S)
                 (LET ((S1 S))
                      (EXISTS-NEXT-EXITPOINT-WITNESS S1))))
        (EPC-NEXT-EXITPOINT-MAIN
         (LAMBDA (S)
                 (LET ((S1 S))
                      (NEXT-EXITPOINT S1))))
        (EPC-EXITSTEPS-MAIN (LAMBDA (S)
                                    (LET ((S1 S))
                                         (EXITSTEPS S1))))
        (EPC-EXITSTEPS-MAIN-TAIL
         (LAMBDA (S I)
                 (LET ((S1 S))
                      (EXITSTEPS-TAIL S1 I))))
        (EPC-IN-MAIN (LAMBDA (S)
                             (LET ((S1 S)) (IN-SUB S1))))
        (EPC-NEXT-EPC-CUTPOINT-MAIN
         (LAMBDA (S)
                 (LET ((S1 S))
                      ($$$NEXT-CUTPOINT-MAIN S1))))
        (EPC-ASSERTION-MAIN
         (LAMBDA (S0 S)
                 (LET ((S0 S0) (S1 S))
                      (SEC_NOT_PRESENT-ASSERTION S0 S1))))
        (EPC-MODIFY-MAIN (LAMBDA (S)
                                 (LET ((S1 S))
                                      (SEC_NOT_PRESENT-MODIFY S1)))))
       (S S1))))
    ("Subgoal 17" :USE ((:INSTANCE $$$ASSERTION-INVARIANT-OVER-CUTPOINTS
                                   (S0 S0)
                                   (S1 S))))
    ("Subgoal 16" :USE ((:INSTANCE $$$ASSERTION-MAIN-IMPLIES-POST (S0 S0)
                                   (S1 S))))
    ("Subgoal 15" :USE ((:INSTANCE $$$PRE-IMPLIES-ASSERTION (S1 S))))
    ("Subgoal 14" :USE ((:INSTANCE $$$ASSERTION-IMPLIES-CUTPOINT (S0 S0)
                                   (S1 S))))
    ("Subgoal 13" :USE ((:INSTANCE $$$PRESUB-IMPLIES-INSUB (S1 S))))
    ("Subgoal 12" :USE ((:INSTANCE $$$IN-SUB-IMPLIES-IN-MAIN (S1 S))))
    ("Subgoal 11" :USE ((:INSTANCE $$$NO-MAIN-CUTPOINT-IN-SUB (S1 S))))
    ("Subgoal 10" :USE ((:INSTANCE (:DEFINITION $$$EXISTS-NEXT-CUTPOINT)
                                   (S1 S))))
    ("Subgoal 9" :USE ((:INSTANCE $$$EXISTS-NEXT-CUTPOINT-SUFF (S1 S))))
    ("Subgoal 8" :USE ((:INSTANCE $$$NEXT-CUTPOINT-MAIN$DEF (S1 S))))

    ("Subgoal 7" :USE ((:INSTANCE $$$CORRECTNESS-OF-SUB (S1 S))))
    ("Subgoal 6" :USE ((:INSTANCE $$$STEPS-TO-EXITPOINT-SUB-TAIL$DEF
                                   (S1 S))))
    ("Subgoal 5" :USE ((:INSTANCE (:DEFINITION $$$EXISTS-EXITPOINT-SUB)
                                   (S1 S))))
    ("Subgoal 4" :USE ((:INSTANCE $$$EXISTS-EXITPOINT-SUB-SUFF (S1 S))))
    ("Subgoal 3" :USE ((:INSTANCE (:DEFINITION $$$NEXT-EXITPOINT-SUB)
                                  (S1 S))))
    ("Subgoal 2" :USE ((:INSTANCE (:DEFINITION $$$STEPS-TO-EXITPOINT-SUB)
                                  (S1 S))))
    ("Subgoal 1" :IN-THEORY (ENABLE Y86))))
 )



#||
(defsimulate+
  y86-step
  :run y86
  :inmain in-sub
  :cutpoint sec_not_present-cutpoint-p
  :assertion-params (s0 s1)
  :precondition sec_not_present-pre
  :assertion sec_not_present-assertion
  :modify sec_not_present-modify

  :exitsteps exitsteps
  :exists-next-exitpoint exists-next-exitpoint
  :next-exitpoint next-exitpoint

  :correctness-theorem sec_not_present-correct)
||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; create_nested_pt

;;; "main"

(in-theory (disable init_pdpt-modify
                    init_pdts-modify
                    sec_not_present-modify
                    init_pdpt-loaded-thm-32
                    init_pdpt-loaded-thm-08
                    init_pdts-loaded-thm-32
                    init_pdts-loaded-thm-08
                    sec_not_present-loaded-thm-32
                    sec_not_present-loaded-thm-08))

(defun in-create_nested_pt (s)
  (let ((eip (g :eip s)))
    (and (<= (+ *SEC_NOT_PRESENT* (snpt-code-location)) eip)
         (< eip (+ 993 (snpt-code-location))))))

(defun create_nested_pt-cutpoint-p (s)
  (let ((eip (g :eip s)))
    (or (equal eip (+ *CREATE_NESTED_PT* (snpt-code-location))) ; start
        (not (in-create_nested_pt s)))))

(defun create_nested_pt-pre (s)
  ;; note: upon entry to sub-routines , the :esp has been decremented
  ;; by 24
  (and t
       ;; general
       (good-state-p s)
       (equal (g :eip s) (+ *CREATE_NESTED_PT* (snpt-code-location)))
       (not (paging-p s))
       ;; disjoint
       (disjointp (list (range (snpt-code-location) 0 993) ; code
                        (range (g :esp s) -100 200)         ; stack --- big enough?
                        (range (r32 (+ 4 (g :esp s)) s) 0 (* 4 8)) ; pdptp
                        (range (r32 (+ 8 (g :esp s)) s) 0 (* 4 4)) ; pdt pointer array
                        (range (r32 (r32 (+ 8 (g :esp s)) s) s) 0 (* 512 8)) ; ptd one
                        (range (r32 (+ 4 (r32 (+ 8 (g :esp s)) s)) s) 0 (* 512 8)) ; pdt two
                        (range (r32 (+ 8 (r32 (+ 8 (g :esp s)) s)) s) 0 (* 512 8)) ; pdt three
                        (range (r32 (+ 12 (r32 (+ 8 (g :esp s)) s)) s) 0 (* 512 8)))) ; pdt four
       ;; all stack addresses are "good" --- the stack does not wrap
       ;; around memory
       (n32p (+ -100 (g :esp s)))
       (n32p (+ 104 (g :esp s)))
       ;; addresses in pdpt and pdt pointer array are "good"
       (n32p (+ 31 (r32 (+ 4 (g :esp s)) s)))
       (n32p (+ 31 (r32 (+ 8 (g :esp s)) s)))  ; ??? 31 now
       ;; addresses in the pdt are "good"
       (n32p (+ 4095 (r32 (r32 (+ 8 (g :esp s)) s) s)))
       (n32p (+ 4095 (r32 (+ 4 (r32 (+ 8 (g :esp s)) s)) s)))
       (n32p (+ 4095 (r32 (+ 8 (r32 (+ 8 (g :esp s)) s)) s)))
       (n32p (+ 4095 (r32 (+ 12 (r32 (+ 8 (g :esp s)) s)) s)))

       ;; the pdpt is 4k page aligned

       ;; the four pdts are also 4k page aligned

       ;; visor_start + visor_size fits into 32 bits
       (n32p (+ (R32 (+ 12 (G :ESP S)) S)
                (R32 (+ 16 (G :ESP S)) S)))
       ;; all of visor's memory lies within one PDT
       (equal (ash (+ (R32 (+ 12 (G :ESP S)) S)
                      (R32 (+ 16 (G :ESP S)) S))
                   -30)
              (ash (R32 (+ 12 (G :ESP S)) S)
                   -30))
       ;; 0 < visor_size
       (< 0 (R32 (+ 16 (G :ESP S)) S))

       ;; return address
       (< (+ 993 (snpt-code-location)) (R32 (g :esp s) S))

       ;; ??? needed tp prove init_pdpt-modify returns a y86-p --- see init_pdpt-pre
       (N32P (+ 1
                (R32 (+ 12 (R32 (+ 8 (G :ESP S)) S))
                     S)))

       ;; A few more hyps found to be usefull --- about visor_start
       ;; --- see sec_not_present-pre
       ;; what is this last one really saying?
       (< (ASH (LOGAND 1071644672 (R32 (+ 12 (G :ESP S)) S))
               -21)
          (ASH (LOGAND 1071644672
                       (+ (R32 (+ 12 (G :ESP S)) S)
                          (R32 (+ 16 (G :ESP S)) S)))
               -21))
       (<= 1
           (ASH (LOGAND 1071644672
                        (+ (R32 (+ 12 (G :ESP S)) S)
                           (R32 (+ 16 (G :ESP S)) S)))
                -21))
       (n32p (+ 7 (* 8
                     (+ -1
                        (ASH (LOGAND 1071644672
                                     (+ (R32 (+ 12 (G :ESP S)) S)
                                        (R32 (+ 16 (G :ESP S)) S)))
                             -21)))
                (LOGAND 4294963200
                        (R32 (+ (R32 (+ 4 (G :ESP S)) S)
                                (* 8
                                   (ASH (R32 (+ 12 (G :ESP S)) S)
                                        -30)))
                             S))))
       (N32P (+ -1
                (LOGAND 4294963200
                        (LOGIOR 1 (R32 (R32 (+ 8 (G :ESP S)) S) S)))
                (* 8
                   (ASH (LOGAND 1071644672
                                (+ (R32 (+ 12 (G :ESP S)) S)
                                   (R32 (+ 16 (G :ESP S)) S)))
                        -21))))
       (N32P (+ -1
                (LOGAND 4294963200
                        (LOGIOR 1
                                (R32 (+ 4 (R32 (+ 8 (G :ESP S)) S))
                                     S)))
                (* 8
                   (ASH (LOGAND 1071644672
                                (+ (R32 (+ 12 (G :ESP S)) S)
                                   (R32 (+ 16 (G :ESP S)) S)))
                        -21))))
       (N32P (+ -1
                (LOGAND 4294963200
                        (LOGIOR 1
                                (R32 (+ 8 (R32 (+ 8 (G :ESP S)) S))
                                     S)))
                (* 8
                   (ASH (LOGAND 1071644672
                                (+ (R32 (+ 12 (G :ESP S)) S)
                                   (R32 (+ 16 (G :ESP S)) S)))
                        -21))))
       (N32P (+ -1
                (LOGAND 4294963200
                        (LOGIOR 1
                                (R32 (+ 12 (R32 (+ 8 (G :ESP S)) S))
                                     S)))
                (* 8
                   (ASH (LOGAND 1071644672
                                (+ (R32 (+ 12 (G :ESP S)) S)
                                   (R32 (+ 16 (G :ESP S)) S)))
                        -21))))
       ;; page aligned
       (equal (LOGAND -4096
                      (R32 (+ 12 (R32 (+ 8 (G :ESP S)) S))
                           S))
              (R32 (+ 12 (R32 (+ 8 (G :ESP S)) S))
                   S))
       (equal (LOGAND -4096
                      (R32 (+ 8 (R32 (+ 8 (G :ESP S)) S))
                           S))
              (R32 (+ 8 (R32 (+ 8 (G :ESP S)) S))
                   S))
       (equal (LOGAND -4096
                      (R32 (+ 4 (R32 (+ 8 (G :ESP S)) S))
                           S))
              (R32 (+ 4 (R32 (+ 8 (G :ESP S)) S))
                   S))
       (equal (LOGAND -4096
                      (R32 (R32 (+ 8 (G :ESP S)) S)
                           S))
              (R32 (R32 (+ 8 (G :ESP S)) S)
                   S))

       ))

(defun create_nested_pt-modify (s)
  (b* ((init_pdpt-setup (update-regs :EAX (R32 (+ 4 (G :ESP S)) S)
                                     :EBP (+ -4 (G :ESP S))
                                     :EIP (+ 687 (SNPT-CODE-LOCATION))
                                     :ESP (+ -24 (G :ESP S))
                                     :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                     :F-OF
                                     (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                         (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                     :F-SF
                                     (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                     :F-ZF (ZF (+ -20 (G :ESP S)))
                                     :IMME1 16
                                     (update-mem (+ -4 (g :esp s))
                                                 (g :ebp s)
                                                 (+ -16 (g :esp s))
                                                 (r32 (+ 8 (g :esp s)) s)
                                                 (+ -20 (g :esp s))
                                                 (r32 (+ 4 (g :esp s)) s)
                                                 (+ -24 (G :ESP S))
                                                 (+ 927 (SNPT-CODE-LOCATION))
                                                 s)))
       (init_pdpt-result (init_pdpt-modify init_pdpt-setup))
       (init_pdts-setup (update-regs :eax (r32 (+ 8 (g :esp s)) s)
                                     :eip (+ *INIT_PDTS* (snpt-code-location))
                                     :ESP (+ -24 (G :ESP S))
                                     (update-mem (+ -20 (g :esp s))
                                                 (r32 (+ 8 (g :esp s)) s)
                                                 (+ -24 (G :ESP S))
                                                 (+ 944 (SNPT-CODE-LOCATION))
                                                 init_pdpt-result)))
       (init_pdts-result (init_pdts-modify init_pdts-setup))
       (sec_not_present-setup (update-regs :eax (r32 (+ 4 (g :esp s)) s)
                                           :eip (+ *SEC_NOT_PRESENT* (snpt-code-location))
                                           :ESP (+ -24 (G :ESP S))
                                           (update-mem (+ -12 (g :esp s))
                                                       (r32 (+ 16 (g :esp s)) s)
                                                       (+ -16 (g :esp s))
                                                       (r32 (+ 12 (g :esp s)) s)
                                                       (+ -20 (g :esp s))
                                                       (r32 (+ 4 (g :esp s)) s)
                                                       (+ -24 (G :ESP S))
                                                       (+ 985 (SNPT-CODE-LOCATION))
                                                       init_pdts-result)))
       (sec_not_present-result (sec_not_present-modify sec_not_present-setup))
       (final-result (update-regs :eax (r32 (+ 4 (g :esp s)) s)
                                  :ebp (g :ebp s)
                                  :eip (r32 (g :esp s) s)
                                  :esp (+ 4 (g :esp s))
                                  sec_not_present-result)))
      final-result))


(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))


;;; Blindly copy in proof of |(init_pdpt-pre s)| and two related thms



 (local
  (defthm ash-thm-100
    (implies (n32p x)
             (and (<= 0 (ash x -30))
                  (< (ash x -30) 4)))
    :hints (("Goal" :in-theory (enable ash-to-floor)))
    :rule-classes :linear))

 (local
  (encapsulate
   ()

   (local
    (defthm break-logand-apart
      (implies (and (integerp x)
                    (integerp y))
               (equal (logand x y)
                      (+ (* 2 (logand (floor x 2) (floor y 2)))
                         (logand (mod x 2) (mod y 2)))))
      :rule-classes nil))

   (defthm logior-thm-100
     (equal (logand -4096
                    (logior 1 x))
            (logand -4096 x))
     :hints (("Goal" :in-theory (disable |(logior 1 x)|
                                         |(floor x 2)|
                                         |(logior (floor x 2) (floor y 2))|)
              :use ((:instance break-logand-apart
                               (x -4096)
                               (y (logior 1 x)))
                    (:instance break-logand-apart
                               (x -4096)
                               (y x))
                    (:instance |(logior (floor x 2) (floor y 2))|
                               (x 1)
                               (y x)))))
     )
   ))

 (encapsulate
  ()

  (defthm crock-200
    (implies (and (integerp x)
                  (n32p x))
             (equal (logand -4096 x)
                    (logand 4294963200 x)))
    :hints (("Goal" :use ((:instance
                           (:theorem
                            (equal (logand (logand x y) z)
                                   (logand x (logand y z))))
                           (x -4096)
                           (y (+ -1 (expt 2 32)))
                           (z x))))))

  (defthm ash-thm-103
    (implies (y86-p s1)
             (equal (LOGAND 4294963200
                            (LOGIOR 1
                                    (R32 addr
                                         S1)))
                    (logand -4096 (r32 addr s1))))
    :hints (("Goal" :in-theory (disable |(logior 1 x)|
                                        logior-thm-100)
             :use ((:instance logior-thm-100
                              (x (R32 addr
                                      S1)))))))
  )

 (local
  (defthm ash-thm-101
    (<= (ash (logand 1071644672 x)
             -21)
        511)
    :hints (("Goal" :in-theory (enable ash-to-floor)))
    :rule-classes :linear))

 (local
  (defthm ash-thm-102
    (<= 0
        (ash (logand 1071644672 x)
             -21))
    :hints (("Goal" :in-theory (enable ash-to-floor)))
    :rule-classes :linear))

 (local
  (in-theory (enable n32+ n32)))

 (local
  (in-theory (disable cf zf sf of
                      subl-cf
                      sall-cf sall-of
                      shrl-cf shrl-of
                      unpack)))


 (local
  (in-theory (disable ash-to-floor)))


 (local
  (defthm |(init_pdpt-pre s)|
    (implies (create_nested_pt-pre s1)
             (INIT_PDPT-PRE
              (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                           :EBP (+ -4 (G :ESP S1))
                           :EIP (+ 687 (SNPT-CODE-LOCATION))
                           :ESP (+ -24 (G :ESP S1))
                           :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                           :F-OF
                           (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                               (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                           :F-SF
                           (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                           :F-ZF (ZF (+ -20 (G :ESP S1)))
                           :IMME1 16
                           (UPDATE-MEM (+ -4 (G :ESP S1))
                                       (G :EBP S1)
                                       (+ -16 (G :ESP S1))
                                       (R32 (+ 8 (G :ESP S1)) S1)
                                       (+ -20 (G :ESP S1))
                                       (R32 (+ 4 (G :ESP S1)) S1)
                                       (+ -24 (G :ESP S1))
                                       (+ 927 (SNPT-CODE-LOCATION))
                                       S1))))))



 (local
  (defthm |(init_pdts-pre s)|
    (implies (create_nested_pt-pre s1)
             (INIT_PDTS-PRE
              (UPDATE-REGS
               :EAX (R32 (+ 8 (G :ESP S1)) S1)
               :EIP (+ 334 (SNPT-CODE-LOCATION))
               :ESP (+ -24 (G :ESP S1))
               (UPDATE-MEM
                (+ -20 (G :ESP S1))
                (R32 (+ 8 (G :ESP S1)) S1)
                (+ -24 (G :ESP S1))
                (+ 944 (SNPT-CODE-LOCATION))
                (INIT_PDPT-MODIFY
                 (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                              :EBP (+ -4 (G :ESP S1))
                              :EIP (+ 687 (SNPT-CODE-LOCATION))
                              :ESP (+ -24 (G :ESP S1))
                              :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                              :F-OF
                              (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                  (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                              :F-SF
                              (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                              :F-ZF (ZF (+ -20 (G :ESP S1)))
                              :IMME1 16
                              (UPDATE-MEM (+ -4 (G :ESP S1))
                                          (G :EBP S1)
                                          (+ -16 (G :ESP S1))
                                          (R32 (+ 8 (G :ESP S1)) S1)
                                          (+ -20 (G :ESP S1))
                                          (R32 (+ 4 (G :ESP S1)) S1)
                                          (+ -24 (G :ESP S1))
                                          (+ 927 (SNPT-CODE-LOCATION))
                                          S1)))))))
    :hints (("Goal" :in-theory (disable |(logior 1 x)|)))))

;;; !!! why so slow?
 (local
  (defthm |(create_nested_pt-pre s)|
    (implies (create_nested_pt-pre s1)
             (SEC_NOT_PRESENT-PRE
              (UPDATE-REGS
               :EAX (R32 (+ 4 (G :ESP S1)) S1)
               :EIP (SNPT-CODE-LOCATION)
               :ESP (+ -24 (G :ESP S1))
               (UPDATE-MEM
                (+ -12 (G :ESP S1))
                (R32 (+ 16 (G :ESP S1)) S1)
                (+ -16 (G :ESP S1))
                (R32 (+ 12 (G :ESP S1)) S1)
                (+ -20 (G :ESP S1))
                (R32 (+ 4 (G :ESP S1)) S1)
                (+ -24 (G :ESP S1))
                (+ 985 (SNPT-CODE-LOCATION))
                (INIT_PDTS-MODIFY
                 (UPDATE-REGS
                  :EAX (R32 (+ 8 (G :ESP S1)) S1)
                  :EIP (+ 334 (SNPT-CODE-LOCATION))
                  :ESP (+ -24 (G :ESP S1))
                  (UPDATE-MEM
                   (+ -20 (G :ESP S1))
                   (R32 (+ 8 (G :ESP S1)) S1)
                   (+ -24 (G :ESP S1))
                   (+ 944 (SNPT-CODE-LOCATION))
                   (INIT_PDPT-MODIFY
                    (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                 :EBP (+ -4 (G :ESP S1))
                                 :EIP (+ 687 (SNPT-CODE-LOCATION))
                                 :ESP (+ -24 (G :ESP S1))
                                 :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                 :F-OF
                                 (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                     (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                 :F-SF
                                 (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                 :F-ZF (ZF (+ -20 (G :ESP S1)))
                                 :IMME1 16
                                 (UPDATE-MEM (+ -4 (G :ESP S1))
                                             (G :EBP S1)
                                             (+ -16 (G :ESP S1))
                                             (R32 (+ 8 (G :ESP S1)) S1)
                                             (+ -20 (G :ESP S1))
                                             (R32 (+ 4 (G :ESP S1)) S1)
                                             (+ -24 (G :ESP S1))
                                             (+ 927 (SNPT-CODE-LOCATION))
                                             S1))))))))))
    :hints (("Goal" :do-not '(generalize eliminate-destructors fertilize)
             :in-theory (disable |(logior 1 x)|
                                 init_pdpt-pre
                                 init_pdts-pre)
             :cases ((equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 0)
                     (equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 1)
                     (equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 2)
                     (equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 3)))
            ("Subgoal 4"
             :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                              (i 0)
                              (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                              :EBP (+ -4 (G :ESP S1))
                                              :EIP (+ 687 (SNPT-CODE-LOCATION))
                                              :ESP (+ -24 (G :ESP S1))
                                              :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                              :F-OF
                                              (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                  (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                              :F-SF
                                              (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                              :F-ZF (ZF (+ -20 (G :ESP S1)))
                                              :IMME1 16
                                              (UPDATE-MEM (+ -4 (G :ESP S1))
                                                          (G :EBP S1)
                                                          (+ -16 (G :ESP S1))
                                                          (R32 (+ 8 (G :ESP S1)) S1)
                                                          (+ -20 (G :ESP S1))
                                                          (R32 (+ 4 (G :ESP S1)) S1)
                                                          (+ -24 (G :ESP S1))
                                                          (+ 927 (SNPT-CODE-LOCATION))
                                                          S1))))))
            ("Subgoal 3"
             :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                              (i 1)
                              (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                              :EBP (+ -4 (G :ESP S1))
                                              :EIP (+ 687 (SNPT-CODE-LOCATION))
                                              :ESP (+ -24 (G :ESP S1))
                                              :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                              :F-OF
                                              (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                  (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                              :F-SF
                                              (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                              :F-ZF (ZF (+ -20 (G :ESP S1)))
                                              :IMME1 16
                                              (UPDATE-MEM (+ -4 (G :ESP S1))
                                                          (G :EBP S1)
                                                          (+ -16 (G :ESP S1))
                                                          (R32 (+ 8 (G :ESP S1)) S1)
                                                          (+ -20 (G :ESP S1))
                                                          (R32 (+ 4 (G :ESP S1)) S1)
                                                          (+ -24 (G :ESP S1))
                                                          (+ 927 (SNPT-CODE-LOCATION))
                                                          S1))))))
            ("Subgoal 2"
             :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                              (i 2)
                              (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                              :EBP (+ -4 (G :ESP S1))
                                              :EIP (+ 687 (SNPT-CODE-LOCATION))
                                              :ESP (+ -24 (G :ESP S1))
                                              :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                              :F-OF
                                              (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                  (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                              :F-SF
                                              (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                              :F-ZF (ZF (+ -20 (G :ESP S1)))
                                              :IMME1 16
                                              (UPDATE-MEM (+ -4 (G :ESP S1))
                                                          (G :EBP S1)
                                                          (+ -16 (G :ESP S1))
                                                          (R32 (+ 8 (G :ESP S1)) S1)
                                                          (+ -20 (G :ESP S1))
                                                          (R32 (+ 4 (G :ESP S1)) S1)
                                                          (+ -24 (G :ESP S1))
                                                          (+ 927 (SNPT-CODE-LOCATION))
                                                          S1))))))
            ("Subgoal 1"
             :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                              (i 3)
                              (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                              :EBP (+ -4 (G :ESP S1))
                                              :EIP (+ 687 (SNPT-CODE-LOCATION))
                                              :ESP (+ -24 (G :ESP S1))
                                              :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                              :F-OF
                                              (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                  (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                              :F-SF
                                              (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                              :F-ZF (ZF (+ -20 (G :ESP S1)))
                                              :IMME1 16
                                              (UPDATE-MEM (+ -4 (G :ESP S1))
                                                          (G :EBP S1)
                                                          (+ -16 (G :ESP S1))
                                                          (R32 (+ 8 (G :ESP S1)) S1)
                                                          (+ -20 (G :ESP S1))
                                                          (R32 (+ 4 (G :ESP S1)) S1)
                                                          (+ -24 (G :ESP S1))
                                                          (+ 927 (SNPT-CODE-LOCATION))
                                                          S1)))))))
    :otf-flg t))


 (local
  (in-theory (disable init_pdpt-pre
                      init_pdts-pre
                      sec_not_present-pre)))

 (defthm |(y86-p (create_nested_pt-modify s))|
   (implies (create_nested_pt-pre s)
            (y86-p (create_nested_pt-modify s)))
   :hints (("Goal" :in-theory (e/d (y86-p
                                    y86-register-guard
                                    y86-flags-guard
                                    y86-memory-guard
                                    y86-supervisor-guard
                                    y86-misc-guard)
                                   (|(y86-p (sec_not_present-modify s))|))
            :use ((:instance |(y86-p (sec_not_present-modify s))|
                             (s (UPDATE-REGS
                                 :EAX (R32 (+ 4 (G :ESP S)) S)
                                 :EIP (SNPT-CODE-LOCATION)
                                 :ESP (+ -24 (G :ESP S))
                                 (UPDATE-MEM
                                  (+ -12 (G :ESP S))
                                  (R32 (+ 16 (G :ESP S)) S)
                                  (+ -16 (G :ESP S))
                                  (R32 (+ 12 (G :ESP S)) S)
                                  (+ -20 (G :ESP S))
                                  (R32 (+ 4 (G :ESP S)) S)
                                  (+ -24 (G :ESP S))
                                  (+ 985 (SNPT-CODE-LOCATION))
                                  (INIT_PDTS-MODIFY
                                   (UPDATE-REGS
                                    :EAX (R32 (+ 8 (G :ESP S)) S)
                                    :EIP (+ 334 (SNPT-CODE-LOCATION))
                                    :ESP (+ -24 (G :ESP S))
                                    (UPDATE-MEM
                                     (+ -20 (G :ESP S))
                                     (R32 (+ 8 (G :ESP S)) S)
                                     (+ -24 (G :ESP S))
                                     (+ 944 (SNPT-CODE-LOCATION))
                                     (INIT_PDPT-MODIFY
                                      (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                   :EBP (+ -4 (G :ESP S))
                                                   :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                   :ESP (+ -24 (G :ESP S))
                                                   :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                   :F-OF
                                                   (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                       (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                   :F-SF
                                                   (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                   :F-ZF (ZF (+ -20 (G :ESP S)))
                                                   :IMME1 16
                                                   (UPDATE-MEM (+ -4 (G :ESP S))
                                                               (G :EBP S)
                                                               (+ -16 (G :ESP S))
                                                               (R32 (+ 8 (G :ESP S)) S)
                                                               (+ -20 (G :ESP S))
                                                               (R32 (+ 4 (G :ESP S)) S)
                                                               (+ -24 (G :ESP S))
                                                               (+ 927 (SNPT-CODE-LOCATION))
                                                               S))))))))))))))

 (defthm |(g :cr0 (create_nested_pt-modify s))|
   (implies (create_nested_pt-pre s)
            (equal (g :cr0 (create_nested_pt-modify s))
                   (G :cr0 s))))


;;; Do I still need all these hints?
;;; !!! grossly slow with all the hints
 (defthm |(r32 addr (create_nested_pt-modify s)) --- init_pdpt|
   (implies (and (create_nested_pt-pre s)

                 (integerp i)
                 (<= 0 i)
                 (<= i 3))
            (equal (r32 (+ (* 8 i)
                           (R32 (+ 4 (G :ESP S)) S))
                        (create_nested_pt-modify s))
                   (LOGIOR 1
                           (R32 (+ (* 4 i)
                                   (R32 (+ 8 (G :ESP S)) S))
                                S))))
   :hints (("Goal" :in-theory (disable |(logior 1 x)|
                                       ash-to-floor)
            :cases ((equal i 0)
                    (equal i 1)
                    (equal i 2)
                    (equal i 3))
            :do-not '(generalize eliminate-destructors fertilize))
           ("Subgoal 4"
            :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                             (i 0)
                             (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                             :EBP (+ -4 (G :ESP S))
                                             :EIP (+ 687 (SNPT-CODE-LOCATION))
                                             :ESP (+ -24 (G :ESP S))
                                             :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                             :F-OF
                                             (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                 (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                             :F-SF
                                             (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                             :F-ZF (ZF (+ -20 (G :ESP S)))
                                             :IMME1 16
                                             (UPDATE-MEM (+ -4 (G :ESP S))
                                                         (G :EBP S)
                                                         (+ -16 (G :ESP S))
                                                         (R32 (+ 8 (G :ESP S)) S)
                                                         (+ -20 (G :ESP S))
                                                         (R32 (+ 4 (G :ESP S)) S)
                                                         (+ -24 (G :ESP S))
                                                         (+ 927 (SNPT-CODE-LOCATION))
                                                         S))))
                  (:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                             (i 1)
                             (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                             :EBP (+ -4 (G :ESP S))
                                             :EIP (+ 687 (SNPT-CODE-LOCATION))
                                             :ESP (+ -24 (G :ESP S))
                                             :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                             :F-OF
                                             (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                 (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                             :F-SF
                                             (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                             :F-ZF (ZF (+ -20 (G :ESP S)))
                                             :IMME1 16
                                             (UPDATE-MEM (+ -4 (G :ESP S))
                                                         (G :EBP S)
                                                         (+ -16 (G :ESP S))
                                                         (R32 (+ 8 (G :ESP S)) S)
                                                         (+ -20 (G :ESP S))
                                                         (R32 (+ 4 (G :ESP S)) S)
                                                         (+ -24 (G :ESP S))
                                                         (+ 927 (SNPT-CODE-LOCATION))
                                                         S))))
                  (:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                             (i 2)
                             (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                             :EBP (+ -4 (G :ESP S))
                                             :EIP (+ 687 (SNPT-CODE-LOCATION))
                                             :ESP (+ -24 (G :ESP S))
                                             :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                             :F-OF
                                             (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                 (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                             :F-SF
                                             (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                             :F-ZF (ZF (+ -20 (G :ESP S)))
                                             :IMME1 16
                                             (UPDATE-MEM (+ -4 (G :ESP S))
                                                         (G :EBP S)
                                                         (+ -16 (G :ESP S))
                                                         (R32 (+ 8 (G :ESP S)) S)
                                                         (+ -20 (G :ESP S))
                                                         (R32 (+ 4 (G :ESP S)) S)
                                                         (+ -24 (G :ESP S))
                                                         (+ 927 (SNPT-CODE-LOCATION))
                                                         S))))
                  (:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                             (i 3)
                             (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                             :EBP (+ -4 (G :ESP S))
                                             :EIP (+ 687 (SNPT-CODE-LOCATION))
                                             :ESP (+ -24 (G :ESP S))
                                             :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                             :F-OF
                                             (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                 (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                             :F-SF
                                             (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                             :F-ZF (ZF (+ -20 (G :ESP S)))
                                             :IMME1 16
                                             (UPDATE-MEM (+ -4 (G :ESP S))
                                                         (G :EBP S)
                                                         (+ -16 (G :ESP S))
                                                         (R32 (+ 8 (G :ESP S)) S)
                                                         (+ -20 (G :ESP S))
                                                         (R32 (+ 4 (G :ESP S)) S)
                                                         (+ -24 (G :ESP S))
                                                         (+ 927 (SNPT-CODE-LOCATION))
                                                         S))))
                  (:instance |(r32 addr (sec_not_present-modify s))|
                             (addr (R32 (+ 4 (G :ESP S)) S))
                             (s (UPDATE-REGS
                                 :EAX (R32 (+ 4 (G :ESP S)) S)
                                 :EIP (SNPT-CODE-LOCATION)
                                 :ESP (+ -24 (G :ESP S))
                                 (UPDATE-MEM
                                  (+ -12 (G :ESP S))
                                  (R32 (+ 16 (G :ESP S)) S)
                                  (+ -16 (G :ESP S))
                                  (R32 (+ 12 (G :ESP S)) S)
                                  (+ -20 (G :ESP S))
                                  (R32 (+ 4 (G :ESP S)) S)
                                  (+ -24 (G :ESP S))
                                  (+ 985 (SNPT-CODE-LOCATION))
                                  (INIT_PDTS-MODIFY
                                   (UPDATE-REGS
                                    :EAX (R32 (+ 8 (G :ESP S)) S)
                                    :EIP (+ 334 (SNPT-CODE-LOCATION))
                                    :ESP (+ -24 (G :ESP S))
                                    (UPDATE-MEM
                                     (+ -20 (G :ESP S))
                                     (R32 (+ 8 (G :ESP S)) S)
                                     (+ -24 (G :ESP S))
                                     (+ 944 (SNPT-CODE-LOCATION))
                                     (INIT_PDPT-MODIFY
                                      (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                   :EBP (+ -4 (G :ESP S))
                                                   :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                   :ESP (+ -24 (G :ESP S))
                                                   :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                   :F-OF
                                                   (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                       (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                   :F-SF
                                                   (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                   :F-ZF (ZF (+ -20 (G :ESP S)))
                                                   :IMME1 16
                                                   (UPDATE-MEM (+ -4 (G :ESP S))
                                                               (G :EBP S)
                                                               (+ -16 (G :ESP S))
                                                               (R32 (+ 8 (G :ESP S)) S)
                                                               (+ -20 (G :ESP S))
                                                               (R32 (+ 4 (G :ESP S)) S)
                                                               (+ -24 (G :ESP S))
                                                               (+ 927 (SNPT-CODE-LOCATION))
                                                               S))))))))))))
           ("Subgoal 4.1" :cases ((equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 0)
                                  (equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 1)
                                  (equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 2)
                                  (equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 3)))
           ("Subgoal 3"
            :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                             (i 0)
                             (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                             :EBP (+ -4 (G :ESP S))
                                             :EIP (+ 687 (SNPT-CODE-LOCATION))
                                             :ESP (+ -24 (G :ESP S))
                                             :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                             :F-OF
                                             (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                 (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                             :F-SF
                                             (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                             :F-ZF (ZF (+ -20 (G :ESP S)))
                                             :IMME1 16
                                             (UPDATE-MEM (+ -4 (G :ESP S))
                                                         (G :EBP S)
                                                         (+ -16 (G :ESP S))
                                                         (R32 (+ 8 (G :ESP S)) S)
                                                         (+ -20 (G :ESP S))
                                                         (R32 (+ 4 (G :ESP S)) S)
                                                         (+ -24 (G :ESP S))
                                                         (+ 927 (SNPT-CODE-LOCATION))
                                                         S))))
                  (:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                             (i 1)
                             (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                             :EBP (+ -4 (G :ESP S))
                                             :EIP (+ 687 (SNPT-CODE-LOCATION))
                                             :ESP (+ -24 (G :ESP S))
                                             :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                             :F-OF
                                             (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                 (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                             :F-SF
                                             (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                             :F-ZF (ZF (+ -20 (G :ESP S)))
                                             :IMME1 16
                                             (UPDATE-MEM (+ -4 (G :ESP S))
                                                         (G :EBP S)
                                                         (+ -16 (G :ESP S))
                                                         (R32 (+ 8 (G :ESP S)) S)
                                                         (+ -20 (G :ESP S))
                                                         (R32 (+ 4 (G :ESP S)) S)
                                                         (+ -24 (G :ESP S))
                                                         (+ 927 (SNPT-CODE-LOCATION))
                                                         S))))
                  (:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                             (i 2)
                             (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                             :EBP (+ -4 (G :ESP S))
                                             :EIP (+ 687 (SNPT-CODE-LOCATION))
                                             :ESP (+ -24 (G :ESP S))
                                             :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                             :F-OF
                                             (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                 (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                             :F-SF
                                             (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                             :F-ZF (ZF (+ -20 (G :ESP S)))
                                             :IMME1 16
                                             (UPDATE-MEM (+ -4 (G :ESP S))
                                                         (G :EBP S)
                                                         (+ -16 (G :ESP S))
                                                         (R32 (+ 8 (G :ESP S)) S)
                                                         (+ -20 (G :ESP S))
                                                         (R32 (+ 4 (G :ESP S)) S)
                                                         (+ -24 (G :ESP S))
                                                         (+ 927 (SNPT-CODE-LOCATION))
                                                         S))))
                  (:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                             (i 3)
                             (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                             :EBP (+ -4 (G :ESP S))
                                             :EIP (+ 687 (SNPT-CODE-LOCATION))
                                             :ESP (+ -24 (G :ESP S))
                                             :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                             :F-OF
                                             (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                 (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                             :F-SF
                                             (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                             :F-ZF (ZF (+ -20 (G :ESP S)))
                                             :IMME1 16
                                             (UPDATE-MEM (+ -4 (G :ESP S))
                                                         (G :EBP S)
                                                         (+ -16 (G :ESP S))
                                                         (R32 (+ 8 (G :ESP S)) S)
                                                         (+ -20 (G :ESP S))
                                                         (R32 (+ 4 (G :ESP S)) S)
                                                         (+ -24 (G :ESP S))
                                                         (+ 927 (SNPT-CODE-LOCATION))
                                                         S))))
                  (:instance |(r32 addr (sec_not_present-modify s))|
                             (addr (+ 8 (R32 (+ 4 (G :ESP S)) S)))
                             (s (UPDATE-REGS
                                 :EAX (R32 (+ 4 (G :ESP S)) S)
                                 :EIP (SNPT-CODE-LOCATION)
                                 :ESP (+ -24 (G :ESP S))
                                 (UPDATE-MEM
                                  (+ -12 (G :ESP S))
                                  (R32 (+ 16 (G :ESP S)) S)
                                  (+ -16 (G :ESP S))
                                  (R32 (+ 12 (G :ESP S)) S)
                                  (+ -20 (G :ESP S))
                                  (R32 (+ 4 (G :ESP S)) S)
                                  (+ -24 (G :ESP S))
                                  (+ 985 (SNPT-CODE-LOCATION))
                                  (INIT_PDTS-MODIFY
                                   (UPDATE-REGS
                                    :EAX (R32 (+ 8 (G :ESP S)) S)
                                    :EIP (+ 334 (SNPT-CODE-LOCATION))
                                    :ESP (+ -24 (G :ESP S))
                                    (UPDATE-MEM
                                     (+ -20 (G :ESP S))
                                     (R32 (+ 8 (G :ESP S)) S)
                                     (+ -24 (G :ESP S))
                                     (+ 944 (SNPT-CODE-LOCATION))
                                     (INIT_PDPT-MODIFY
                                      (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                   :EBP (+ -4 (G :ESP S))
                                                   :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                   :ESP (+ -24 (G :ESP S))
                                                   :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                   :F-OF
                                                   (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                       (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                   :F-SF
                                                   (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                   :F-ZF (ZF (+ -20 (G :ESP S)))
                                                   :IMME1 16
                                                   (UPDATE-MEM (+ -4 (G :ESP S))
                                                               (G :EBP S)
                                                               (+ -16 (G :ESP S))
                                                               (R32 (+ 8 (G :ESP S)) S)
                                                               (+ -20 (G :ESP S))
                                                               (R32 (+ 4 (G :ESP S)) S)
                                                               (+ -24 (G :ESP S))
                                                               (+ 927 (SNPT-CODE-LOCATION))
                                                               S))))))))))))
           ("Subgoal 3.1" :cases ((equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 0)
                                  (equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 1)
                                  (equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 2)
                                  (equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 3)))
           ("Subgoal 2"
            :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                             (i 0)
                             (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                             :EBP (+ -4 (G :ESP S))
                                             :EIP (+ 687 (SNPT-CODE-LOCATION))
                                             :ESP (+ -24 (G :ESP S))
                                             :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                             :F-OF
                                             (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                 (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                             :F-SF
                                             (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                             :F-ZF (ZF (+ -20 (G :ESP S)))
                                             :IMME1 16
                                             (UPDATE-MEM (+ -4 (G :ESP S))
                                                         (G :EBP S)
                                                         (+ -16 (G :ESP S))
                                                         (R32 (+ 8 (G :ESP S)) S)
                                                         (+ -20 (G :ESP S))
                                                         (R32 (+ 4 (G :ESP S)) S)
                                                         (+ -24 (G :ESP S))
                                                         (+ 927 (SNPT-CODE-LOCATION))
                                                         S))))
                  (:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                             (i 1)
                             (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                             :EBP (+ -4 (G :ESP S))
                                             :EIP (+ 687 (SNPT-CODE-LOCATION))
                                             :ESP (+ -24 (G :ESP S))
                                             :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                             :F-OF
                                             (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                 (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                             :F-SF
                                             (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                             :F-ZF (ZF (+ -20 (G :ESP S)))
                                             :IMME1 16
                                             (UPDATE-MEM (+ -4 (G :ESP S))
                                                         (G :EBP S)
                                                         (+ -16 (G :ESP S))
                                                         (R32 (+ 8 (G :ESP S)) S)
                                                         (+ -20 (G :ESP S))
                                                         (R32 (+ 4 (G :ESP S)) S)
                                                         (+ -24 (G :ESP S))
                                                         (+ 927 (SNPT-CODE-LOCATION))
                                                         S))))
                  (:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                             (i 2)
                             (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                             :EBP (+ -4 (G :ESP S))
                                             :EIP (+ 687 (SNPT-CODE-LOCATION))
                                             :ESP (+ -24 (G :ESP S))
                                             :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                             :F-OF
                                             (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                 (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                             :F-SF
                                             (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                             :F-ZF (ZF (+ -20 (G :ESP S)))
                                             :IMME1 16
                                             (UPDATE-MEM (+ -4 (G :ESP S))
                                                         (G :EBP S)
                                                         (+ -16 (G :ESP S))
                                                         (R32 (+ 8 (G :ESP S)) S)
                                                         (+ -20 (G :ESP S))
                                                         (R32 (+ 4 (G :ESP S)) S)
                                                         (+ -24 (G :ESP S))
                                                         (+ 927 (SNPT-CODE-LOCATION))
                                                         S))))
                  (:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                             (i 3)
                             (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                             :EBP (+ -4 (G :ESP S))
                                             :EIP (+ 687 (SNPT-CODE-LOCATION))
                                             :ESP (+ -24 (G :ESP S))
                                             :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                             :F-OF
                                             (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                 (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                             :F-SF
                                             (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                             :F-ZF (ZF (+ -20 (G :ESP S)))
                                             :IMME1 16
                                             (UPDATE-MEM (+ -4 (G :ESP S))
                                                         (G :EBP S)
                                                         (+ -16 (G :ESP S))
                                                         (R32 (+ 8 (G :ESP S)) S)
                                                         (+ -20 (G :ESP S))
                                                         (R32 (+ 4 (G :ESP S)) S)
                                                         (+ -24 (G :ESP S))
                                                         (+ 927 (SNPT-CODE-LOCATION))
                                                         S))))
                  (:instance |(r32 addr (sec_not_present-modify s))|
                             (addr (+ 16 (R32 (+ 4 (G :ESP S)) S)))
                             (s (UPDATE-REGS
                                 :EAX (R32 (+ 4 (G :ESP S)) S)
                                 :EIP (SNPT-CODE-LOCATION)
                                 :ESP (+ -24 (G :ESP S))
                                 (UPDATE-MEM
                                  (+ -12 (G :ESP S))
                                  (R32 (+ 16 (G :ESP S)) S)
                                  (+ -16 (G :ESP S))
                                  (R32 (+ 12 (G :ESP S)) S)
                                  (+ -20 (G :ESP S))
                                  (R32 (+ 4 (G :ESP S)) S)
                                  (+ -24 (G :ESP S))
                                  (+ 985 (SNPT-CODE-LOCATION))
                                  (INIT_PDTS-MODIFY
                                   (UPDATE-REGS
                                    :EAX (R32 (+ 8 (G :ESP S)) S)
                                    :EIP (+ 334 (SNPT-CODE-LOCATION))
                                    :ESP (+ -24 (G :ESP S))
                                    (UPDATE-MEM
                                     (+ -20 (G :ESP S))
                                     (R32 (+ 8 (G :ESP S)) S)
                                     (+ -24 (G :ESP S))
                                     (+ 944 (SNPT-CODE-LOCATION))
                                     (INIT_PDPT-MODIFY
                                      (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                   :EBP (+ -4 (G :ESP S))
                                                   :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                   :ESP (+ -24 (G :ESP S))
                                                   :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                   :F-OF
                                                   (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                       (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                   :F-SF
                                                   (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                   :F-ZF (ZF (+ -20 (G :ESP S)))
                                                   :IMME1 16
                                                   (UPDATE-MEM (+ -4 (G :ESP S))
                                                               (G :EBP S)
                                                               (+ -16 (G :ESP S))
                                                               (R32 (+ 8 (G :ESP S)) S)
                                                               (+ -20 (G :ESP S))
                                                               (R32 (+ 4 (G :ESP S)) S)
                                                               (+ -24 (G :ESP S))
                                                               (+ 927 (SNPT-CODE-LOCATION))
                                                               S))))))))))))
           ("Subgoal 2.1" :cases ((equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 0)
                                  (equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 1)
                                  (equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 2)
                                  (equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 3)))
           ("Subgoal 1"
            :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                             (i 0)
                             (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                             :EBP (+ -4 (G :ESP S))
                                             :EIP (+ 687 (SNPT-CODE-LOCATION))
                                             :ESP (+ -24 (G :ESP S))
                                             :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                             :F-OF
                                             (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                 (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                             :F-SF
                                             (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                             :F-ZF (ZF (+ -20 (G :ESP S)))
                                             :IMME1 16
                                             (UPDATE-MEM (+ -4 (G :ESP S))
                                                         (G :EBP S)
                                                         (+ -16 (G :ESP S))
                                                         (R32 (+ 8 (G :ESP S)) S)
                                                         (+ -20 (G :ESP S))
                                                         (R32 (+ 4 (G :ESP S)) S)
                                                         (+ -24 (G :ESP S))
                                                         (+ 927 (SNPT-CODE-LOCATION))
                                                         S))))
                  (:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                             (i 1)
                             (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                             :EBP (+ -4 (G :ESP S))
                                             :EIP (+ 687 (SNPT-CODE-LOCATION))
                                             :ESP (+ -24 (G :ESP S))
                                             :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                             :F-OF
                                             (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                 (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                             :F-SF
                                             (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                             :F-ZF (ZF (+ -20 (G :ESP S)))
                                             :IMME1 16
                                             (UPDATE-MEM (+ -4 (G :ESP S))
                                                         (G :EBP S)
                                                         (+ -16 (G :ESP S))
                                                         (R32 (+ 8 (G :ESP S)) S)
                                                         (+ -20 (G :ESP S))
                                                         (R32 (+ 4 (G :ESP S)) S)
                                                         (+ -24 (G :ESP S))
                                                         (+ 927 (SNPT-CODE-LOCATION))
                                                         S))))
                  (:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                             (i 2)
                             (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                             :EBP (+ -4 (G :ESP S))
                                             :EIP (+ 687 (SNPT-CODE-LOCATION))
                                             :ESP (+ -24 (G :ESP S))
                                             :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                             :F-OF
                                             (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                 (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                             :F-SF
                                             (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                             :F-ZF (ZF (+ -20 (G :ESP S)))
                                             :IMME1 16
                                             (UPDATE-MEM (+ -4 (G :ESP S))
                                                         (G :EBP S)
                                                         (+ -16 (G :ESP S))
                                                         (R32 (+ 8 (G :ESP S)) S)
                                                         (+ -20 (G :ESP S))
                                                         (R32 (+ 4 (G :ESP S)) S)
                                                         (+ -24 (G :ESP S))
                                                         (+ 927 (SNPT-CODE-LOCATION))
                                                         S))))
                  (:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                             (i 3)
                             (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                             :EBP (+ -4 (G :ESP S))
                                             :EIP (+ 687 (SNPT-CODE-LOCATION))
                                             :ESP (+ -24 (G :ESP S))
                                             :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                             :F-OF
                                             (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                 (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                             :F-SF
                                             (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                             :F-ZF (ZF (+ -20 (G :ESP S)))
                                             :IMME1 16
                                             (UPDATE-MEM (+ -4 (G :ESP S))
                                                         (G :EBP S)
                                                         (+ -16 (G :ESP S))
                                                         (R32 (+ 8 (G :ESP S)) S)
                                                         (+ -20 (G :ESP S))
                                                         (R32 (+ 4 (G :ESP S)) S)
                                                         (+ -24 (G :ESP S))
                                                         (+ 927 (SNPT-CODE-LOCATION))
                                                         S))))
                  (:instance |(r32 addr (sec_not_present-modify s))|
                             (addr (+ 24 (R32 (+ 4 (G :ESP S)) S)))
                             (s (UPDATE-REGS
                                 :EAX (R32 (+ 4 (G :ESP S)) S)
                                 :EIP (SNPT-CODE-LOCATION)
                                 :ESP (+ -24 (G :ESP S))
                                 (UPDATE-MEM
                                  (+ -12 (G :ESP S))
                                  (R32 (+ 16 (G :ESP S)) S)
                                  (+ -16 (G :ESP S))
                                  (R32 (+ 12 (G :ESP S)) S)
                                  (+ -20 (G :ESP S))
                                  (R32 (+ 4 (G :ESP S)) S)
                                  (+ -24 (G :ESP S))
                                  (+ 985 (SNPT-CODE-LOCATION))
                                  (INIT_PDTS-MODIFY
                                   (UPDATE-REGS
                                    :EAX (R32 (+ 8 (G :ESP S)) S)
                                    :EIP (+ 334 (SNPT-CODE-LOCATION))
                                    :ESP (+ -24 (G :ESP S))
                                    (UPDATE-MEM
                                     (+ -20 (G :ESP S))
                                     (R32 (+ 8 (G :ESP S)) S)
                                     (+ -24 (G :ESP S))
                                     (+ 944 (SNPT-CODE-LOCATION))
                                     (INIT_PDPT-MODIFY
                                      (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                   :EBP (+ -4 (G :ESP S))
                                                   :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                   :ESP (+ -24 (G :ESP S))
                                                   :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                   :F-OF
                                                   (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                       (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                   :F-SF
                                                   (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                   :F-ZF (ZF (+ -20 (G :ESP S)))
                                                   :IMME1 16
                                                   (UPDATE-MEM (+ -4 (G :ESP S))
                                                               (G :EBP S)
                                                               (+ -16 (G :ESP S))
                                                               (R32 (+ 8 (G :ESP S)) S)
                                                               (+ -20 (G :ESP S))
                                                               (R32 (+ 4 (G :ESP S)) S)
                                                               (+ -24 (G :ESP S))
                                                               (+ 927 (SNPT-CODE-LOCATION))
                                                               S))))))))))))
           ("Subgoal 1.1" :cases ((equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 0)
                                  (equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 1)
                                  (equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 2)
                                  (equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 3))))
   :otf-flg t)

 (defthm |(r32 addr (create_nested_pt-modify s)) --- sec_not_present|
   (implies (and (create_nested_pt-pre s)

                 (integerp i-prime)
                 (n32p (+ (* 8 I-PRIME)
                          (LOGAND 4294963200
                                  (R32 (+ (R32 (+ 8 (G :ESP S)) S)
                                          (* 4 (ASH (R32 (+ 12 (G :ESP S)) S) -30)))
                                       S))))
                 (n32p (+ 3
                          (* 8 I-PRIME)
                          (LOGAND 4294963200
                                  (R32 (+ (R32 (+ 8 (G :ESP S)) S)
                                          (* 4 (ASH (R32 (+ 12 (G :ESP S)) S) -30)))
                                       S))))
                 (<= (ASH (LOGAND 1071644672 (R32 (+ 12 (G :ESP S)) S))
                          -21)
                     i-prime)
                 (<= i-prime
                     (+ -1
                        (ASH (LOGAND 1071644672
                                     (+ (R32 (+ 12 (G :ESP S)) S)
                                        (R32 (+ 16 (G :ESP S)) S)))
                             -21)))
                 (disjointp (list (range (+ (* 8 I-PRIME)
                                            (LOGAND 4294963200
                                                    (R32 (+ (R32 (+ 8 (G :ESP S)) S)
                                                            (* 4 (ASH (R32 (+ 12 (G :ESP S)) S) -30)))
                                                         S)))
                                         0
                                         4)
                                  (range (g :esp s) -56 56))))
            (equal (r32 (+ (* 8 i-prime)
                           (LOGAND 4294963200
                                   (R32 (+ (* 4 (ASH (R32 (+ 12 (G :ESP S)) S) -30))
                                           (R32 (+ 8 (G :ESP S)) S))
                                        S)))
                        (create_nested_pt-modify s))
                   0))
   :hints (("Goal" :in-theory (disable |(logior 1 x)|
                                       ash-to-floor)
            :do-not '(generalize eliminate-destructors fertilize)
            :use ((:instance |(r32 addr (sec_not_present-modify s)) --- written to 1|
                             (i-prime i-prime)
                             (s (UPDATE-REGS
                                 :EAX (R32 (+ 4 (G :ESP S)) S)
                                 :EIP (SNPT-CODE-LOCATION)
                                 :ESP (+ -24 (G :ESP S))
                                 (UPDATE-MEM
                                  (+ -12 (G :ESP S))
                                  (R32 (+ 16 (G :ESP S)) S)
                                  (+ -16 (G :ESP S))
                                  (R32 (+ 12 (G :ESP S)) S)
                                  (+ -20 (G :ESP S))
                                  (R32 (+ 4 (G :ESP S)) S)
                                  (+ -24 (G :ESP S))
                                  (+ 985 (SNPT-CODE-LOCATION))
                                  (INIT_PDTS-MODIFY
                                   (UPDATE-REGS
                                    :EAX (R32 (+ 8 (G :ESP S)) S)
                                    :EIP (+ 334 (SNPT-CODE-LOCATION))
                                    :ESP (+ -24 (G :ESP S))
                                    (UPDATE-MEM
                                     (+ -20 (G :ESP S))
                                     (R32 (+ 8 (G :ESP S)) S)
                                     (+ -24 (G :ESP S))
                                     (+ 944 (SNPT-CODE-LOCATION))
                                     (INIT_PDPT-MODIFY
                                      (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                   :EBP (+ -4 (G :ESP S))
                                                   :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                   :ESP (+ -24 (G :ESP S))
                                                   :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                   :F-OF
                                                   (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                       (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                   :F-SF
                                                   (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                   :F-ZF (ZF (+ -20 (G :ESP S)))
                                                   :IMME1 16
                                                   (UPDATE-MEM (+ -4 (G :ESP S))
                                                               (G :EBP S)
                                                               (+ -16 (G :ESP S))
                                                               (R32 (+ 8 (G :ESP S)) S)
                                                               (+ -20 (G :ESP S))
                                                               (R32 (+ 4 (G :ESP S)) S)
                                                               (+ -24 (G :ESP S))
                                                               (+ 927 (SNPT-CODE-LOCATION))
                                                               S)))))))))))
            )

           ("Subgoal 4" :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                                         (i (ASH (R32 (+ 12 (G :ESP S)) S) -30))
                                         (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                         :EBP (+ -4 (G :ESP S))
                                                         :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                         :ESP (+ -24 (G :ESP S))
                                                         :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                         :F-OF
                                                         (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                             (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                         :F-SF
                                                         (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                         :F-ZF (ZF (+ -20 (G :ESP S)))
                                                         :IMME1 16
                                                         (UPDATE-MEM (+ -4 (G :ESP S))
                                                                     (G :EBP S)
                                                                     (+ -16 (G :ESP S))
                                                                     (R32 (+ 8 (G :ESP S)) S)
                                                                     (+ -20 (G :ESP S))
                                                                     (R32 (+ 4 (G :ESP S)) S)
                                                                     (+ -24 (G :ESP S))
                                                                     (+ 927 (SNPT-CODE-LOCATION))
                                                                     S))))))

           ("Subgoal 2" :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                                         (i (ASH (R32 (+ 12 (G :ESP S)) S) -30))
                                         (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                         :EBP (+ -4 (G :ESP S))
                                                         :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                         :ESP (+ -24 (G :ESP S))
                                                         :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                         :F-OF
                                                         (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                             (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                         :F-SF
                                                         (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                         :F-ZF (ZF (+ -20 (G :ESP S)))
                                                         :IMME1 16
                                                         (UPDATE-MEM (+ -4 (G :ESP S))
                                                                     (G :EBP S)
                                                                     (+ -16 (G :ESP S))
                                                                     (R32 (+ 8 (G :ESP S)) S)
                                                                     (+ -20 (G :ESP S))
                                                                     (R32 (+ 4 (G :ESP S)) S)
                                                                     (+ -24 (G :ESP S))
                                                                     (+ 927 (SNPT-CODE-LOCATION))
                                                                     S))))))
           ("Subgoal 2.2" :cases ((equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 0)
                                  (equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 1)
                                  (equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 2)
                                  (equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 3)))
           )
   :otf-flg t)

 (local
  (encapsulate
   ()

   (local
    (defthm crock-333-1
      (not (memberp x nil))
      :hints (("Goal" :in-theory (enable memberp)))))

   (local
    (defthm crock-333
      (implies (and (integerp x)
                    (integerp start)
                    (integerp end)
                    (< x start)
                    (not (memberp x acc)))
               (not (memberp x (range-1 start end acc))))
      :hints (("Goal" :in-theory (enable range-1
                                         memberp)))))

   (local
    (defthm crock-334
      (implies (and (integerp x)
                    (integerp start)
                    (integerp end)
                    (< end x)
                    (not (memberp x acc)))
               (not (memberp x (range-1 start end acc))))
      :hints (("Goal" :in-theory (enable range-1
                                         memberp)))))

   (local
    (defthm crock-335-1
      (implies (memberp x acc)
               (memberp x (range-1 start end acc)))
      :hints (("Goal" :in-theory (enable range-1
                                         memberp)))))

   (local
    (defthm crock-335
      (implies (and (integerp x)
                    (integerp start)
                    (integerp end)
                    (<= start end)
                    (<= start x)
                    (<= x end))
               (memberp x (range-1 start end acc)))
      :hints (("Goal" :in-theory (enable range-1
                                         memberp)
               :expand ((RANGE-1 END END ACC)
                        (RANGE-1 (+ -1 END) END ACC)
                        (RANGE-1 (+ -1 END)
                                 (+ -1 END)
                                 (CONS END ACC)))))))

   (defthm extra-disjointp-thm
     (implies (and (integerp x)
                   (integerp base)
                   (integerp offset)
                   (integerp length)
                   (< 0 length))
              (equal (disjointp (list (list x)
                                      (range base offset length)))
                     (or (< x
                            (+ base offset))
                         (<= (+ base offset length)
                             x))))
     :hints (("Goal" :in-theory (enable disjointp
                                        disjointp-1
                                        disjoint-bags-p
                                        range
                                        range-1)))
     :otf-flg t)
   ))

;;; but lets not introduce extra case splits.  I do not want to have
;;; to redo the hints for
;;; |(r32 addr (create_nested_pt-modify s)) --- init_pdts| and it is
;;; already too slow.
 (local
  (in-theory (disable extra-disjointp-thm)))



;;; Very slow!
;;; We have to do some extra reasoning about disjointp here.
 (defthm |(r32 addr (create_nested_pt-modify s)) --- init_pdts --- 1|
   (implies (and (create_nested_pt-pre s)

                 (integerp i-prime)
                 (<= 0 i-prime)
                 (<= i-prime 3)
                 (integerp j-prime)
                 (<= 0 j-prime)
                 (<= j-prime 511)

                 (N32P (+ (* 8 J-PRIME)
                          (R32 (+ (* 4 I-PRIME)
                                  (R32 (+ 8 (G :ESP S)) S))
                               S)))
                 (N32P (+ 3 (* 8 J-PRIME)
                          (R32 (+ (* 4 I-PRIME)
                                  (R32 (+ 8 (G :ESP S)) S))
                               S)))

                 (disjointp (list (list (* 8 j-prime))
                                  (range (* 8
                                            (ASH (LOGAND 1071644672 (R32 (+ 12 (G :ESP S)) S))
                                                 -21))
                                         0
                                         (+ (* -8
                                               (ASH (LOGAND 1071644672 (R32 (+ 12 (G :ESP S)) S))
                                                    -21))
                                            (* 8
                                               (ASH (LOGAND 1071644672
                                                            (+ (R32 (+ 12 (G :ESP S)) S)
                                                               (R32 (+ 16 (G :ESP S)) S)))
                                                    -21))))))
                 )
            (equal (r32 (+ (* 8 j-prime)
                           (R32 (+ (* 4 i-prime)
                                   (R32 (+ 8 (G :ESP S)) S))
                                S))
                        (create_nested_pt-modify s))
                   (LOGIOR 231
                           (+ (* 512 I-PRIME 2097152)
                              (* 2097152 J-PRIME)))))
   :hints (("Goal" :in-theory (disable |(logior 1 x)|
                                       ash-to-floor)
            :do-not '(generalize eliminate-destructors fertilize)
            :use ((:instance |(r32 addr (sec_not_present-modify s))|
                             (addr (+ (* 8 J-PRIME)
                                      (R32 (+ (* 4 I-PRIME)
                                              (R32 (+ 8 (G :ESP S)) S))
                                           S)))
                             (s (UPDATE-REGS
                                 :EAX (R32 (+ 4 (G :ESP S)) S)
                                 :EIP (SNPT-CODE-LOCATION)
                                 :ESP (+ -24 (G :ESP S))
                                 (UPDATE-MEM
                                  (+ -12 (G :ESP S))
                                  (R32 (+ 16 (G :ESP S)) S)
                                  (+ -16 (G :ESP S))
                                  (R32 (+ 12 (G :ESP S)) S)
                                  (+ -20 (G :ESP S))
                                  (R32 (+ 4 (G :ESP S)) S)
                                  (+ -24 (G :ESP S))
                                  (+ 985 (SNPT-CODE-LOCATION))
                                  (INIT_PDTS-MODIFY
                                   (UPDATE-REGS
                                    :EAX (R32 (+ 8 (G :ESP S)) S)
                                    :EIP (+ 334 (SNPT-CODE-LOCATION))
                                    :ESP (+ -24 (G :ESP S))
                                    (UPDATE-MEM
                                     (+ -20 (G :ESP S))
                                     (R32 (+ 8 (G :ESP S)) S)
                                     (+ -24 (G :ESP S))
                                     (+ 944 (SNPT-CODE-LOCATION))
                                     (INIT_PDPT-MODIFY
                                      (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                   :EBP (+ -4 (G :ESP S))
                                                   :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                   :ESP (+ -24 (G :ESP S))
                                                   :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                   :F-OF
                                                   (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                       (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                   :F-SF
                                                   (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                   :F-ZF (ZF (+ -20 (G :ESP S)))
                                                   :IMME1 16
                                                   (UPDATE-MEM (+ -4 (G :ESP S))
                                                               (G :EBP S)
                                                               (+ -16 (G :ESP S))
                                                               (R32 (+ 8 (G :ESP S)) S)
                                                               (+ -20 (G :ESP S))
                                                               (R32 (+ 4 (G :ESP S)) S)
                                                               (+ -24 (G :ESP S))
                                                               (+ 927 (SNPT-CODE-LOCATION))
                                                               S)))))))))))
            )
           ("Subgoal 3" :cases ((equal i-prime 0)
                                (equal i-prime 1)
                                (equal i-prime 2)
                                (equal i-prime 3)))
           ("Subgoal 3.4" :use ((:instance |(r32 addr (init_pdts-modify s)) --- written to 1|
                                           (j-prime j-prime)
                                           (i-prime 0)
                                           (s (UPDATE-REGS
                                               :EAX (R32 (+ 8 (G :ESP S)) S)
                                               :EIP (+ 334 (SNPT-CODE-LOCATION))
                                               :ESP (+ -24 (G :ESP S))
                                               (UPDATE-MEM
                                                (+ -20 (G :ESP S))
                                                (R32 (+ 8 (G :ESP S)) S)
                                                (+ -24 (G :ESP S))
                                                (+ 944 (SNPT-CODE-LOCATION))
                                                (INIT_PDPT-MODIFY
                                                 (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                              :EBP (+ -4 (G :ESP S))
                                                              :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                              :ESP (+ -24 (G :ESP S))
                                                              :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                              :F-OF
                                                              (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                                  (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                              :F-SF
                                                              (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                              :F-ZF (ZF (+ -20 (G :ESP S)))
                                                              :IMME1 16
                                                              (UPDATE-MEM (+ -4 (G :ESP S))
                                                                          (G :EBP S)
                                                                          (+ -16 (G :ESP S))
                                                                          (R32 (+ 8 (G :ESP S)) S)
                                                                          (+ -20 (G :ESP S))
                                                                          (R32 (+ 4 (G :ESP S)) S)
                                                                          (+ -24 (G :ESP S))
                                                                          (+ 927 (SNPT-CODE-LOCATION))
                                                                          S)))))))))
           ("Subgoal 3.3" :use ((:instance |(r32 addr (init_pdts-modify s)) --- written to 1|
                                           (j-prime j-prime)
                                           (i-prime 1)
                                           (s (UPDATE-REGS
                                               :EAX (R32 (+ 8 (G :ESP S)) S)
                                               :EIP (+ 334 (SNPT-CODE-LOCATION))
                                               :ESP (+ -24 (G :ESP S))
                                               (UPDATE-MEM
                                                (+ -20 (G :ESP S))
                                                (R32 (+ 8 (G :ESP S)) S)
                                                (+ -24 (G :ESP S))
                                                (+ 944 (SNPT-CODE-LOCATION))
                                                (INIT_PDPT-MODIFY
                                                 (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                              :EBP (+ -4 (G :ESP S))
                                                              :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                              :ESP (+ -24 (G :ESP S))
                                                              :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                              :F-OF
                                                              (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                                  (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                              :F-SF
                                                              (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                              :F-ZF (ZF (+ -20 (G :ESP S)))
                                                              :IMME1 16
                                                              (UPDATE-MEM (+ -4 (G :ESP S))
                                                                          (G :EBP S)
                                                                          (+ -16 (G :ESP S))
                                                                          (R32 (+ 8 (G :ESP S)) S)
                                                                          (+ -20 (G :ESP S))
                                                                          (R32 (+ 4 (G :ESP S)) S)
                                                                          (+ -24 (G :ESP S))
                                                                          (+ 927 (SNPT-CODE-LOCATION))
                                                                          S)))))))))
           ("Subgoal 3.2" :use ((:instance |(r32 addr (init_pdts-modify s)) --- written to 1|
                                           (j-prime j-prime)
                                           (i-prime 2)
                                           (s (UPDATE-REGS
                                               :EAX (R32 (+ 8 (G :ESP S)) S)
                                               :EIP (+ 334 (SNPT-CODE-LOCATION))
                                               :ESP (+ -24 (G :ESP S))
                                               (UPDATE-MEM
                                                (+ -20 (G :ESP S))
                                                (R32 (+ 8 (G :ESP S)) S)
                                                (+ -24 (G :ESP S))
                                                (+ 944 (SNPT-CODE-LOCATION))
                                                (INIT_PDPT-MODIFY
                                                 (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                              :EBP (+ -4 (G :ESP S))
                                                              :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                              :ESP (+ -24 (G :ESP S))
                                                              :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                              :F-OF
                                                              (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                                  (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                              :F-SF
                                                              (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                              :F-ZF (ZF (+ -20 (G :ESP S)))
                                                              :IMME1 16
                                                              (UPDATE-MEM (+ -4 (G :ESP S))
                                                                          (G :EBP S)
                                                                          (+ -16 (G :ESP S))
                                                                          (R32 (+ 8 (G :ESP S)) S)
                                                                          (+ -20 (G :ESP S))
                                                                          (R32 (+ 4 (G :ESP S)) S)
                                                                          (+ -24 (G :ESP S))
                                                                          (+ 927 (SNPT-CODE-LOCATION))
                                                                          S)))))))))
           ("Subgoal 3.1" :use ((:instance |(r32 addr (init_pdts-modify s)) --- written to 1|
                                           (j-prime j-prime)
                                           (i-prime 3)
                                           (s (UPDATE-REGS
                                               :EAX (R32 (+ 8 (G :ESP S)) S)
                                               :EIP (+ 334 (SNPT-CODE-LOCATION))
                                               :ESP (+ -24 (G :ESP S))
                                               (UPDATE-MEM
                                                (+ -20 (G :ESP S))
                                                (R32 (+ 8 (G :ESP S)) S)
                                                (+ -24 (G :ESP S))
                                                (+ 944 (SNPT-CODE-LOCATION))
                                                (INIT_PDPT-MODIFY
                                                 (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                              :EBP (+ -4 (G :ESP S))
                                                              :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                              :ESP (+ -24 (G :ESP S))
                                                              :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                              :F-OF
                                                              (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                                  (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                              :F-SF
                                                              (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                              :F-ZF (ZF (+ -20 (G :ESP S)))
                                                              :IMME1 16
                                                              (UPDATE-MEM (+ -4 (G :ESP S))
                                                                          (G :EBP S)
                                                                          (+ -16 (G :ESP S))
                                                                          (R32 (+ 8 (G :ESP S)) S)
                                                                          (+ -20 (G :ESP S))
                                                                          (R32 (+ 4 (G :ESP S)) S)
                                                                          (+ -24 (G :ESP S))
                                                                          (+ 927 (SNPT-CODE-LOCATION))
                                                                          S)))))))))
           ("Subgoal 1" :cases ((equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 0)
                                (equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 1)
                                (equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 2)
                                (equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 3)))
           ("Subgoal 1.4" :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                                           (i 0)
                                           (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                           :EBP (+ -4 (G :ESP S))
                                                           :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                           :ESP (+ -24 (G :ESP S))
                                                           :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                           :F-OF
                                                           (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                               (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                           :F-SF
                                                           (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                           :F-ZF (ZF (+ -20 (G :ESP S)))
                                                           :IMME1 16
                                                           (UPDATE-MEM (+ -4 (G :ESP S))
                                                                       (G :EBP S)
                                                                       (+ -16 (G :ESP S))
                                                                       (R32 (+ 8 (G :ESP S)) S)
                                                                       (+ -20 (G :ESP S))
                                                                       (R32 (+ 4 (G :ESP S)) S)
                                                                       (+ -24 (G :ESP S))
                                                                       (+ 927 (SNPT-CODE-LOCATION))
                                                                       S))))))
           ("Subgoal 1.4'''" :cases ((equal i-prime 0)
                                     (equal i-prime 1)
                                     (equal i-prime 2)
                                     (equal i-prime 3)))
           ("Subgoal 1.4.4" :in-theory (e/d  (extra-disjointp-thm)
                                             (|(logior 1 x)|
                                              ash-to-floor)))
           ("Subgoal 1.3" :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                                           (i 1)
                                           (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                           :EBP (+ -4 (G :ESP S))
                                                           :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                           :ESP (+ -24 (G :ESP S))
                                                           :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                           :F-OF
                                                           (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                               (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                           :F-SF
                                                           (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                           :F-ZF (ZF (+ -20 (G :ESP S)))
                                                           :IMME1 16
                                                           (UPDATE-MEM (+ -4 (G :ESP S))
                                                                       (G :EBP S)
                                                                       (+ -16 (G :ESP S))
                                                                       (R32 (+ 8 (G :ESP S)) S)
                                                                       (+ -20 (G :ESP S))
                                                                       (R32 (+ 4 (G :ESP S)) S)
                                                                       (+ -24 (G :ESP S))
                                                                       (+ 927 (SNPT-CODE-LOCATION))
                                                                       S))))))
           ("Subgoal 1.3'''" :cases ((equal i-prime 0)
                                     (equal i-prime 1)
                                     (equal i-prime 2)
                                     (equal i-prime 3)))
           ("Subgoal 1.3.3" :in-theory (e/d  (extra-disjointp-thm)
                                             (|(logior 1 x)|
                                              ash-to-floor)))
           ("Subgoal 1.2" :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                                           (i 2)
                                           (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                           :EBP (+ -4 (G :ESP S))
                                                           :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                           :ESP (+ -24 (G :ESP S))
                                                           :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                           :F-OF
                                                           (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                               (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                           :F-SF
                                                           (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                           :F-ZF (ZF (+ -20 (G :ESP S)))
                                                           :IMME1 16
                                                           (UPDATE-MEM (+ -4 (G :ESP S))
                                                                       (G :EBP S)
                                                                       (+ -16 (G :ESP S))
                                                                       (R32 (+ 8 (G :ESP S)) S)
                                                                       (+ -20 (G :ESP S))
                                                                       (R32 (+ 4 (G :ESP S)) S)
                                                                       (+ -24 (G :ESP S))
                                                                       (+ 927 (SNPT-CODE-LOCATION))
                                                                       S))))))
           ("Subgoal 1.2'''" :cases ((equal i-prime 0)
                                     (equal i-prime 1)
                                     (equal i-prime 2)
                                     (equal i-prime 3)))
           ("Subgoal 1.2.2" :in-theory (e/d  (extra-disjointp-thm)
                                             (|(logior 1 x)|
                                              ash-to-floor)))
           ("Subgoal 1.1" :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                                           (i 3)
                                           (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                           :EBP (+ -4 (G :ESP S))
                                                           :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                           :ESP (+ -24 (G :ESP S))
                                                           :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                           :F-OF
                                                           (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                               (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                           :F-SF
                                                           (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                           :F-ZF (ZF (+ -20 (G :ESP S)))
                                                           :IMME1 16
                                                           (UPDATE-MEM (+ -4 (G :ESP S))
                                                                       (G :EBP S)
                                                                       (+ -16 (G :ESP S))
                                                                       (R32 (+ 8 (G :ESP S)) S)
                                                                       (+ -20 (G :ESP S))
                                                                       (R32 (+ 4 (G :ESP S)) S)
                                                                       (+ -24 (G :ESP S))
                                                                       (+ 927 (SNPT-CODE-LOCATION))
                                                                       S))))))
           ("Subgoal 1.1'''" :cases ((equal i-prime 0)
                                     (equal i-prime 1)
                                     (equal i-prime 2)
                                     (equal i-prime 3)))
           ("Subgoal 1.1.1" :in-theory (e/d  (extra-disjointp-thm)
                                             (|(logior 1 x)|
                                              ash-to-floor)))
           )
   :otf-flg t)



 (defthm |(r32 addr (create_nested_pt-modify s)) --- init_pdts --- 2|
   (implies (and (create_nested_pt-pre s)

                 (integerp i-prime)
                 (<= 0 i-prime)
                 (<= i-prime 3)
                 (integerp j-prime)
                 (<= 0 j-prime)
                 (<= j-prime 511)

                 (N32P (+ (* 8 J-PRIME)
                          (R32 (+ (* 4 I-PRIME)
                                  (R32 (+ 8 (G :ESP S)) S))
                               S)))
                 (N32P (+ 3 (* 8 J-PRIME)
                          (R32 (+ (* 4 I-PRIME)
                                  (R32 (+ 8 (G :ESP S)) S))
                               S)))

                 (not (equal i-prime
                             (ash (R32 (+ 12 (G :ESP S)) S) -30)))
                 )
            (equal (r32 (+ (* 8 j-prime)
                           (R32 (+ (* 4 i-prime)
                                   (R32 (+ 8 (G :ESP S)) S))
                                S))
                        (create_nested_pt-modify s))
                   (LOGIOR 231
                           (+ (* 512 I-PRIME 2097152)
                              (* 2097152 J-PRIME)))))
   :hints (("Goal" :in-theory (disable |(logior 1 x)|
                                       ash-to-floor)
            :do-not '(generalize eliminate-destructors fertilize)
            :use ((:instance |(r32 addr (sec_not_present-modify s))|
                             (addr (+ (* 8 J-PRIME)
                                      (R32 (+ (* 4 I-PRIME)
                                              (R32 (+ 8 (G :ESP S)) S))
                                           S)))
                             (s (UPDATE-REGS
                                 :EAX (R32 (+ 4 (G :ESP S)) S)
                                 :EIP (SNPT-CODE-LOCATION)
                                 :ESP (+ -24 (G :ESP S))
                                 (UPDATE-MEM
                                  (+ -12 (G :ESP S))
                                  (R32 (+ 16 (G :ESP S)) S)
                                  (+ -16 (G :ESP S))
                                  (R32 (+ 12 (G :ESP S)) S)
                                  (+ -20 (G :ESP S))
                                  (R32 (+ 4 (G :ESP S)) S)
                                  (+ -24 (G :ESP S))
                                  (+ 985 (SNPT-CODE-LOCATION))
                                  (INIT_PDTS-MODIFY
                                   (UPDATE-REGS
                                    :EAX (R32 (+ 8 (G :ESP S)) S)
                                    :EIP (+ 334 (SNPT-CODE-LOCATION))
                                    :ESP (+ -24 (G :ESP S))
                                    (UPDATE-MEM
                                     (+ -20 (G :ESP S))
                                     (R32 (+ 8 (G :ESP S)) S)
                                     (+ -24 (G :ESP S))
                                     (+ 944 (SNPT-CODE-LOCATION))
                                     (INIT_PDPT-MODIFY
                                      (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                   :EBP (+ -4 (G :ESP S))
                                                   :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                   :ESP (+ -24 (G :ESP S))
                                                   :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                   :F-OF
                                                   (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                       (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                   :F-SF
                                                   (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                   :F-ZF (ZF (+ -20 (G :ESP S)))
                                                   :IMME1 16
                                                   (UPDATE-MEM (+ -4 (G :ESP S))
                                                               (G :EBP S)
                                                               (+ -16 (G :ESP S))
                                                               (R32 (+ 8 (G :ESP S)) S)
                                                               (+ -20 (G :ESP S))
                                                               (R32 (+ 4 (G :ESP S)) S)
                                                               (+ -24 (G :ESP S))
                                                               (+ 927 (SNPT-CODE-LOCATION))
                                                               S)))))))))))
            )
           ("Subgoal 3" :cases ((equal i-prime 0)
                                (equal i-prime 1)
                                (equal i-prime 2)
                                (equal i-prime 3)))
           ("Subgoal 3.4" :use ((:instance |(r32 addr (init_pdts-modify s)) --- written to 1|
                                           (j-prime j-prime)
                                           (i-prime 0)
                                           (s (UPDATE-REGS
                                               :EAX (R32 (+ 8 (G :ESP S)) S)
                                               :EIP (+ 334 (SNPT-CODE-LOCATION))
                                               :ESP (+ -24 (G :ESP S))
                                               (UPDATE-MEM
                                                (+ -20 (G :ESP S))
                                                (R32 (+ 8 (G :ESP S)) S)
                                                (+ -24 (G :ESP S))
                                                (+ 944 (SNPT-CODE-LOCATION))
                                                (INIT_PDPT-MODIFY
                                                 (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                              :EBP (+ -4 (G :ESP S))
                                                              :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                              :ESP (+ -24 (G :ESP S))
                                                              :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                              :F-OF
                                                              (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                                  (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                              :F-SF
                                                              (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                              :F-ZF (ZF (+ -20 (G :ESP S)))
                                                              :IMME1 16
                                                              (UPDATE-MEM (+ -4 (G :ESP S))
                                                                          (G :EBP S)
                                                                          (+ -16 (G :ESP S))
                                                                          (R32 (+ 8 (G :ESP S)) S)
                                                                          (+ -20 (G :ESP S))
                                                                          (R32 (+ 4 (G :ESP S)) S)
                                                                          (+ -24 (G :ESP S))
                                                                          (+ 927 (SNPT-CODE-LOCATION))
                                                                          S)))))))))

           ("Subgoal 3.3" :use ((:instance |(r32 addr (init_pdts-modify s)) --- written to 1|
                                           (j-prime j-prime)
                                           (i-prime 1)
                                           (s (UPDATE-REGS
                                               :EAX (R32 (+ 8 (G :ESP S)) S)
                                               :EIP (+ 334 (SNPT-CODE-LOCATION))
                                               :ESP (+ -24 (G :ESP S))
                                               (UPDATE-MEM
                                                (+ -20 (G :ESP S))
                                                (R32 (+ 8 (G :ESP S)) S)
                                                (+ -24 (G :ESP S))
                                                (+ 944 (SNPT-CODE-LOCATION))
                                                (INIT_PDPT-MODIFY
                                                 (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                              :EBP (+ -4 (G :ESP S))
                                                              :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                              :ESP (+ -24 (G :ESP S))
                                                              :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                              :F-OF
                                                              (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                                  (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                              :F-SF
                                                              (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                              :F-ZF (ZF (+ -20 (G :ESP S)))
                                                              :IMME1 16
                                                              (UPDATE-MEM (+ -4 (G :ESP S))
                                                                          (G :EBP S)
                                                                          (+ -16 (G :ESP S))
                                                                          (R32 (+ 8 (G :ESP S)) S)
                                                                          (+ -20 (G :ESP S))
                                                                          (R32 (+ 4 (G :ESP S)) S)
                                                                          (+ -24 (G :ESP S))
                                                                          (+ 927 (SNPT-CODE-LOCATION))
                                                                          S)))))))))

           ("Subgoal 3.2" :use ((:instance |(r32 addr (init_pdts-modify s)) --- written to 1|
                                           (j-prime j-prime)
                                           (i-prime 2)
                                           (s (UPDATE-REGS
                                               :EAX (R32 (+ 8 (G :ESP S)) S)
                                               :EIP (+ 334 (SNPT-CODE-LOCATION))
                                               :ESP (+ -24 (G :ESP S))
                                               (UPDATE-MEM
                                                (+ -20 (G :ESP S))
                                                (R32 (+ 8 (G :ESP S)) S)
                                                (+ -24 (G :ESP S))
                                                (+ 944 (SNPT-CODE-LOCATION))
                                                (INIT_PDPT-MODIFY
                                                 (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                              :EBP (+ -4 (G :ESP S))
                                                              :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                              :ESP (+ -24 (G :ESP S))
                                                              :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                              :F-OF
                                                              (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                                  (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                              :F-SF
                                                              (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                              :F-ZF (ZF (+ -20 (G :ESP S)))
                                                              :IMME1 16
                                                              (UPDATE-MEM (+ -4 (G :ESP S))
                                                                          (G :EBP S)
                                                                          (+ -16 (G :ESP S))
                                                                          (R32 (+ 8 (G :ESP S)) S)
                                                                          (+ -20 (G :ESP S))
                                                                          (R32 (+ 4 (G :ESP S)) S)
                                                                          (+ -24 (G :ESP S))
                                                                          (+ 927 (SNPT-CODE-LOCATION))
                                                                          S)))))))))

           ("Subgoal 3.1" :use ((:instance |(r32 addr (init_pdts-modify s)) --- written to 1|
                                           (j-prime j-prime)
                                           (i-prime 3)
                                           (s (UPDATE-REGS
                                               :EAX (R32 (+ 8 (G :ESP S)) S)
                                               :EIP (+ 334 (SNPT-CODE-LOCATION))
                                               :ESP (+ -24 (G :ESP S))
                                               (UPDATE-MEM
                                                (+ -20 (G :ESP S))
                                                (R32 (+ 8 (G :ESP S)) S)
                                                (+ -24 (G :ESP S))
                                                (+ 944 (SNPT-CODE-LOCATION))
                                                (INIT_PDPT-MODIFY
                                                 (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                              :EBP (+ -4 (G :ESP S))
                                                              :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                              :ESP (+ -24 (G :ESP S))
                                                              :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                              :F-OF
                                                              (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                                  (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                              :F-SF
                                                              (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                              :F-ZF (ZF (+ -20 (G :ESP S)))
                                                              :IMME1 16
                                                              (UPDATE-MEM (+ -4 (G :ESP S))
                                                                          (G :EBP S)
                                                                          (+ -16 (G :ESP S))
                                                                          (R32 (+ 8 (G :ESP S)) S)
                                                                          (+ -20 (G :ESP S))
                                                                          (R32 (+ 4 (G :ESP S)) S)
                                                                          (+ -24 (G :ESP S))
                                                                          (+ 927 (SNPT-CODE-LOCATION))
                                                                          S)))))))))
           ("Subgoal 1" :cases ((equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 0)
                                (equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 1)
                                (equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 2)
                                (equal (ASH (R32 (+ 12 (G :ESP S)) S) -30) 3)))
           ("Subgoal 1.4" :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                                           (i 0)
                                           (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                           :EBP (+ -4 (G :ESP S))
                                                           :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                           :ESP (+ -24 (G :ESP S))
                                                           :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                           :F-OF
                                                           (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                               (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                           :F-SF
                                                           (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                           :F-ZF (ZF (+ -20 (G :ESP S)))
                                                           :IMME1 16
                                                           (UPDATE-MEM (+ -4 (G :ESP S))
                                                                       (G :EBP S)
                                                                       (+ -16 (G :ESP S))
                                                                       (R32 (+ 8 (G :ESP S)) S)
                                                                       (+ -20 (G :ESP S))
                                                                       (R32 (+ 4 (G :ESP S)) S)
                                                                       (+ -24 (G :ESP S))
                                                                       (+ 927 (SNPT-CODE-LOCATION))
                                                                       S))))))
           ("Subgoal 1.4'''" :cases ((equal i-prime 0)
                                     (equal i-prime 1)
                                     (equal i-prime 2)
                                     (equal i-prime 3)))
           ("Subgoal 1.3" :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                                           (i 1)
                                           (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                           :EBP (+ -4 (G :ESP S))
                                                           :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                           :ESP (+ -24 (G :ESP S))
                                                           :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                           :F-OF
                                                           (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                               (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                           :F-SF
                                                           (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                           :F-ZF (ZF (+ -20 (G :ESP S)))
                                                           :IMME1 16
                                                           (UPDATE-MEM (+ -4 (G :ESP S))
                                                                       (G :EBP S)
                                                                       (+ -16 (G :ESP S))
                                                                       (R32 (+ 8 (G :ESP S)) S)
                                                                       (+ -20 (G :ESP S))
                                                                       (R32 (+ 4 (G :ESP S)) S)
                                                                       (+ -24 (G :ESP S))
                                                                       (+ 927 (SNPT-CODE-LOCATION))
                                                                       S))))))
           ("Subgoal 1.3'''" :cases ((equal i-prime 0)
                                     (equal i-prime 1)
                                     (equal i-prime 2)
                                     (equal i-prime 3)))
           ("Subgoal 1.2" :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                                           (i 2)
                                           (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                           :EBP (+ -4 (G :ESP S))
                                                           :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                           :ESP (+ -24 (G :ESP S))
                                                           :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                           :F-OF
                                                           (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                               (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                           :F-SF
                                                           (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                           :F-ZF (ZF (+ -20 (G :ESP S)))
                                                           :IMME1 16
                                                           (UPDATE-MEM (+ -4 (G :ESP S))
                                                                       (G :EBP S)
                                                                       (+ -16 (G :ESP S))
                                                                       (R32 (+ 8 (G :ESP S)) S)
                                                                       (+ -20 (G :ESP S))
                                                                       (R32 (+ 4 (G :ESP S)) S)
                                                                       (+ -24 (G :ESP S))
                                                                       (+ 927 (SNPT-CODE-LOCATION))
                                                                       S))))))
           ("Subgoal 1.2'''" :cases ((equal i-prime 0)
                                     (equal i-prime 1)
                                     (equal i-prime 2)
                                     (equal i-prime 3)))
           ("Subgoal 1.1" :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                                           (i 3)
                                           (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S)) S)
                                                           :EBP (+ -4 (G :ESP S))
                                                           :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                           :ESP (+ -24 (G :ESP S))
                                                           :F-CF (SUBL-CF 16 (+ -4 (G :ESP S)))
                                                           :F-OF
                                                           (OF (N32-TO-I32 (+ -20 (G :ESP S)))
                                                               (+ -16 (N32-TO-I32 (+ -4 (G :ESP S)))))
                                                           :F-SF
                                                           (SF (N32-TO-I32 (+ -20 (G :ESP S))))
                                                           :F-ZF (ZF (+ -20 (G :ESP S)))
                                                           :IMME1 16
                                                           (UPDATE-MEM (+ -4 (G :ESP S))
                                                                       (G :EBP S)
                                                                       (+ -16 (G :ESP S))
                                                                       (R32 (+ 8 (G :ESP S)) S)
                                                                       (+ -20 (G :ESP S))
                                                                       (R32 (+ 4 (G :ESP S)) S)
                                                                       (+ -24 (G :ESP S))
                                                                       (+ 927 (SNPT-CODE-LOCATION))
                                                                       S))))))
           ("Subgoal 1.1'''" :cases ((equal i-prime 0)
                                     (equal i-prime 1)
                                     (equal i-prime 2)
                                     (equal i-prime 3)))
           )
   :otf-flg t)


;;; |(r32 addr (sec_not_present-modify s))|







 )



(defun create_nested_pt-assertion (s0 s1)
  (cond ((not (in-create_nested_pt s1))
         ;; exit
         (equal s1 (create_nested_pt-modify s0)))
        ((equal (g :eip s1)
                (+ *CREATE_NESTED_PT* (snpt-code-location)))
         ;; start
         (and (create_nested_pt-pre s1)
              (equal s1 s0)))
        (t
         'NIL)))


(ENCAPSULATE
 NIL

 ;; at least $$$PRESUB-IMPLIES-INSUB is much faster with this
 (local (include-book "arithmetic-5/top" :dir :system))



 (local
  (defthm ash-thm-100
    (implies (n32p x)
             (and (<= 0 (ash x -30))
                  (< (ash x -30) 4)))
    :hints (("Goal" :in-theory (enable ash-to-floor)))
    :rule-classes :linear))

 (local
  (encapsulate
   ()

   (local
    (defthm break-logand-apart
      (implies (and (integerp x)
                    (integerp y))
               (equal (logand x y)
                      (+ (* 2 (logand (floor x 2) (floor y 2)))
                         (logand (mod x 2) (mod y 2)))))
      :rule-classes nil))

   (defthm logior-thm-100
     (equal (logand -4096
                    (logior 1 x))
            (logand -4096 x))
     :hints (("Goal" :in-theory (disable |(logior 1 x)|
                                         |(floor x 2)|
                                         |(logior (floor x 2) (floor y 2))|)
              :use ((:instance break-logand-apart
                               (x -4096)
                               (y (logior 1 x)))
                    (:instance break-logand-apart
                               (x -4096)
                               (y x))
                    (:instance |(logior (floor x 2) (floor y 2))|
                               (x 1)
                               (y x)))))
     )
   ))

 (encapsulate
  ()

  (defthm crock-200
    (implies (and (integerp x)
                  (n32p x))
             (equal (logand -4096 x)
                    (logand 4294963200 x)))
    :hints (("Goal" :use ((:instance
                           (:theorem
                            (equal (logand (logand x y) z)
                                   (logand x (logand y z))))
                           (x -4096)
                           (y (+ -1 (expt 2 32)))
                           (z x))))))

  (defthm ash-thm-103
    (implies (y86-p s1)
             (equal (LOGAND 4294963200
                            (LOGIOR 1
                                    (R32 addr
                                         S1)))
                    (logand -4096 (r32 addr s1))))
    :hints (("Goal" :in-theory (disable |(logior 1 x)|
                                        logior-thm-100)
                    :use ((:instance logior-thm-100
                                     (x (R32 addr
                                         S1)))))))
  )

 (local
  (defthm ash-thm-101
    (<= (ash (logand 1071644672 x)
             -21)
        511)
    :hints (("Goal" :in-theory (enable ash-to-floor)))
    :rule-classes :linear))

 (local
  (defthm ash-thm-102
    (<= 0
        (ash (logand 1071644672 x)
             -21))
    :hints (("Goal" :in-theory (enable ash-to-floor)))
    :rule-classes :linear))

 (LOCAL (DEFTHEORY USER-THEORY (CURRENT-THEORY :HERE)))
 (LOCAL
  (ENCAPSULATE
   NIL
   (LOCAL (DEFTHEORY SUBTHEORY (CURRENT-THEORY :HERE)))
   (LOCAL (IN-THEORY (THEORY 'MINIMAL-THEORY)))
   (DEFUN-NX $$$PRESUB (S1)
     (DECLARE (XARGS :NORMALIZE NIL))
     (OR (INIT_PDPT-PRE S1)
         (INIT_PDTS-PRE S1)
         (SEC_NOT_PRESENT-PRE S1)))
   (DEFUN-NX $$$MODIFYSUB (S1)
     (DECLARE (XARGS :NORMALIZE NIL))
     (COND ((INIT_PDPT-PRE S1)
            (INIT_PDPT-MODIFY S1))
           ((INIT_PDTS-PRE S1)
            (INIT_PDTS-MODIFY S1))
           ((SEC_NOT_PRESENT-PRE S1)
            (SEC_NOT_PRESENT-MODIFY S1))
           (T S1)))
   (DEFTHM
     $$$PRESUB-IMPLIES-INSUB
     (IMPLIES ($$$PRESUB S1) (IN-SUB S1))
     :HINTS
     (("Goal" :IN-THEORY (UNION-THEORIES (THEORY 'SUBTHEORY)
                                         (LIST '$$$PRESUB '$$$MODIFYSUB))))
     :RULE-CLASSES NIL)
   (DEFTHM
     $$$NO-MAIN-CUTPOINT-IN-SUB
     (IMPLIES (IN-SUB S1)
              (NOT (CREATE_NESTED_PT-CUTPOINT-P S1)))
     :HINTS
     (("Goal" :IN-THEORY (UNION-THEORIES (THEORY 'SUBTHEORY)
                                         (LIST '$$$PRESUB '$$$MODIFYSUB))))
     :RULE-CLASSES NIL)
   (DEFTHM
     $$$IN-SUB-IMPLIES-IN-MAIN
     (IMPLIES (IN-SUB S1)
              (IN-CREATE_NESTED_PT S1))
     :HINTS
     (("Goal" :IN-THEORY (UNION-THEORIES (THEORY 'SUBTHEORY)
                                         (LIST '$$$PRESUB '$$$MODIFYSUB))))
     :RULE-CLASSES NIL)
   (DEFTHM $$$CORRECTNESS-OF-SUB
     (IMPLIES (AND ($$$PRESUB S1)
                   (EXISTS-NEXT-EXITPOINT S1))
              (AND (LET* ((S1 (NEXT-EXITPOINT S1)))
                         (NOT (IN-SUB S1)))
                   (EQUAL (NEXT-EXITPOINT S1)
                          ($$$MODIFYSUB S1))))
     :HINTS (("Goal" :IN-THEORY (ENABLE $$$PRESUB $$$MODIFYSUB)
              :USE ((:INSTANCE INIT_PDPT-CORRECT)
                    (:INSTANCE INIT_PDTS-CORRECT)
                    (:INSTANCE SEC_NOT_PRESENT-CORRECT))))
     :RULE-CLASSES NIL)
   (LOCAL (IN-THEORY (THEORY 'GROUND-ZERO)))
   (DEFP $$$NEXT-CUTPOINT-MAIN (S1)
     (IF (OR (CREATE_NESTED_PT-CUTPOINT-P S1)
             (NOT (IN-CREATE_NESTED_PT S1)))
         S1
         (LET* ((S1 (IF ($$$PRESUB S1)
                        ($$$MODIFYSUB S1)
                        (Y86-STEP S1))))
               ($$$NEXT-CUTPOINT-MAIN S1)))

;;; This rule-claases nil interfered with my computed
;;; expand hint.  Why does it not appear in corresponding
;;; definitions above?

     ;;:RULE-CLASSES NIL
     )
   (DEFTHM
     $$$DEFP-SYMSIM-THEOREM
     (EQUAL ($$$NEXT-CUTPOINT-MAIN S1)
            (IF (OR (CREATE_NESTED_PT-CUTPOINT-P S1)
                    (NOT (IN-CREATE_NESTED_PT S1)))
                S1
                (COND ((INIT_PDPT-PRE S1)
                       ($$$NEXT-CUTPOINT-MAIN (INIT_PDPT-MODIFY S1)))
                      ((INIT_PDTS-PRE S1)
                       ($$$NEXT-CUTPOINT-MAIN (INIT_PDTS-MODIFY S1)))
                      ((SEC_NOT_PRESENT-PRE S1)
                       ($$$NEXT-CUTPOINT-MAIN (SEC_NOT_PRESENT-MODIFY S1)))
                      (T (LET* ((S1 (Y86-STEP S1)))
                               ($$$NEXT-CUTPOINT-MAIN S1))))))
     :HINTS (("Goal" :USE ((:INSTANCE $$$NEXT-CUTPOINT-MAIN$DEF))
              :IN-THEORY (ENABLE $$$PRESUB $$$MODIFYSUB))))))
 (LOCAL (DEFTHM $$$PRE-IMPLIES-ASSERTION
          (IMPLIES (CREATE_NESTED_PT-PRE S1)
                   (LET ((S0 S1))
                        (CREATE_NESTED_PT-ASSERTION S0 S1)))
          :RULE-CLASSES NIL))
 (LOCAL (DEFTHM $$$ASSERTION-MAIN-IMPLIES-POST
          (IMPLIES (AND (CREATE_NESTED_PT-ASSERTION S0 S1)
                        (NOT (IN-CREATE_NESTED_PT S1)))
                   (EQUAL S1
                          (LET ((S1 S0))
                               (CREATE_NESTED_PT-MODIFY S1))))
          :RULE-CLASSES NIL))
 (LOCAL (DEFTHM $$$ASSERTION-IMPLIES-CUTPOINT
          (IMPLIES (CREATE_NESTED_PT-ASSERTION S0 S1)
                   (OR (CREATE_NESTED_PT-CUTPOINT-P S1)
                       (NOT (IN-CREATE_NESTED_PT S1))))
          :RULE-CLASSES NIL))
 (LOCAL (IN-THEORY (THEORY 'GROUND-ZERO)))
 (LOCAL (DEFUN-SK $$$EXISTS-NEXT-CUTPOINT (S1)
          (EXISTS N
                  (LET* ((S1 (Y86 S1 N)))
                        (CREATE_NESTED_PT-CUTPOINT-P S1)))))
 (LOCAL (IN-THEORY (UNION-THEORIES (THEORY 'USER-THEORY)
                                   (LIST '$$$DEFP-SYMSIM-THEOREM))))





 (local
  (in-theory (disable $$$DEFP-SYMSIM-THEOREM)))

 (local
  (in-theory (enable n32+ n32)))

 (local
  (in-theory (disable cf zf sf of
                      subl-cf
                      sall-cf sall-of
                      shrl-cf shrl-of
                      unpack)))

;;; Maybe try this by hand

 (local
  (set-default-hints nil))


 (local
  (in-theory (disable ash-to-floor)))


 (local
  (defthm |(init_pdpt-pre s)|
    (implies (create_nested_pt-pre s1)
             (INIT_PDPT-PRE
              (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                           :EBP (+ -4 (G :ESP S1))
                           :EIP (+ 687 (SNPT-CODE-LOCATION))
                           :ESP (+ -24 (G :ESP S1))
                           :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                           :F-OF
                           (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                               (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                           :F-SF
                           (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                           :F-ZF (ZF (+ -20 (G :ESP S1)))
                           :IMME1 16
                           (UPDATE-MEM (+ -4 (G :ESP S1))
                                       (G :EBP S1)
                                       (+ -16 (G :ESP S1))
                                       (R32 (+ 8 (G :ESP S1)) S1)
                                       (+ -20 (G :ESP S1))
                                       (R32 (+ 4 (G :ESP S1)) S1)
                                       (+ -24 (G :ESP S1))
                                       (+ 927 (SNPT-CODE-LOCATION))
                                       S1))))))



 (local
  (defthm |(init_pdts-pre s)|
    (implies (create_nested_pt-pre s1)
             (INIT_PDTS-PRE
              (UPDATE-REGS
               :EAX (R32 (+ 8 (G :ESP S1)) S1)
               :EIP (+ 334 (SNPT-CODE-LOCATION))
               :ESP (+ -24 (G :ESP S1))
               (UPDATE-MEM
                (+ -20 (G :ESP S1))
                (R32 (+ 8 (G :ESP S1)) S1)
                (+ -24 (G :ESP S1))
                (+ 944 (SNPT-CODE-LOCATION))
                (INIT_PDPT-MODIFY
                 (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                              :EBP (+ -4 (G :ESP S1))
                              :EIP (+ 687 (SNPT-CODE-LOCATION))
                              :ESP (+ -24 (G :ESP S1))
                              :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                              :F-OF
                              (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                  (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                              :F-SF
                              (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                              :F-ZF (ZF (+ -20 (G :ESP S1)))
                              :IMME1 16
                              (UPDATE-MEM (+ -4 (G :ESP S1))
                                          (G :EBP S1)
                                          (+ -16 (G :ESP S1))
                                          (R32 (+ 8 (G :ESP S1)) S1)
                                          (+ -20 (G :ESP S1))
                                          (R32 (+ 4 (G :ESP S1)) S1)
                                          (+ -24 (G :ESP S1))
                                          (+ 927 (SNPT-CODE-LOCATION))
                                          S1)))))))
    :hints (("Goal" :in-theory (disable |(logior 1 x)|)))))

;;; !!! why so slow?
 (local
  (defthm |(create_nested_pt-pre s)|
    (implies (create_nested_pt-pre s1)
             (SEC_NOT_PRESENT-PRE
              (UPDATE-REGS
               :EAX (R32 (+ 4 (G :ESP S1)) S1)
               :EIP (SNPT-CODE-LOCATION)
               :ESP (+ -24 (G :ESP S1))
               (UPDATE-MEM
                (+ -12 (G :ESP S1))
                (R32 (+ 16 (G :ESP S1)) S1)
                (+ -16 (G :ESP S1))
                (R32 (+ 12 (G :ESP S1)) S1)
                (+ -20 (G :ESP S1))
                (R32 (+ 4 (G :ESP S1)) S1)
                (+ -24 (G :ESP S1))
                (+ 985 (SNPT-CODE-LOCATION))
                (INIT_PDTS-MODIFY
                 (UPDATE-REGS
                  :EAX (R32 (+ 8 (G :ESP S1)) S1)
                  :EIP (+ 334 (SNPT-CODE-LOCATION))
                  :ESP (+ -24 (G :ESP S1))
                  (UPDATE-MEM
                   (+ -20 (G :ESP S1))
                   (R32 (+ 8 (G :ESP S1)) S1)
                   (+ -24 (G :ESP S1))
                   (+ 944 (SNPT-CODE-LOCATION))
                   (INIT_PDPT-MODIFY
                    (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                 :EBP (+ -4 (G :ESP S1))
                                 :EIP (+ 687 (SNPT-CODE-LOCATION))
                                 :ESP (+ -24 (G :ESP S1))
                                 :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                 :F-OF
                                 (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                     (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                 :F-SF
                                 (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                 :F-ZF (ZF (+ -20 (G :ESP S1)))
                                 :IMME1 16
                                 (UPDATE-MEM (+ -4 (G :ESP S1))
                                             (G :EBP S1)
                                             (+ -16 (G :ESP S1))
                                             (R32 (+ 8 (G :ESP S1)) S1)
                                             (+ -20 (G :ESP S1))
                                             (R32 (+ 4 (G :ESP S1)) S1)
                                             (+ -24 (G :ESP S1))
                                             (+ 927 (SNPT-CODE-LOCATION))
                                             S1))))))))))
    :hints (("Goal" :do-not '(generalize eliminate-destructors fertilize)
             :in-theory (disable |(logior 1 x)|
                                 init_pdpt-pre
                                 init_pdts-pre)
             :cases ((equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 0)
                     (equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 1)
                     (equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 2)
                     (equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 3)))
            ("Subgoal 4"
             :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                              (i 0)
                              (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                              :EBP (+ -4 (G :ESP S1))
                                              :EIP (+ 687 (SNPT-CODE-LOCATION))
                                              :ESP (+ -24 (G :ESP S1))
                                              :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                              :F-OF
                                              (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                  (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                              :F-SF
                                              (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                              :F-ZF (ZF (+ -20 (G :ESP S1)))
                                              :IMME1 16
                                              (UPDATE-MEM (+ -4 (G :ESP S1))
                                                          (G :EBP S1)
                                                          (+ -16 (G :ESP S1))
                                                          (R32 (+ 8 (G :ESP S1)) S1)
                                                          (+ -20 (G :ESP S1))
                                                          (R32 (+ 4 (G :ESP S1)) S1)
                                                          (+ -24 (G :ESP S1))
                                                          (+ 927 (SNPT-CODE-LOCATION))
                                                          S1))))))
            ("Subgoal 3"
             :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                              (i 1)
                              (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                              :EBP (+ -4 (G :ESP S1))
                                              :EIP (+ 687 (SNPT-CODE-LOCATION))
                                              :ESP (+ -24 (G :ESP S1))
                                              :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                              :F-OF
                                              (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                  (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                              :F-SF
                                              (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                              :F-ZF (ZF (+ -20 (G :ESP S1)))
                                              :IMME1 16
                                              (UPDATE-MEM (+ -4 (G :ESP S1))
                                                          (G :EBP S1)
                                                          (+ -16 (G :ESP S1))
                                                          (R32 (+ 8 (G :ESP S1)) S1)
                                                          (+ -20 (G :ESP S1))
                                                          (R32 (+ 4 (G :ESP S1)) S1)
                                                          (+ -24 (G :ESP S1))
                                                          (+ 927 (SNPT-CODE-LOCATION))
                                                          S1))))))
            ("Subgoal 2"
             :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                              (i 2)
                              (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                              :EBP (+ -4 (G :ESP S1))
                                              :EIP (+ 687 (SNPT-CODE-LOCATION))
                                              :ESP (+ -24 (G :ESP S1))
                                              :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                              :F-OF
                                              (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                  (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                              :F-SF
                                              (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                              :F-ZF (ZF (+ -20 (G :ESP S1)))
                                              :IMME1 16
                                              (UPDATE-MEM (+ -4 (G :ESP S1))
                                                          (G :EBP S1)
                                                          (+ -16 (G :ESP S1))
                                                          (R32 (+ 8 (G :ESP S1)) S1)
                                                          (+ -20 (G :ESP S1))
                                                          (R32 (+ 4 (G :ESP S1)) S1)
                                                          (+ -24 (G :ESP S1))
                                                          (+ 927 (SNPT-CODE-LOCATION))
                                                          S1))))))
            ("Subgoal 1"
             :use ((:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                              (i 3)
                              (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                              :EBP (+ -4 (G :ESP S1))
                                              :EIP (+ 687 (SNPT-CODE-LOCATION))
                                              :ESP (+ -24 (G :ESP S1))
                                              :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                              :F-OF
                                              (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                  (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                              :F-SF
                                              (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                              :F-ZF (ZF (+ -20 (G :ESP S1)))
                                              :IMME1 16
                                              (UPDATE-MEM (+ -4 (G :ESP S1))
                                                          (G :EBP S1)
                                                          (+ -16 (G :ESP S1))
                                                          (R32 (+ 8 (G :ESP S1)) S1)
                                                          (+ -20 (G :ESP S1))
                                                          (R32 (+ 4 (G :ESP S1)) S1)
                                                          (+ -24 (G :ESP S1))
                                                          (+ 927 (SNPT-CODE-LOCATION))
                                                          S1)))))))
    :otf-flg t))

 (local
  (defthm init_pdpt-pre-false
    (implies (not (equal (g :eip s) (+ *INIT_PDPT* (snpt-code-location))))
             (not (init_pdpt-pre s)))))

 (local
  (defthm init_pdts-pre-false
    (implies (not (equal (g :eip s) (+ *INIT_PDTS* (snpt-code-location))))
             (not (init_pdts-pre s)))))

 (local
  (defthm sec_not_present-pre-false
    (implies (not (equal (g :eip s) (+ *SEC_NOT_PRESENT* (snpt-code-location))))
             (not (sec_not_present-pre s)))))



 (local
  (in-theory (disable init_pdpt-pre
                      init_pdts-pre
                      sec_not_present-pre)))



 (local
 (defthm why-0
   (implies (good-state-p s)
            (CREATE_NESTED_PT-LOADED-P s))))


 (local
  (defthm simulate-main
    (implies (and (equal (g :eip s1)
                         (+ *CREATE_NESTED_PT* (snpt-code-location)))
                  ;; start
                  (create_nested_pt-pre s1)
                  (in-create_nested_pt s1)

                  (N32P (+ 31 (R32 (+ 8 (G :ESP S1)) S1)))
                  (< (ASH (LOGAND 1071644672 (R32 (+ 12 (G :ESP S1)) S1))
                          -21)
                     (ASH (LOGAND 1071644672
                                  (+ (R32 (+ 12 (G :ESP S1)) S1)
                                     (R32 (+ 16 (G :ESP S1)) S1)))
                          -21))
                  (< (+ 993 (snpt-code-location))
                     (R32 (G :ESP S1) S1))

                  )
             (equal ($$$NEXT-CUTPOINT-MAIN (Y86-STEP S1))
                    (UPDATE-REGS
                     :EAX (R32 (+ 4 (G :ESP S1)) S1)
                     :EBP (G :EBP S1)
                     :EIP (R32 (G :ESP S1) S1)
                     :ESP (+ 4 (G :ESP S1))
                     (SEC_NOT_PRESENT-MODIFY
                      (UPDATE-REGS
                       :EAX (R32 (+ 4 (G :ESP S1)) S1)
                       :EIP (SNPT-CODE-LOCATION)
                       :ESP (+ -24 (G :ESP S1))
                       (UPDATE-MEM
                        (+ -12 (G :ESP S1))
                        (R32 (+ 16 (G :ESP S1)) S1)
                        (+ -16 (G :ESP S1))
                        (R32 (+ 12 (G :ESP S1)) S1)
                        (+ -20 (G :ESP S1))
                        (R32 (+ 4 (G :ESP S1)) S1)
                        (+ -24 (G :ESP S1))
                        (+ 985 (SNPT-CODE-LOCATION))
                        (INIT_PDTS-MODIFY
                         (UPDATE-REGS
                          :EAX (R32 (+ 8 (G :ESP S1)) S1)
                          :EIP (+ 334 (SNPT-CODE-LOCATION))
                          :ESP (+ -24 (G :ESP S1))
                          (UPDATE-MEM
                           (+ -20 (G :ESP S1))
                           (R32 (+ 8 (G :ESP S1)) S1)
                           (+ -24 (G :ESP S1))
                           (+ 944 (SNPT-CODE-LOCATION))
                           (INIT_PDPT-MODIFY
                            (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                         :EBP (+ -4 (G :ESP S1))
                                         :EIP (+ 687 (SNPT-CODE-LOCATION))
                                         :ESP (+ -24 (G :ESP S1))
                                         :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                         :F-OF
                                         (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                             (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                         :F-SF
                                         (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                         :F-ZF (ZF (+ -20 (G :ESP S1)))
                                         :IMME1 16
                                         (UPDATE-MEM (+ -4 (G :ESP S1))
                                                     (G :EBP S1)
                                                     (+ -16 (G :ESP S1))
                                                     (R32 (+ 8 (G :ESP S1)) S1)
                                                     (+ -20 (G :ESP S1))
                                                     (R32 (+ 4 (G :ESP S1)) S1)
                                                     (+ -24 (G :ESP S1))
                                                     (+ 927 (SNPT-CODE-LOCATION))
                                                     S1))))))))))))
    :hints (("Goal" :in-theory (disable MOD-BOUNDS-1
                                        N32+-WHEN-WORD-ALIGNED
                                        |(word-aligned-p x)|
                                        INIT_PDPT-LOADED-THM-32
                                        INIT_PDTS-LOADED-THM-32
                                        SEC_NOT_PRESENT-LOADED-THM-32
                                        |(mod (+ x y) z) where (<= 0 z)|
                                        CANCEL-MOD-+

                                        |(logior 1 x)|
                                        )
             :do-not '(generalize eliminate-destructors fertilize))
            ("Goal''" :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                       (s1 (UPDATE-REGS :EIP (+ 888 (SNPT-CODE-LOCATION))
                                                        :ESP (+ -4 (G :ESP S1))
                                                        (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                    (G :EBP S1)
                                                                    S1))))))
            ("Goal'5'" :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                        (s1 (UPDATE-REGS :EBP (+ -4 (G :ESP S1))
                                                         :EIP (+ 890 (SNPT-CODE-LOCATION))
                                                         :ESP (+ -4 (G :ESP S1))
                                                         (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                     (G :EBP S1)
                                                                     S1))))))
            ("Goal'8'" :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                        (s1 (UPDATE-REGS :EBP (+ -4 (G :ESP S1))
                                                         :EIP (+ 896 (SNPT-CODE-LOCATION))
                                                         :ESP (+ -4 (G :ESP S1))
                                                         :IMME1
                                                         16
                                                         (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                     (G :EBP S1)
                                                                     S1))))))
            ("Goal'11'" :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                         (s1 (UPDATE-REGS :EBP (+ -4 (G :ESP S1))
                                                          :EIP (+ 898 (SNPT-CODE-LOCATION))
                                                          :ESP (+ -20 (G :ESP S1))
                                                          :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                          :F-OF
                                                          (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                              (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                          :F-SF
                                                          (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                          :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                          :IMME1 16
                                                          (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                      (G :EBP S1)
                                                                      S1))))))
            ("Goal'14'" :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                         (s1 (UPDATE-REGS :EAX (R32 (+ 8 (G :ESP S1)) S1)
                                                          :EBP (+ -4 (G :ESP S1))
                                                          :EIP (+ 904 (SNPT-CODE-LOCATION))
                                                          :ESP (+ -20 (G :ESP S1))
                                                          :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                          :F-OF
                                                          (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                              (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                          :F-SF
                                                          (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                          :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                          :IMME1 16
                                                          (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                      (G :EBP S1)
                                                                      S1))))))
            ("Goal'17'" :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                         (s1 (UPDATE-REGS :EAX (R32 (+ 8 (G :ESP S1)) S1)
                                                          :EBP (+ -4 (G :ESP S1))
                                                          :EIP (+ 910 (SNPT-CODE-LOCATION))
                                                          :ESP (+ -20 (G :ESP S1))
                                                          :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                          :F-OF
                                                          (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                              (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                          :F-SF
                                                          (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                          :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                          :IMME1 16
                                                          (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                      (G :EBP S1)
                                                                      (+ -16 (G :ESP S1))
                                                                      (R32 (+ 8 (G :ESP S1)) S1)
                                                                      S1))))))
            ("Goal'20'" :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                         (s1 (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                          :EBP (+ -4 (G :ESP S1))
                                                          :EIP (+ 916 (SNPT-CODE-LOCATION))
                                                          :ESP (+ -20 (G :ESP S1))
                                                          :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                          :F-OF
                                                          (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                              (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                          :F-SF
                                                          (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                          :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                          :IMME1 16
                                                          (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                      (G :EBP S1)
                                                                      (+ -16 (G :ESP S1))
                                                                      (R32 (+ 8 (G :ESP S1)) S1)
                                                                      S1))))))
            ("Goal'23'" :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                         (s1 (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                          :EBP (+ -4 (G :ESP S1))
                                                          :EIP (+ 922 (SNPT-CODE-LOCATION))
                                                          :ESP (+ -20 (G :ESP S1))
                                                          :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                          :F-OF
                                                          (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                              (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                          :F-SF
                                                          (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                          :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                          :IMME1 16
                                                          (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                      (G :EBP S1)
                                                                      (+ -16 (G :ESP S1))
                                                                      (R32 (+ 8 (G :ESP S1)) S1)
                                                                      (+ -20 (G :ESP S1))
                                                                      (R32 (+ 4 (G :ESP S1)) S1)
                                                                      S1))))))
            ("Goal'26'" :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                         (s1 (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                          :EBP (+ -4 (G :ESP S1))
                                                          :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                          :ESP (+ -24 (G :ESP S1))
                                                          :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                          :F-OF
                                                          (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                              (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                          :F-SF
                                                          (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                          :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                          :IMME1 16
                                                          (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                      (G :EBP S1)
                                                                      (+ -16 (G :ESP S1))
                                                                      (R32 (+ 8 (G :ESP S1)) S1)
                                                                      (+ -20 (G :ESP S1))
                                                                      (R32 (+ 4 (G :ESP S1)) S1)
                                                                      (+ -24 (G :ESP S1))
                                                                      (+ 927 (SNPT-CODE-LOCATION))
                                                                      S1))))))
            ("Goal'29'" :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                         (s1 (INIT_PDPT-MODIFY
                                              (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                           :EBP (+ -4 (G :ESP S1))
                                                           :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                           :ESP (+ -24 (G :ESP S1))
                                                           :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                           :F-OF
                                                           (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                               (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                           :F-SF
                                                           (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                           :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                           :IMME1 16
                                                           (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                       (G :EBP S1)
                                                                       (+ -16 (G :ESP S1))
                                                                       (R32 (+ 8 (G :ESP S1)) S1)
                                                                       (+ -20 (G :ESP S1))
                                                                       (R32 (+ 4 (G :ESP S1)) S1)
                                                                       (+ -24 (G :ESP S1))
                                                                       (+ 927 (SNPT-CODE-LOCATION))
                                                                       S1)))))))
            ("Goal'32'"  :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                          (s1 (UPDATE-REGS
                                               :EAX (R32 (+ 8 (G :ESP S1)) S1)
                                               :EIP (+ 933 (SNPT-CODE-LOCATION))
                                               (INIT_PDPT-MODIFY
                                                (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                             :EBP (+ -4 (G :ESP S1))
                                                             :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                             :ESP (+ -24 (G :ESP S1))
                                                             :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                             :F-OF
                                                             (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                                 (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                             :F-SF
                                                             (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                             :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                             :IMME1 16
                                                             (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                         (G :EBP S1)
                                                                         (+ -16 (G :ESP S1))
                                                                         (R32 (+ 8 (G :ESP S1)) S1)
                                                                         (+ -20 (G :ESP S1))
                                                                         (R32 (+ 4 (G :ESP S1)) S1)
                                                                         (+ -24 (G :ESP S1))
                                                                         (+ 927 (SNPT-CODE-LOCATION))
                                                                         S1))))))))
            ("Goal'35'"  :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                          (s1 (UPDATE-REGS
                                               :EAX (R32 (+ 8 (G :ESP S1)) S1)
                                               :EIP (+ 939 (SNPT-CODE-LOCATION))
                                               (UPDATE-MEM
                                                (+ -20 (G :ESP S1))
                                                (R32 (+ 8 (G :ESP S1)) S1)
                                                (INIT_PDPT-MODIFY
                                                 (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                              :EBP (+ -4 (G :ESP S1))
                                                              :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                              :ESP (+ -24 (G :ESP S1))
                                                              :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                              :F-OF
                                                              (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                                  (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                              :F-SF
                                                              (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                              :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                              :IMME1 16
                                                              (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                          (G :EBP S1)
                                                                          (+ -16 (G :ESP S1))
                                                                          (R32 (+ 8 (G :ESP S1)) S1)
                                                                          (+ -20 (G :ESP S1))
                                                                          (R32 (+ 4 (G :ESP S1)) S1)
                                                                          (+ -24 (G :ESP S1))
                                                                          (+ 927 (SNPT-CODE-LOCATION))
                                                                          S1)))))))))
            ("Goal'38'"  :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                          (s1 (UPDATE-REGS
                                               :EAX (R32 (+ 8 (G :ESP S1)) S1)
                                               :EIP (+ 334 (SNPT-CODE-LOCATION))
                                               :ESP (+ -24 (G :ESP S1))
                                               (UPDATE-MEM
                                                (+ -20 (G :ESP S1))
                                                (R32 (+ 8 (G :ESP S1)) S1)
                                                (+ -24 (G :ESP S1))
                                                (+ 944 (SNPT-CODE-LOCATION))
                                                (INIT_PDPT-MODIFY
                                                 (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                              :EBP (+ -4 (G :ESP S1))
                                                              :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                              :ESP (+ -24 (G :ESP S1))
                                                              :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                              :F-OF
                                                              (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                                  (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                              :F-SF
                                                              (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                              :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                              :IMME1 16
                                                              (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                          (G :EBP S1)
                                                                          (+ -16 (G :ESP S1))
                                                                          (R32 (+ 8 (G :ESP S1)) S1)
                                                                          (+ -20 (G :ESP S1))
                                                                          (R32 (+ 4 (G :ESP S1)) S1)
                                                                          (+ -24 (G :ESP S1))
                                                                          (+ 927 (SNPT-CODE-LOCATION))
                                                                          S1)))))))))
            ("Goal'41'"  :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                          (s1 (INIT_PDTS-MODIFY
                                               (UPDATE-REGS
                                                :EAX (R32 (+ 8 (G :ESP S1)) S1)
                                                :EIP (+ 334 (SNPT-CODE-LOCATION))
                                                :ESP (+ -24 (G :ESP S1))
                                                (UPDATE-MEM
                                                 (+ -20 (G :ESP S1))
                                                 (R32 (+ 8 (G :ESP S1)) S1)
                                                 (+ -24 (G :ESP S1))
                                                 (+ 944 (SNPT-CODE-LOCATION))
                                                 (INIT_PDPT-MODIFY
                                                  (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                               :EBP (+ -4 (G :ESP S1))
                                                               :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                               :ESP (+ -24 (G :ESP S1))
                                                               :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                               :F-OF
                                                               (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                                   (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                               :F-SF
                                                               (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                               :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                               :IMME1 16
                                                               (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                           (G :EBP S1)
                                                                           (+ -16 (G :ESP S1))
                                                                           (R32 (+ 8 (G :ESP S1)) S1)
                                                                           (+ -20 (G :ESP S1))
                                                                           (R32 (+ 4 (G :ESP S1)) S1)
                                                                           (+ -24 (G :ESP S1))
                                                                           (+ 927 (SNPT-CODE-LOCATION))
                                                                           S1))))))))))
            ("Goal'44'"  :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                          (s1 (UPDATE-REGS
                                               :EAX (R32 (+ 16 (G :ESP S1)) S1)
                                               :EIP (+ 950 (SNPT-CODE-LOCATION))
                                               (INIT_PDTS-MODIFY
                                                (UPDATE-REGS
                                                 :EAX (R32 (+ 8 (G :ESP S1)) S1)
                                                 :EIP (+ 334 (SNPT-CODE-LOCATION))
                                                 :ESP (+ -24 (G :ESP S1))
                                                 (UPDATE-MEM
                                                  (+ -20 (G :ESP S1))
                                                  (R32 (+ 8 (G :ESP S1)) S1)
                                                  (+ -24 (G :ESP S1))
                                                  (+ 944 (SNPT-CODE-LOCATION))
                                                  (INIT_PDPT-MODIFY
                                                   (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                                :EBP (+ -4 (G :ESP S1))
                                                                :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                                :ESP (+ -24 (G :ESP S1))
                                                                :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                                :F-OF
                                                                (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                                    (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                                :F-SF
                                                                (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                                :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                                :IMME1 16
                                                                (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                            (G :EBP S1)
                                                                            (+ -16 (G :ESP S1))
                                                                            (R32 (+ 8 (G :ESP S1)) S1)
                                                                            (+ -20 (G :ESP S1))
                                                                            (R32 (+ 4 (G :ESP S1)) S1)
                                                                            (+ -24 (G :ESP S1))
                                                                            (+ 927 (SNPT-CODE-LOCATION))
                                                                            S1)))))))))))
            ("Goal'47'"  :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                          (s1 (UPDATE-REGS
                                               :EAX (R32 (+ 16 (G :ESP S1)) S1)
                                               :EIP (+ 956 (SNPT-CODE-LOCATION))
                                               (UPDATE-MEM
                                                (+ -12 (G :ESP S1))
                                                (R32 (+ 16 (G :ESP S1)) S1)
                                                (INIT_PDTS-MODIFY
                                                 (UPDATE-REGS
                                                  :EAX (R32 (+ 8 (G :ESP S1)) S1)
                                                  :EIP (+ 334 (SNPT-CODE-LOCATION))
                                                  :ESP (+ -24 (G :ESP S1))
                                                  (UPDATE-MEM
                                                   (+ -20 (G :ESP S1))
                                                   (R32 (+ 8 (G :ESP S1)) S1)
                                                   (+ -24 (G :ESP S1))
                                                   (+ 944 (SNPT-CODE-LOCATION))
                                                   (INIT_PDPT-MODIFY
                                                    (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                                 :EBP (+ -4 (G :ESP S1))
                                                                 :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                                 :ESP (+ -24 (G :ESP S1))
                                                                 :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                                 :F-OF
                                                                 (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                                     (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                                 :F-SF
                                                                 (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                                 :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                                 :IMME1 16
                                                                 (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                             (G :EBP S1)
                                                                             (+ -16 (G :ESP S1))
                                                                             (R32 (+ 8 (G :ESP S1)) S1)
                                                                             (+ -20 (G :ESP S1))
                                                                             (R32 (+ 4 (G :ESP S1)) S1)
                                                                             (+ -24 (G :ESP S1))
                                                                             (+ 927 (SNPT-CODE-LOCATION))
                                                                             S1))))))))))))
            ("Goal'50'"  :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                          (s1 (UPDATE-REGS
                                               :EAX (R32 (+ 12 (G :ESP S1)) S1)
                                               :EIP (+ 962 (SNPT-CODE-LOCATION))
                                               (UPDATE-MEM
                                                (+ -12 (G :ESP S1))
                                                (R32 (+ 16 (G :ESP S1)) S1)
                                                (INIT_PDTS-MODIFY
                                                 (UPDATE-REGS
                                                  :EAX (R32 (+ 8 (G :ESP S1)) S1)
                                                  :EIP (+ 334 (SNPT-CODE-LOCATION))
                                                  :ESP (+ -24 (G :ESP S1))
                                                  (UPDATE-MEM
                                                   (+ -20 (G :ESP S1))
                                                   (R32 (+ 8 (G :ESP S1)) S1)
                                                   (+ -24 (G :ESP S1))
                                                   (+ 944 (SNPT-CODE-LOCATION))
                                                   (INIT_PDPT-MODIFY
                                                    (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                                 :EBP (+ -4 (G :ESP S1))
                                                                 :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                                 :ESP (+ -24 (G :ESP S1))
                                                                 :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                                 :F-OF
                                                                 (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                                     (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                                 :F-SF
                                                                 (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                                 :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                                 :IMME1 16
                                                                 (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                             (G :EBP S1)
                                                                             (+ -16 (G :ESP S1))
                                                                             (R32 (+ 8 (G :ESP S1)) S1)
                                                                             (+ -20 (G :ESP S1))
                                                                             (R32 (+ 4 (G :ESP S1)) S1)
                                                                             (+ -24 (G :ESP S1))
                                                                             (+ 927 (SNPT-CODE-LOCATION))
                                                                             S1))))))))))))
            ("Goal'53'"  :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                          (s1 (UPDATE-REGS
                                               :EAX (R32 (+ 12 (G :ESP S1)) S1)
                                               :EIP (+ 968 (SNPT-CODE-LOCATION))
                                               (UPDATE-MEM
                                                (+ -12 (G :ESP S1))
                                                (R32 (+ 16 (G :ESP S1)) S1)
                                                (+ -16 (G :ESP S1))
                                                (R32 (+ 12 (G :ESP S1)) S1)
                                                (INIT_PDTS-MODIFY
                                                 (UPDATE-REGS
                                                  :EAX (R32 (+ 8 (G :ESP S1)) S1)
                                                  :EIP (+ 334 (SNPT-CODE-LOCATION))
                                                  :ESP (+ -24 (G :ESP S1))
                                                  (UPDATE-MEM
                                                   (+ -20 (G :ESP S1))
                                                   (R32 (+ 8 (G :ESP S1)) S1)
                                                   (+ -24 (G :ESP S1))
                                                   (+ 944 (SNPT-CODE-LOCATION))
                                                   (INIT_PDPT-MODIFY
                                                    (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                                 :EBP (+ -4 (G :ESP S1))
                                                                 :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                                 :ESP (+ -24 (G :ESP S1))
                                                                 :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                                 :F-OF
                                                                 (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                                     (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                                 :F-SF
                                                                 (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                                 :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                                 :IMME1 16
                                                                 (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                             (G :EBP S1)
                                                                             (+ -16 (G :ESP S1))
                                                                             (R32 (+ 8 (G :ESP S1)) S1)
                                                                             (+ -20 (G :ESP S1))
                                                                             (R32 (+ 4 (G :ESP S1)) S1)
                                                                             (+ -24 (G :ESP S1))
                                                                             (+ 927 (SNPT-CODE-LOCATION))
                                                                             S1))))))))))))
            ("Goal'56'"  :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                          (s1 (UPDATE-REGS
                                               :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                               :EIP (+ 974 (SNPT-CODE-LOCATION))
                                               (UPDATE-MEM
                                                (+ -12 (G :ESP S1))
                                                (R32 (+ 16 (G :ESP S1)) S1)
                                                (+ -16 (G :ESP S1))
                                                (R32 (+ 12 (G :ESP S1)) S1)
                                                (INIT_PDTS-MODIFY
                                                 (UPDATE-REGS
                                                  :EAX (R32 (+ 8 (G :ESP S1)) S1)
                                                  :EIP (+ 334 (SNPT-CODE-LOCATION))
                                                  :ESP (+ -24 (G :ESP S1))
                                                  (UPDATE-MEM
                                                   (+ -20 (G :ESP S1))
                                                   (R32 (+ 8 (G :ESP S1)) S1)
                                                   (+ -24 (G :ESP S1))
                                                   (+ 944 (SNPT-CODE-LOCATION))
                                                   (INIT_PDPT-MODIFY
                                                    (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                                 :EBP (+ -4 (G :ESP S1))
                                                                 :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                                 :ESP (+ -24 (G :ESP S1))
                                                                 :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                                 :F-OF
                                                                 (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                                     (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                                 :F-SF
                                                                 (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                                 :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                                 :IMME1 16
                                                                 (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                             (G :EBP S1)
                                                                             (+ -16 (G :ESP S1))
                                                                             (R32 (+ 8 (G :ESP S1)) S1)
                                                                             (+ -20 (G :ESP S1))
                                                                             (R32 (+ 4 (G :ESP S1)) S1)
                                                                             (+ -24 (G :ESP S1))
                                                                             (+ 927 (SNPT-CODE-LOCATION))
                                                                             S1))))))))))))
            ("Goal'59'"  :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                          (s1 (UPDATE-REGS
                                               :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                               :EIP (+ 980 (SNPT-CODE-LOCATION))
                                               (UPDATE-MEM
                                                (+ -12 (G :ESP S1))
                                                (R32 (+ 16 (G :ESP S1)) S1)
                                                (+ -16 (G :ESP S1))
                                                (R32 (+ 12 (G :ESP S1)) S1)
                                                (+ -20 (G :ESP S1))
                                                (R32 (+ 4 (G :ESP S1)) S1)
                                                (INIT_PDTS-MODIFY
                                                 (UPDATE-REGS
                                                  :EAX (R32 (+ 8 (G :ESP S1)) S1)
                                                  :EIP (+ 334 (SNPT-CODE-LOCATION))
                                                  :ESP (+ -24 (G :ESP S1))
                                                  (UPDATE-MEM
                                                   (+ -20 (G :ESP S1))
                                                   (R32 (+ 8 (G :ESP S1)) S1)
                                                   (+ -24 (G :ESP S1))
                                                   (+ 944 (SNPT-CODE-LOCATION))
                                                   (INIT_PDPT-MODIFY
                                                    (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                                 :EBP (+ -4 (G :ESP S1))
                                                                 :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                                 :ESP (+ -24 (G :ESP S1))
                                                                 :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                                 :F-OF
                                                                 (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                                     (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                                 :F-SF
                                                                 (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                                 :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                                 :IMME1 16
                                                                 (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                             (G :EBP S1)
                                                                             (+ -16 (G :ESP S1))
                                                                             (R32 (+ 8 (G :ESP S1)) S1)
                                                                             (+ -20 (G :ESP S1))
                                                                             (R32 (+ 4 (G :ESP S1)) S1)
                                                                             (+ -24 (G :ESP S1))
                                                                             (+ 927 (SNPT-CODE-LOCATION))
                                                                             S1))))))))))))
            ("Goal'62'"  :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                          (s1 (UPDATE-REGS
                                               :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                               :EIP (SNPT-CODE-LOCATION)
                                               :ESP (+ -24 (G :ESP S1))
                                               (UPDATE-MEM
                                                (+ -12 (G :ESP S1))
                                                (R32 (+ 16 (G :ESP S1)) S1)
                                                (+ -16 (G :ESP S1))
                                                (R32 (+ 12 (G :ESP S1)) S1)
                                                (+ -20 (G :ESP S1))
                                                (R32 (+ 4 (G :ESP S1)) S1)
                                                (+ -24 (G :ESP S1))
                                                (+ 985 (SNPT-CODE-LOCATION))
                                                (INIT_PDTS-MODIFY
                                                 (UPDATE-REGS
                                                  :EAX (R32 (+ 8 (G :ESP S1)) S1)
                                                  :EIP (+ 334 (SNPT-CODE-LOCATION))
                                                  :ESP (+ -24 (G :ESP S1))
                                                  (UPDATE-MEM
                                                   (+ -20 (G :ESP S1))
                                                   (R32 (+ 8 (G :ESP S1)) S1)
                                                   (+ -24 (G :ESP S1))
                                                   (+ 944 (SNPT-CODE-LOCATION))
                                                   (INIT_PDPT-MODIFY
                                                    (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                                 :EBP (+ -4 (G :ESP S1))
                                                                 :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                                 :ESP (+ -24 (G :ESP S1))
                                                                 :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                                 :F-OF
                                                                 (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                                     (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                                 :F-SF
                                                                 (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                                 :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                                 :IMME1 16
                                                                 (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                             (G :EBP S1)
                                                                             (+ -16 (G :ESP S1))
                                                                             (R32 (+ 8 (G :ESP S1)) S1)
                                                                             (+ -20 (G :ESP S1))
                                                                             (R32 (+ 4 (G :ESP S1)) S1)
                                                                             (+ -24 (G :ESP S1))
                                                                             (+ 927 (SNPT-CODE-LOCATION))
                                                                             S1))))))))))))
            ("Goal'65'"  :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                          (s1 (SEC_NOT_PRESENT-MODIFY
                                               (UPDATE-REGS
                                                :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                :EIP (SNPT-CODE-LOCATION)
                                                :ESP (+ -24 (G :ESP S1))
                                                (UPDATE-MEM
                                                 (+ -12 (G :ESP S1))
                                                 (R32 (+ 16 (G :ESP S1)) S1)
                                                 (+ -16 (G :ESP S1))
                                                 (R32 (+ 12 (G :ESP S1)) S1)
                                                 (+ -20 (G :ESP S1))
                                                 (R32 (+ 4 (G :ESP S1)) S1)
                                                 (+ -24 (G :ESP S1))
                                                 (+ 985 (SNPT-CODE-LOCATION))
                                                 (INIT_PDTS-MODIFY
                                                  (UPDATE-REGS
                                                   :EAX (R32 (+ 8 (G :ESP S1)) S1)
                                                   :EIP (+ 334 (SNPT-CODE-LOCATION))
                                                   :ESP (+ -24 (G :ESP S1))
                                                   (UPDATE-MEM
                                                    (+ -20 (G :ESP S1))
                                                    (R32 (+ 8 (G :ESP S1)) S1)
                                                    (+ -24 (G :ESP S1))
                                                    (+ 944 (SNPT-CODE-LOCATION))
                                                    (INIT_PDPT-MODIFY
                                                     (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                                  :EBP (+ -4 (G :ESP S1))
                                                                  :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                                  :ESP (+ -24 (G :ESP S1))
                                                                  :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                                  :F-OF
                                                                  (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                                      (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                                  :F-SF
                                                                  (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                                  :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                                  :IMME1 16
                                                                  (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                              (G :EBP S1)
                                                                              (+ -16 (G :ESP S1))
                                                                              (R32 (+ 8 (G :ESP S1)) S1)
                                                                              (+ -20 (G :ESP S1))
                                                                              (R32 (+ 4 (G :ESP S1)) S1)
                                                                              (+ -24 (G :ESP S1))
                                                                              (+ 927 (SNPT-CODE-LOCATION))
                                                                              S1)))))))))))
                               ))

            ("Goal'68'" :use ((:instance |(r32 addr (sec_not_present-modify s))|
                                         (addr (+ 4 (g :esp s1)))
                                         (s (UPDATE-REGS
                                             :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                             :EIP (SNPT-CODE-LOCATION)
                                             :ESP (+ -24 (G :ESP S1))
                                             (UPDATE-MEM
                                              (+ -12 (G :ESP S1))
                                              (R32 (+ 16 (G :ESP S1)) S1)
                                              (+ -16 (G :ESP S1))
                                              (R32 (+ 12 (G :ESP S1)) S1)
                                              (+ -20 (G :ESP S1))
                                              (R32 (+ 4 (G :ESP S1)) S1)
                                              (+ -24 (G :ESP S1))
                                              (+ 985 (SNPT-CODE-LOCATION))
                                              (INIT_PDTS-MODIFY
                                               (UPDATE-REGS
                                                :EAX (R32 (+ 8 (G :ESP S1)) S1)
                                                :EIP (+ 334 (SNPT-CODE-LOCATION))
                                                :ESP (+ -24 (G :ESP S1))
                                                (UPDATE-MEM
                                                 (+ -20 (G :ESP S1))
                                                 (R32 (+ 8 (G :ESP S1)) S1)
                                                 (+ -24 (G :ESP S1))
                                                 (+ 944 (SNPT-CODE-LOCATION))
                                                 (INIT_PDPT-MODIFY
                                                  (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                               :EBP (+ -4 (G :ESP S1))
                                                               :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                               :ESP (+ -24 (G :ESP S1))
                                                               :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                               :F-OF
                                                               (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                                   (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                               :F-SF
                                                               (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                               :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                               :IMME1 16
                                                               (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                           (G :EBP S1)
                                                                           (+ -16 (G :ESP S1))
                                                                           (R32 (+ 8 (G :ESP S1)) S1)
                                                                           (+ -20 (G :ESP S1))
                                                                           (R32 (+ 4 (G :ESP S1)) S1)
                                                                           (+ -24 (G :ESP S1))
                                                                           (+ 927 (SNPT-CODE-LOCATION))
                                                                           S1))))))))))
                              (:instance |(r32 addr (sec_not_present-modify s))|
                                         (addr (+ -4 (g :esp s1)))
                                         (s (UPDATE-REGS
                                             :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                             :EIP (SNPT-CODE-LOCATION)
                                             :ESP (+ -24 (G :ESP S1))
                                             (UPDATE-MEM
                                              (+ -12 (G :ESP S1))
                                              (R32 (+ 16 (G :ESP S1)) S1)
                                              (+ -16 (G :ESP S1))
                                              (R32 (+ 12 (G :ESP S1)) S1)
                                              (+ -20 (G :ESP S1))
                                              (R32 (+ 4 (G :ESP S1)) S1)
                                              (+ -24 (G :ESP S1))
                                              (+ 985 (SNPT-CODE-LOCATION))
                                              (INIT_PDTS-MODIFY
                                               (UPDATE-REGS
                                                :EAX (R32 (+ 8 (G :ESP S1)) S1)
                                                :EIP (+ 334 (SNPT-CODE-LOCATION))
                                                :ESP (+ -24 (G :ESP S1))
                                                (UPDATE-MEM
                                                 (+ -20 (G :ESP S1))
                                                 (R32 (+ 8 (G :ESP S1)) S1)
                                                 (+ -24 (G :ESP S1))
                                                 (+ 944 (SNPT-CODE-LOCATION))
                                                 (INIT_PDPT-MODIFY
                                                  (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                               :EBP (+ -4 (G :ESP S1))
                                                               :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                               :ESP (+ -24 (G :ESP S1))
                                                               :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                               :F-OF
                                                               (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                                   (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                               :F-SF
                                                               (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                               :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                               :IMME1 16
                                                               (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                           (G :EBP S1)
                                                                           (+ -16 (G :ESP S1))
                                                                           (R32 (+ 8 (G :ESP S1)) S1)
                                                                           (+ -20 (G :ESP S1))
                                                                           (R32 (+ 4 (G :ESP S1)) S1)
                                                                           (+ -24 (G :ESP S1))
                                                                           (+ 927 (SNPT-CODE-LOCATION))
                                                                           S1))))))))))
                              (:instance |(r32 addr (init_pdpt-modify s)) --- written to 1|
                                         (i (ASH (R32 (+ 12 (G :ESP S1)) S1) -30))
                                         (s (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                         :EBP (+ -4 (G :ESP S1))
                                                         :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                         :ESP (+ -24 (G :ESP S1))
                                                         :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                         :F-OF
                                                         (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                             (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                         :F-SF
                                                         (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                         :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                         :IMME1 16
                                                         (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                     (G :EBP S1)
                                                                     (+ -16 (G :ESP S1))
                                                                     (R32 (+ 8 (G :ESP S1)) S1)
                                                                     (+ -20 (G :ESP S1))
                                                                     (R32 (+ 4 (G :ESP S1)) S1)
                                                                     (+ -24 (G :ESP S1))
                                                                     (+ 927 (SNPT-CODE-LOCATION))
                                                                     S1))))))


            ("Subgoal 11"  :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                            (s1 (UPDATE-REGS
                                                 :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                 :EIP (+ 991 (SNPT-CODE-LOCATION))
                                                 (SEC_NOT_PRESENT-MODIFY
                                                  (UPDATE-REGS
                                                   :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                   :EIP (SNPT-CODE-LOCATION)
                                                   :ESP (+ -24 (G :ESP S1))
                                                   (UPDATE-MEM
                                                    (+ -12 (G :ESP S1))
                                                    (R32 (+ 16 (G :ESP S1)) S1)
                                                    (+ -16 (G :ESP S1))
                                                    (R32 (+ 12 (G :ESP S1)) S1)
                                                    (+ -20 (G :ESP S1))
                                                    (R32 (+ 4 (G :ESP S1)) S1)
                                                    (+ -24 (G :ESP S1))
                                                    (+ 985 (SNPT-CODE-LOCATION))
                                                    (INIT_PDTS-MODIFY
                                                     (UPDATE-REGS
                                                      :EAX (R32 (+ 8 (G :ESP S1)) S1)
                                                      :EIP (+ 334 (SNPT-CODE-LOCATION))
                                                      :ESP (+ -24 (G :ESP S1))
                                                      (UPDATE-MEM
                                                       (+ -20 (G :ESP S1))
                                                       (R32 (+ 8 (G :ESP S1)) S1)
                                                       (+ -24 (G :ESP S1))
                                                       (+ 944 (SNPT-CODE-LOCATION))
                                                       (INIT_PDPT-MODIFY
                                                        (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                                     :EBP (+ -4 (G :ESP S1))
                                                                     :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                                     :ESP (+ -24 (G :ESP S1))
                                                                     :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                                     :F-OF
                                                                     (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                                         (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                                     :F-SF
                                                                     (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                                     :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                                     :IMME1 16
                                                                     (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                                 (G :EBP S1)
                                                                                 (+ -16 (G :ESP S1))
                                                                                 (R32 (+ 8 (G :ESP S1)) S1)
                                                                                 (+ -20 (G :ESP S1))
                                                                                 (R32 (+ 4 (G :ESP S1)) S1)
                                                                                 (+ -24 (G :ESP S1))
                                                                                 (+ 927 (SNPT-CODE-LOCATION))
                                                                                 S1))))))))))))))



            ("Subgoal 11'''"  :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                               (s1 (UPDATE-REGS
                                                    :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                    :EBP (G :EBP S1)
                                                    :EIP (+ 992 (SNPT-CODE-LOCATION))
                                                    :ESP (G :ESP S1)
                                                    (SEC_NOT_PRESENT-MODIFY
                                                     (UPDATE-REGS
                                                      :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                      :EIP (SNPT-CODE-LOCATION)
                                                      :ESP (+ -24 (G :ESP S1))
                                                      (UPDATE-MEM
                                                       (+ -12 (G :ESP S1))
                                                       (R32 (+ 16 (G :ESP S1)) S1)
                                                       (+ -16 (G :ESP S1))
                                                       (R32 (+ 12 (G :ESP S1)) S1)
                                                       (+ -20 (G :ESP S1))
                                                       (R32 (+ 4 (G :ESP S1)) S1)
                                                       (+ -24 (G :ESP S1))
                                                       (+ 985 (SNPT-CODE-LOCATION))
                                                       (INIT_PDTS-MODIFY
                                                        (UPDATE-REGS
                                                         :EAX (R32 (+ 8 (G :ESP S1)) S1)
                                                         :EIP (+ 334 (SNPT-CODE-LOCATION))
                                                         :ESP (+ -24 (G :ESP S1))
                                                         (UPDATE-MEM
                                                          (+ -20 (G :ESP S1))
                                                          (R32 (+ 8 (G :ESP S1)) S1)
                                                          (+ -24 (G :ESP S1))
                                                          (+ 944 (SNPT-CODE-LOCATION))
                                                          (INIT_PDPT-MODIFY
                                                           (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                                        :EBP (+ -4 (G :ESP S1))
                                                                        :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                                        :ESP (+ -24 (G :ESP S1))
                                                                        :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                                        :F-OF
                                                                        (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                                            (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                                        :F-SF
                                                                        (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                                        :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                                        :IMME1 16
                                                                        (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                                    (G :EBP S1)
                                                                                    (+ -16 (G :ESP S1))
                                                                                    (R32 (+ 8 (G :ESP S1)) S1)
                                                                                    (+ -20 (G :ESP S1))
                                                                                    (R32 (+ 4 (G :ESP S1)) S1)
                                                                                    (+ -24 (G :ESP S1))
                                                                                    (+ 927 (SNPT-CODE-LOCATION))
                                                                                    S1))))))))))))))

            ("Subgoal 11'6'" :use ((:instance |(r32 addr (sec_not_present-modify s))|
                                              (addr (g :esp s1))
                                              (s (UPDATE-REGS
                                                  :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                  :EIP (SNPT-CODE-LOCATION)
                                                  :ESP (+ -24 (G :ESP S1))
                                                  (UPDATE-MEM
                                                   (+ -12 (G :ESP S1))
                                                   (R32 (+ 16 (G :ESP S1)) S1)
                                                   (+ -16 (G :ESP S1))
                                                   (R32 (+ 12 (G :ESP S1)) S1)
                                                   (+ -20 (G :ESP S1))
                                                   (R32 (+ 4 (G :ESP S1)) S1)
                                                   (+ -24 (G :ESP S1))
                                                   (+ 985 (SNPT-CODE-LOCATION))
                                                   (INIT_PDTS-MODIFY
                                                    (UPDATE-REGS
                                                     :EAX (R32 (+ 8 (G :ESP S1)) S1)
                                                     :EIP (+ 334 (SNPT-CODE-LOCATION))
                                                     :ESP (+ -24 (G :ESP S1))
                                                     (UPDATE-MEM
                                                      (+ -20 (G :ESP S1))
                                                      (R32 (+ 8 (G :ESP S1)) S1)
                                                      (+ -24 (G :ESP S1))
                                                      (+ 944 (SNPT-CODE-LOCATION))
                                                      (INIT_PDPT-MODIFY
                                                       (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                                    :EBP (+ -4 (G :ESP S1))
                                                                    :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                                    :ESP (+ -24 (G :ESP S1))
                                                                    :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                                    :F-OF
                                                                    (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                                        (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                                    :F-SF
                                                                    (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                                    :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                                    :IMME1 16
                                                                    (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                                (G :EBP S1)
                                                                                (+ -16 (G :ESP S1))
                                                                                (R32 (+ 8 (G :ESP S1)) S1)
                                                                                (+ -20 (G :ESP S1))
                                                                                (R32 (+ 4 (G :ESP S1)) S1)
                                                                                (+ -24 (G :ESP S1))
                                                                                (+ 927 (SNPT-CODE-LOCATION))
                                                                                S1))))))))))))

            ("Subgoal 11.2"  :use ((:instance $$$DEFP-SYMSIM-THEOREM
                                              (s1 (UPDATE-REGS
                                                   :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                   :EBP (G :EBP S1)
                                                   :EIP (R32 (G :ESP S1) S1)
                                                   :ESP (+ 4 (G :ESP S1))
                                                   (SEC_NOT_PRESENT-MODIFY
                                                    (UPDATE-REGS
                                                     :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                     :EIP (SNPT-CODE-LOCATION)
                                                     :ESP (+ -24 (G :ESP S1))
                                                     (UPDATE-MEM
                                                      (+ -12 (G :ESP S1))
                                                      (R32 (+ 16 (G :ESP S1)) S1)
                                                      (+ -16 (G :ESP S1))
                                                      (R32 (+ 12 (G :ESP S1)) S1)
                                                      (+ -20 (G :ESP S1))
                                                      (R32 (+ 4 (G :ESP S1)) S1)
                                                      (+ -24 (G :ESP S1))
                                                      (+ 985 (SNPT-CODE-LOCATION))
                                                      (INIT_PDTS-MODIFY
                                                       (UPDATE-REGS
                                                        :EAX (R32 (+ 8 (G :ESP S1)) S1)
                                                        :EIP (+ 334 (SNPT-CODE-LOCATION))
                                                        :ESP (+ -24 (G :ESP S1))
                                                        (UPDATE-MEM
                                                         (+ -20 (G :ESP S1))
                                                         (R32 (+ 8 (G :ESP S1)) S1)
                                                         (+ -24 (G :ESP S1))
                                                         (+ 944 (SNPT-CODE-LOCATION))
                                                         (INIT_PDPT-MODIFY
                                                          (UPDATE-REGS :EAX (R32 (+ 4 (G :ESP S1)) S1)
                                                                       :EBP (+ -4 (G :ESP S1))
                                                                       :EIP (+ 687 (SNPT-CODE-LOCATION))
                                                                       :ESP (+ -24 (G :ESP S1))
                                                                       :F-CF (SUBL-CF 16 (+ -4 (G :ESP S1)))
                                                                       :F-OF
                                                                       (OF (N32-TO-I32 (+ -20 (G :ESP S1)))
                                                                           (+ -16 (N32-TO-I32 (+ -4 (G :ESP S1)))))
                                                                       :F-SF
                                                                       (SF (N32-TO-I32 (+ -20 (G :ESP S1))))
                                                                       :F-ZF (ZF (+ -20 (G :ESP S1)))
                                                                       :IMME1 16
                                                                       (UPDATE-MEM (+ -4 (G :ESP S1))
                                                                                   (G :EBP S1)
                                                                                   (+ -16 (G :ESP S1))
                                                                                   (R32 (+ 8 (G :ESP S1)) S1)
                                                                                   (+ -20 (G :ESP S1))
                                                                                   (R32 (+ 4 (G :ESP S1)) S1)
                                                                                   (+ -24 (G :ESP S1))
                                                                                   (+ 927 (SNPT-CODE-LOCATION))
                                                                                   S1))))))))))))))

            ("Subgoal 11.1" :cases ((equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 0)
                                    (equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 1)
                                    (equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 2)
                                    (equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 3)))

            ("Subgoal 8" :cases ((equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 0)
                                 (equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 1)
                                 (equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 2)
                                 (equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 3)))

            ("Subgoal 5" :cases ((equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 0)
                                 (equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 1)
                                 (equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 2)
                                 (equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 3)))

            ("Subgoal 2" :cases ((equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 0)
                                 (equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 1)
                                 (equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 2)
                                 (equal (ASH (R32 (+ 12 (G :ESP S1)) S1) -30) 3)))

            )
    :otf-flg t))



 (local
  (set-default-hints nil))

 (local
  (in-theory (disable |(y86-step st)|
                      |(logior 1 x)|)))

 (local
  (defun assertion-invariant-default-hint-1 (hyps)
    (cond ((endp hyps)
           (mv nil nil))                ; should be error
          ((and (equal (fn-symb (car hyps)) 'NOT)
                (equal (fn-symb (arg1 (car hyps))) 'EQUAL)
                (equal (fn-symb (arg1 (arg1 (car hyps)))) 'S)
                (equal (arg2 (arg1 (car hyps))) 'S1))
           (mv (cdr hyps) (arg1 (arg1 (car hyps)))))
          ((and (equal (fn-symb (car hyps)) 'NOT)
                (equal (fn-symb (arg1 (car hyps))) 'EQUAL)
                (equal (fn-symb (arg2 (arg1 (car hyps)))) 'S)
                (equal (arg1 (arg1 (car hyps))) 'S1))
           (mv (cdr hyps) (arg2 (arg1 (car hyps)))))
          (t
           (mv-let (new-hyps s1-subst)
                   (assertion-invariant-default-hint-1 (cdr hyps))
                   (mv (cons (car hyps) new-hyps)
                       s1-subst))))))

 (local
  (defun assertion-invariant-default-hint (stable-under-simplificationp clause world)
    (declare (xargs :mode :program))
    (if stable-under-simplificationp
        (b* ((concl (car (last clause)))
             ((mv new-hyps s1-subst)
              (assertion-invariant-default-hint-1 (butlast clause 1)))
             (concl-vars (all-vars concl))
             (new-concl `((LAMBDA ,concl-vars ,concl) ,@(subst s1-subst 's1 concl-vars)))
             (instance (prettyify-clause (append new-hyps
                                                 (list new-concl))
                                         nil world)))
            `(:use ((:instance
                     (:theorem ,instance)))
                   ;; :expand ((INIT_PDTS-MODIFY-LOOP-1 (R32 (+ -20 (G :EBP S1)) S1)
                   ;;                                  S0))
                   ))
      nil)))


 (local
  (set-default-hints '((assertion-invariant-default-hint stable-under-simplificationp
                                                         clause
                                                         world))))

 (local
  (set-default-hints nil))


 (LOCAL (DEFTHM $$$ASSERTION-INVARIANT-OVER-CUTPOINTS
          (IMPLIES (AND (CREATE_NESTED_PT-ASSERTION S0 S1)
                        (IN-CREATE_NESTED_PT S1)
                        (LET* ((S1 (Y86 S1 N)))
                              (NOT (IN-CREATE_NESTED_PT S1))))
                   (LET* ((S1 (Y86-STEP S1))
                          (S1 ($$$NEXT-CUTPOINT-MAIN S1)))
                         (CREATE_NESTED_PT-ASSERTION S0 S1)))
          :RULE-CLASSES NIL
          :HINTS NIL))




 (LOCAL (IN-THEORY (THEORY 'GROUND-ZERO)))
 (DEFP CREATE_NESTED_PT-EXITSTEPS-TAIL (S1 I)
   (IF (NOT (IN-CREATE_NESTED_PT S1))
       I
       (LET* ((S1 (Y86-STEP S1)))
             (CREATE_NESTED_PT-EXITSTEPS-TAIL S1 (1+ I)))))
 (DEFUN CREATE_NESTED_PT-EXITSTEPS (S1)
   (LET* ((STEPS (CREATE_NESTED_PT-EXITSTEPS-TAIL S1 0))
          (S1 (Y86 S1 STEPS)))
         (IF (NOT (IN-CREATE_NESTED_PT S1))
             STEPS (OMEGA))))
 (DEFUN-SK CREATE_NESTED_PT-EXISTS-NEXT-EXITPOINT
   (S1)
   (EXISTS N
           (LET* ((S1 (Y86 S1 N)))
                 (NOT (IN-CREATE_NESTED_PT S1)))))
 (DEFUN CREATE_NESTED_PT-NEXT-EXITPOINT (S1)
   (LET* ((STEPS (CREATE_NESTED_PT-EXITSTEPS S1)))
         (Y86 S1 STEPS)))
 (LOCAL (IN-THEORY (THEORY 'MINIMAL-THEORY)))
 (DEFTHM
   CREATE_NESTED_PT-CORRECT
   (IMPLIES (AND (CREATE_NESTED_PT-PRE S1)
                 (CREATE_NESTED_PT-EXISTS-NEXT-EXITPOINT S1))
            (AND (LET ((S1 (CREATE_NESTED_PT-NEXT-EXITPOINT S1)))
                      (NOT (IN-CREATE_NESTED_PT S1)))
                 (EQUAL (CREATE_NESTED_PT-NEXT-EXITPOINT S1)
                        (CREATE_NESTED_PT-MODIFY S1))))
   :OTF-FLG T
   :RULE-CLASSES NIL
   :HINTS
   (("Goal"
     :USE
     ((:INSTANCE
       (:FUNCTIONAL-INSTANCE
        |epc composite partial correctness|
        (EPC-NEXT (LAMBDA (S)
                          (LET ((S1 S)) (Y86-STEP S1))))
        (EPC-RUN (LAMBDA (S N) (Y86 S N)))
        (EXISTS-EPC-NEXT-CUTPOINT
         (LAMBDA (S)
                 (LET ((S1 S))
                      ($$$EXISTS-NEXT-CUTPOINT S1))))
        (EXISTS-EPC-NEXT-CUTPOINT-WITNESS
         (LAMBDA (S)
                 (LET ((S1 S))
                      ($$$EXISTS-NEXT-CUTPOINT-WITNESS S1))))
        (EPC-PRE-SUB (LAMBDA (S)
                             (LET ((S1 S)) ($$$PRESUB S1))))
        (EPC-IN-SUB (LAMBDA (S) (LET ((S1 S)) (IN-SUB S1))))
        (EPC-EXISTS-EXITPOINT-SUB (LAMBDA (S)
                                          (LET ((S1 S))
                                               (EXISTS-NEXT-EXITPOINT S1))))
        (EPC-EXISTS-EXITPOINT-SUB-WITNESS
         (LAMBDA (S)
                 (LET ((S1 S))
                      (EXISTS-NEXT-EXITPOINT-WITNESS S1))))
        (EPC-STEPS-TO-EXITPOINT-TAIL-SUB
         (LAMBDA (S I)
                 (LET ((S1 S)) (EXITSTEPS-TAIL S1 I))))
        (EPC-MODIFY-SUB (LAMBDA (S)
                                (LET ((S1 S)) ($$$MODIFYSUB S1))))
        (EPC-NEXT-EXITPOINT-SUB (LAMBDA (S)
                                        (LET ((S1 S)) (NEXT-EXITPOINT S1))))
        (EPC-STEPS-TO-EXITPOINT-SUB (LAMBDA (S)
                                            (LET ((S1 S)) (EXITSTEPS S1))))
        (EPC-PRE-MAIN (LAMBDA (S)
                              (LET ((S1 S))
                                   (CREATE_NESTED_PT-PRE S1))))
        (EPC-CUTPOINT-MAIN (LAMBDA (S)
                                   (LET ((S1 S))
                                        (CREATE_NESTED_PT-CUTPOINT-P S1))))
        (EPC-EXISTS-EXITPOINT-MAIN
         (LAMBDA (S)
                 (LET ((S1 S))
                      (CREATE_NESTED_PT-EXISTS-NEXT-EXITPOINT S1))))
        (EPC-EXISTS-EXITPOINT-MAIN-WITNESS
         (LAMBDA (S)
                 (LET ((S1 S))
                      (CREATE_NESTED_PT-EXISTS-NEXT-EXITPOINT-WITNESS S1))))
        (EPC-NEXT-EXITPOINT-MAIN
         (LAMBDA (S)
                 (LET ((S1 S))
                      (CREATE_NESTED_PT-NEXT-EXITPOINT S1))))
        (EPC-EXITSTEPS-MAIN (LAMBDA (S)
                                    (LET ((S1 S))
                                         (CREATE_NESTED_PT-EXITSTEPS S1))))
        (EPC-EXITSTEPS-MAIN-TAIL
         (LAMBDA (S I)
                 (LET ((S1 S))
                      (CREATE_NESTED_PT-EXITSTEPS-TAIL S1 I))))
        (EPC-IN-MAIN (LAMBDA (S)
                             (LET ((S1 S))
                                  (IN-CREATE_NESTED_PT S1))))
        (EPC-NEXT-EPC-CUTPOINT-MAIN
         (LAMBDA (S)
                 (LET ((S1 S))
                      ($$$NEXT-CUTPOINT-MAIN S1))))
        (EPC-ASSERTION-MAIN
         (LAMBDA (S0 S)
                 (LET ((S0 S0) (S1 S))
                      (CREATE_NESTED_PT-ASSERTION S0 S1))))
        (EPC-MODIFY-MAIN (LAMBDA (S)
                                 (LET ((S1 S))
                                      (CREATE_NESTED_PT-MODIFY S1)))))
       (S S1))))
    ("Subgoal 22" :USE ((:INSTANCE $$$ASSERTION-INVARIANT-OVER-CUTPOINTS
                                   (S0 S0)
                                   (S1 S))))
    ("Subgoal 21" :USE ((:INSTANCE $$$ASSERTION-MAIN-IMPLIES-POST (S0 S0)
                                   (S1 S))))
    ("Subgoal 20" :USE ((:INSTANCE $$$PRE-IMPLIES-ASSERTION (S1 S))))
    ("Subgoal 19" :USE ((:INSTANCE $$$ASSERTION-IMPLIES-CUTPOINT (S0 S0)
                                   (S1 S))))
    ("Subgoal 18" :USE ((:INSTANCE $$$PRESUB-IMPLIES-INSUB (S1 S))))
    ("Subgoal 17" :USE ((:INSTANCE $$$IN-SUB-IMPLIES-IN-MAIN (S1 S))))
    ("Subgoal 16" :USE ((:INSTANCE $$$NO-MAIN-CUTPOINT-IN-SUB (S1 S))))
    ("Subgoal 15" :USE ((:INSTANCE (:DEFINITION $$$EXISTS-NEXT-CUTPOINT)
                                   (S1 S))))
    ("Subgoal 14" :USE ((:INSTANCE $$$EXISTS-NEXT-CUTPOINT-SUFF (S1 S))))
    ("Subgoal 13" :USE ((:INSTANCE $$$NEXT-CUTPOINT-MAIN$DEF (S1 S))))
    ("Subgoal 12" :USE ((:INSTANCE $$$CORRECTNESS-OF-SUB (S1 S))))
    ("Subgoal 11" :USE ((:INSTANCE EXITSTEPS-TAIL$DEF (S1 S))))
    ("Subgoal 10" :USE ((:INSTANCE (:DEFINITION EXISTS-NEXT-EXITPOINT)
                                   (S1 S))))
    ("Subgoal 9" :USE ((:INSTANCE EXISTS-NEXT-EXITPOINT-SUFF (S1 S))))
    ("Subgoal 8" :USE ((:INSTANCE (:DEFINITION NEXT-EXITPOINT)
                                  (S1 S))))
    ("Subgoal 7" :USE ((:INSTANCE (:DEFINITION EXITSTEPS)
                                  (S1 S))))
    ("Subgoal 6" :IN-THEORY (ENABLE Y86))
    ("Subgoal 5"
     :USE ((:INSTANCE (:DEFINITION CREATE_NESTED_PT-NEXT-EXITPOINT)
                      (S1 S))))
    ("Subgoal 4" :USE ((:INSTANCE (:DEFINITION CREATE_NESTED_PT-EXITSTEPS)
                                  (S1 S))))
    ("Subgoal 3" :USE ((:INSTANCE CREATE_NESTED_PT-EXITSTEPS-TAIL$DEF
                                  (S1 S))))
    ("Subgoal 2"
     :USE ((:INSTANCE CREATE_NESTED_PT-EXISTS-NEXT-EXITPOINT-SUFF
                      (S1 S))))
    ("Subgoal 1"
     :USE ((:INSTANCE (:DEFINITION CREATE_NESTED_PT-EXISTS-NEXT-EXITPOINT)
                      (S1 S))))))

)



#||
(defsimulate+
  y86-step
  :run y86
  :inmain in-create_nested_pt
  :cutpoint create_nested_pt-cutpoint-p
  :assertion-params (s0 s1)
  :precondition create_nested_pt-pre
  :assertion create_nested_pt-assertion
  :modify create_nested_pt-modify

  :subs ((init_pdpt-pre init_pdpt-modify init_pdpt-correct)
         (init_pdts-pre init_pdts-modify init_pdts-correct)
         (sec_not_present-pre sec_not_present-modify sec_not_present-correct))
  :insub in-sub

  :exists-exitpoint-sub exists-next-exitpoint
  :steps-to-exitpoint-sub exitsteps
  :steps-to-exitpoint-sub-tail exitsteps-tail
  :next-exitpoint-sub next-exitpoint

  :exitsteps create_nested_pt-exitsteps
  :exists-next-exitpoint create_nested_pt-exists-next-exitpoint
  :next-exitpoint create_nested_pt-next-exitpoint

  :correctness-theorem create_nested_pt-correct)o
||#

