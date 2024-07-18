; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Robert Krug         <rkrug@cs.utexas.edu>
; Shilpi Goel         <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-structures" :dir :utils)
(include-book "physical-memory" :ttags (:undef-flg :include-raw))
(include-book "clause-processors/find-matching" :dir :system)

;; [Shilpi]: For now, I've removed nested paging and all paging modes
;; except IA-32e paging from our model.

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

(defsection paging
  :parents (machine)
  :short "Specification of x86 Paging"
  )

(defsection ia32e-paging
  :parents (paging)
  :short "Specification of Paging in the 64-bit Mode"
  )

(local (xdoc::set-default-parents ia32e-paging))

;; ======================================================================

(define same-page ((lin-addr integerp)
                   (lin-addr-2 integerp))
  (or (equal lin-addr lin-addr-2)
      (and (mbt (and (integerp lin-addr)
                     (integerp lin-addr-2)))
           (equal (logtail 12 lin-addr)
                  (logtail 12 lin-addr-2))))
  ///
  (defequiv same-page)

  (local (defthmd equal-logtail-i-implies-equal-logtail-j-for-j>=i
                  (implies (and (natp i)
                                (integerp x)
                                (integerp y)
                                (integerp j)
                                (>= j i)
                                (equal (logtail i x)
                                       (logtail i y)))
                           (equal (logtail j x)
                                  (logtail j y)))
                  :hints (("Goal" :in-theory (enable logtail**
                                                     bitops::logtail-induct)))))

  (defthm same-page-implies-logtails>=12-equal
          (implies (and (integerp i)
                        (>= i 12)
                        (same-page y (double-rewrite x))
                        (syntaxp (not (equal x y))))
                   (equal (logtail i x)
                          (logtail i y)))
          :hints (("Goal" :use (:instance equal-logtail-i-implies-equal-logtail-j-for-j>=i (i 12) (j i) (x x) (y y)))))

  (defthm same-page-address-construction
          (implies (same-page x y)
                   (same-page (logior (loghead i x)
                                      (ash z i))
                              (logior (loghead i y)
                                      (ash z i))))
          :rule-classes :congruence)

  (defthm same-page-implies-logapp<=12-equal
          (implies (and (integerp n)
                        (<= n 12)
                        (same-page y (double-rewrite x))
                        (syntaxp (not (equal x y))))
                   (same-page (logapp n x z)
                              (logapp n y z)))
          :hints (("Goal" :in-theory (enable logtail**
                                             bitops::logtail-induct
                                             logapp**
                                             bitops::logapp-induct))))

  (defthm same-page-implies-same-page-logheads
          (implies (same-page a b)
                   (same-page (loghead n a) (loghead n b)))
          :rule-classes :congruence)

  (local (defthmd logext-maintains-logtail-equals
                  (implies (and (integerp k)
                                (> k n)
                                (natp n)
                                (integerp x)
                                (integerp y)
                                (equal (logtail n x)
                                       (logtail n y)))
                           (equal (logtail n (logext k x))
                                  (logtail n (logext k y))))
                  :hints (("Goal" :in-theory (enable logtail**
                                                     bitops::logtail-induct
                                                     logext**
                                                     bitops::logext-induct)))))

  (defthm logexting-maintains-same-page
          (implies (and (integerp n)
                        (> n 12)
                        (same-page y (double-rewrite x))
                        (syntaxp (not (equal x y))))
                   (same-page (logext n x)
                              (logext n y)))
          :hints (("Goal" :use (:instance logext-maintains-logtail-equals (n 12) (k n)))))

  (defthmd logtails<=12-equal-implies-same-page
           (implies (and (integerp x)
                         (integerp y)
                         (natp n)
                         (<= n 12)
                         (equal (logtail n x) (logtail n y)))
                    (same-page x y))
           :hints (("Goal" :use (:instance equal-logtail-i-implies-equal-logtail-j-for-j>=i (j 12) (i n))))))

(defthm 0-loghead-of-ash
        (implies (and (natp n)
                      (natp m)
                      (<= n m))
                 (equal (loghead n (ash x m))
                        0))
        :hints (("Goal" :in-theory (enable loghead** bitops::loghead-induct
                                           ash** bitops::ash**-induct))))

(define same-page-offset ((lin-addr integerp)
                          (lin-addr-2 integerp))
  (equal (loghead 12 lin-addr)
         (loghead 12 lin-addr-2))
  ///
  (defequiv same-page-offset)

  (defthm same-page-offset-addr-construction
          (implies (and (natp n)
                        (>= n 12))
                   (same-page-offset (logior (loghead n x)
                                             (ash y n))
                                     x)))

  (defthm logexted-is-same-page
          (implies (and (natp n)
                        (>= n 12))
                   (same-page-offset (logext n x)
                                     x)))

  (local (defthmd equal-loghead-implies-equal-more-restrictive-logheads
                  (implies (and (natp n)
                                (natp m)
                                (<= m n)
                                (equal (loghead n x)
                                       (loghead n y)))
                           (equal (loghead m x)
                                  (loghead m y)))
                  :hints (("Goal" :in-theory (enable loghead** bitops::loghead-induct)))))

  (defthm same-page-offset-implies-same-logheads
          (implies (and (natp n)
                        (<= n 12)
                        (same-page-offset y (double-rewrite x))
                        (syntaxp (not (equal x y))))
                   (equal (loghead n x)
                          (loghead n y)))
          :hints (("Goal" :use (:instance equal-loghead-implies-equal-more-restrictive-logheads
                                          (n 12) (m n) (x x) (y y))))))

(defthm loghead-zero-smaller
  (implies (and (equal (loghead n x) 0)
                (natp n)
                (<= m n))
           (equal (loghead m x) 0))
  :hints (("Goal" :in-theory (e/d*
                              (acl2::ihsext-recursive-redefs
                               acl2::ihsext-inductions)
                              ()))))

(define virtual-page-num-p (x)
  :inline t
  (signed-byte-p (- *max-linear-address-size* 12) x)
  ///
  (defthm virtual-page-num-p-thm
          (equal (virtual-page-num-p x)
                 (signed-byte-p (- *max-linear-address-size* 12) x))
          :rule-classes :rewrite)

  (define virtual-page-num-fix ((x virtual-page-num-p))
    :enabled t
    :inline t
    (mbe :logic (if (virtual-page-num-p x) x 0)
         :exec x))

  (fty::deffixtype virtual-page-num
    :pred virtual-page-num-p
    :fix virtual-page-num-fix
    :equiv virtual-page-num-equiv
    :define t))

(define physical-page-num-p (x)
  :inline t
  (unsigned-byte-p (- *physical-address-size* 12) x)
  ///
  (defthm physical-page-num-p-thm
          (equal (physical-page-num-p x)
                 (unsigned-byte-p (- *physical-address-size* 12) x))
          :rule-classes :rewrite)

  (define physical-page-num-fix ((x physical-page-num-p))
    :enabled t
    :inline t
    (mbe :logic (if (physical-page-num-p x) x 0)
         :exec x))

  (fty::deffixtype physical-page-num
    :pred physical-page-num-p
    :fix physical-page-num-fix
    :equiv physical-page-num-equiv
    :define t))

(define page-walk-err-p (x)
  (or (not x)
      (equal x :not-present)
      (equal x :rsvd-set))
  ///
  (defthm page-walk-err-p-thm
          (implies
            (or (not x)
                (equal x :not-present)
                (equal x :rsvd-set))
            (page-walk-err-p x))))

;; This defines *paging-levels* and functions <prefix><level-name> that perform
;; the page table walk. The only effect they have on the state is that they may
;; set the accessed bit in paging structure entries. The page table walk is
;; completely independent of x86 fields except for memory. This allows us to
;; implement the tlb in a manner that is compliant with the x86 ISA.
(defmacro generate-page-table-walk
  (;; The width of a paging entry
   entry-width
   ;; Number of bits used to index into a single level of the tables
   level-width
   ;; Given the address of a paging structure entry and the state, return the entry
   entry-accessor
   ;; Function that takes an entry and determines whether it is present This
   ;; can't be an exit because exits are handled after setting the accessed
   ;; bit, but presence must be tested before updating the accessed bit
   present-p
   ;; Set accessed bit, if necessary. Takes the entry, entry address, and the
   ;; state and returns a new state
   set-accessed-bit
   ;; Function that takes a paging entry and returns the physical page number of the
   ;; next table or, if at the last table, returns the translation
   next
   ;; A prefix to apply before the name of the page table walk functions
   prefix
   ;; Accumulator specifications look as follows:
   ;; (<id> <tlb entry accessor> <fold op> <page structure accessor>)
   ;; These are how we define values getting accumulated into the tlb entry. At
   ;; each level, the value in the tlb entry is replaced with
   ;; (<fold op> (<tlb entry accessor> tlb-entry) (<page structure accessor> entry))
   accumulators
   ;; Exit specifiers look as follows:
   ;; (<id> <condition> <return-val>)
   ;; If <condition> is true, we return <return-val>.
   exits
   ;; Write translation ppn into tlb-entry
   write-ppn
   ;; Level specifiers look as follows:
   ;; (<level-name> [:excludes (<id_1> <id_2> ... <id_n>)])
   ;; This states that level-name is a level of the page table walk and <id_i>
   ;; (which may refer to any combination of accumulators and exits) should not
   ;; be used at this level of the page table walk. Levels must be specified in
   ;; order, highest level first. rsvd-set-p is a predicate that examines an entry
   ;; at this level and returns true iff a reserved bit is set in that entry.
   levels)
  (b* ((nlevels (len (unquote levels))))
      ;; make-event is required here because of some weirdness with using
      ;; collect and when in macros.
      `(make-event
         `(encapsulate
            ()

            (defconst *paging-levels*
                      ',(loop$ for level in ,levels
                               collect
                               (car level)))
            ,@(reverse
                (loop$
                  for level in ,levels
                  as n from 0 to (1- ,nlevels)
                  as next-level in (append (cdr,levels) (list nil))
                  collect
                  (b* (;; Get the value associated with the keywords if it was
                       ;; found otherwise, it remains nil
                       (excludes (assoc-keyword :excludes (cdr level)))
                       (excludes (if excludes (cadr excludes) excludes)))

                      `(define ,(acl2::packn (list ,prefix (car level)))
                         ((vpn virtual-page-num-p
                               "The virtual page number we are translating.")
                          (base-ppn physical-page-num-p
                                    "The physical page number of this level of the table.")
                          (tlb-entry tlb-entry-p
                                     "The tlb entry that has been constructed so far.")
                          x86)
                         :guard (not (app-view x86))
                         :guard-hints (("Goal" :expand ((:with logapp (:free (x y) (logapp 12 x y))))))
                         :returns (mv (flg page-walk-err-p)
                                      (tlb-entry tlb-entry-p)
                                      (x86 x86p :hyp (x86p x86)))
                         :prepwork
                         ((local (include-book "arithmetic-5/top" :dir :system)))

                         (b* ((vpn (virtual-page-num-fix vpn))
                              (base-ppn (physical-page-num-fix base-ppn))
                              ((the (unsigned-byte ,,level-width) idx)
                               (loghead ,,level-width
                                        (ash vpn
                                             ,(* -1 (- (1- ,nlevels) n) ,level-width))))
                              (entry-addr (logapp 12 (* idx ,,entry-width)
                                                  base-ppn))
                              (entry (,,entry-accessor entry-addr x86))

                              ((unless (,,present-p entry)) (mv :not-present 0 x86))

                              (x86 (,,set-accessed-bit entry entry-addr x86))

                              (?xlation-width ,(* ,level-width (1+ n)))

                              ;; Accumulate all the values into tlb-entry
                              ,@(loop$
                                  for accumulator in ,accumulators
                                  when (not (member (car accumulator) excludes))
                                  collect
                                  `(tlb-entry (,(acl2::packn (list '! (cadr accumulator)))
                                                (,(caddr accumulator)
                                                  (,(cadr accumulator) tlb-entry)
                                                  (,(cadddr accumulator) entry))
                                                tlb-entry)))

                              ;; Check if we should exit early
                              ,@(loop$
                                  for exit in ,exits
                                  when (not (member (car exit) excludes))
                                  collect
                                  `((when ,(cadr exit))
                                    ,(caddr exit))))

                             ;; If this is the final level of the walk, we
                             ;; can return the tlb entry after adding the
                             ;; ppn to it. Otherwise, we continue to the
                             ;; next level.
                             ,(if (null next-level)
                                `(mv nil (,,write-ppn (,,next entry) tlb-entry) x86)
                                `(,(acl2::packn (list ,prefix (car next-level)))
                                   vpn (,,next entry) tlb-entry x86)))
                         ///
                         (fty::deffixequiv ,(acl2::packn (list ,prefix (car level))))))))))))

;; This is a tlb entry with the identity for all the accumulators. It is passed
;; to the top level page table walk.
(defconst *initial-tlb-entry*
          (make-tlb-entry :r/w 1 :u/s 1 :xd 0))

(generate-page-table-walk
  8
  9
  'rm-low-64
  '(lambda (entry) (eql (ia32e-page-tablesBits->p entry) 1))
  '(lambda (entry entry-addr x86)
     (if (not (eql (ia32e-page-tablesBits->a entry) 1))
       (wm-low-64 entry-addr (!ia32e-page-tablesBits->a 1 entry) x86)
       x86))
  'ia32e-page-tablesBits->reference-addr
  'walk-table-
  '((r/w tlb-entry->r/w b-and ia32e-page-tablesBits->r/w)
    (u/s tlb-entry->u/s b-and ia32e-page-tablesBits->u/s)
    (xd tlb-entry->xd b-ior ia32e-page-tablesBits->xd)
    (d tlb-entry->d prog2$ ia32e-page-tablesBits->d)
    (lowest-level-paging-entry-addr tlb-entry->lowest-level-paging-entry-addr
                                    prog2$ (lambda (x)
                                             (declare (ignore x))
                                             (logtail 3 entry-addr))))
  '(;; ps is a reserved bit if this is a level where large pages are not allowed
    (ps-rsvd (eql (ia32e-page-tablesBits->ps entry) 1)
             (mv :rsvd-set 0 x86))
    ;; xd is reserved if nxe = 0
    (xd-maybe-rsvd (and (eql (ia32e-page-tablesBits->xd entry) 1)
                        (eql (ia32_eferBits->nxe (n12 (msri *ia32_efer-idx* x86))) 0))
                   (mv :rsvd-set 0 x86))
    ;; Larger than 4k page
    (large-page (eql (ia32e-page-tablesBits->ps entry) 1)
                (b* ((discard-width (- (- *max-linear-address-size* 12) xlation-width))
                     (addr (ia32e-page-tablesBits->reference-addr entry))
                     ;; The lower bits in the address field are reserved, except for the lsb,
                     ;; which is the PAT bit
                     ((unless (eql (logtail 1 (loghead discard-width addr)) 0)) (mv :rsvd-set 0 x86))
                     (tlb-entry (!tlb-entry->ppn
                                  (logapp discard-width vpn (logtail discard-width addr))
                                  tlb-entry)))
                    (mv nil tlb-entry x86))))
  '!tlb-entry->ppn
  '((pml4-table :excludes (d large-page lowest-level-paging-entry-addr))
    (page-dir-ptr-table :excludes (ps-rsvd))
    (page-directory :excludes (ps-rsvd))
    ;; We exclude ps-rsvd here because the ps bit is the PAT bit in the page table
    (page-table :excludes (large-page ps-rsvd))))

(include-book "projects/apply/base" :dir :system)

(in-theory (e/d (take) (acl2::alternative-take acl2::take-opener)))

;; This function takes the current paging level and the arguments that are
;; passed to defthm-paging and expands the occurrences of walk-table-level
(define defthm-paging-expansion
  ((level symbolp)
   tree)
  (if (atom tree)
    (if (equal tree 'walk-table-level)
      (acl2::packn (list 'walk-table- level))
      tree)
    (cons (defthm-paging-expansion level (car tree))
          (defthm-paging-expansion level (cdr tree))))
  ///
  (defbadge defthm-paging-expansion)
  (defwarrant defthm-paging-expansion))

;; It is often necessary to prove theorems about paging that apply to all
;; levels of the paging hierarchy. This macro is just like defthm except in the
;; arguments (except for the name) one may use the symbol walk-table-level. The
;; given theorem is submitted to defthm once for each level of the paging
;; hierarchy with the name of the level of the paging hierarchy appended to the
;; theorem name and the symbol walk-table-level replaced with
;; walk-table-<level>. The theorems are submitted in reverse order of the page
;; table walk (i.e. leaf first).
(defmacro defthm-paging
  (name &rest rst)
  ;; We use make-event because loop$ isn't supported in macros
  `(make-event
    `(encapsulate
      ()

      ,@(loop$
          for level in (reverse *paging-levels*)
          collect
          `(encapsulate
             ()

             (defthm ,(acl2::packn (list ',name level))
                     ,@(defthm-paging-expansion level ',rst)))))))

;; Proves that the paging result is invariant under a given operation on the
;; x86 state.
(defmacro defthm-paging-values-invariant
  (name hyps op &rest rst)
  `(defthm-paging
     ,name
     (implies
       ,hyps
       (and (equal (mv-nth 0 (walk-table-level vpn base-ppn tlb-entry ,op))
                   (mv-nth 0 (walk-table-level vpn base-ppn tlb-entry x86)))
            (equal (mv-nth 1 (walk-table-level vpn base-ppn tlb-entry ,op))
                   (mv-nth 1 (walk-table-level vpn base-ppn tlb-entry x86)))))
     ,@rst))

(defthm-paging
  xr-of-walk-table-
  (implies (not (equal fld :mem))
           (equal (xr fld idx (mv-nth 2 (walk-table-level vpn base-ppn tlb-entry x86)))
                  (xr fld idx x86)))
  :hints (("Goal" :in-theory (enable walk-table-level))))

(defthm-paging-values-invariant
  walk-table-of-xw-
  (and (not (equal fld :mem))
       (not (equal fld :msr))
       (not (equal fld :app-view)))
  (xw fld idx val x86)
  :hints (("Goal" :in-theory (enable walk-table-level))))

(defthm-paging
  mv-nth-2-walk-table-of-xw-
  (implies (and (not (equal fld :mem))
                (not (equal fld :msr))
                (not (equal fld :app-view)))
           (equal (mv-nth 2 (walk-table-level vpn base-ppn tlb-entry (xw fld idx val x86)))
                  (xw fld idx val (mv-nth 2 (walk-table-level vpn base-ppn tlb-entry x86)))))
  :hints (("Goal" :in-theory (enable walk-table-level))))

(defabbrev cpl (x86)
  (the (unsigned-byte 2)
       (segment-selectorBits->rpl
        (the (unsigned-byte 16) (seg-visiblei #.*cs* x86)))))

(defthm-unsigned-byte-p n64p-xr-ctr
  :hyp t
  :bound 64
  :concl (xr :ctr i x86)
  :gen-linear t
  :gen-type t)

(define check-access
  ((tlb-entry tlb-entry-p)
   (r-w-x :type (member :r :w :x))
   x86
   &optional
   ;; TO-DO: For now, we are treating all supervisor-mode accesses as
   ;; explicit. We need to detect and then account for implicit
   ;; accesses later.
   ((supervisor-mode-access-type
                      :type (unsigned-byte 1)
                      "@('0'): Explicit; @('1'): Implicit")
    ;; Default value is 0.
    '0))
  :enabled t
  :returns (err booleanp)
  (b* ((cpl (cpl x86))
       (cr0
         ;; CR0 is still a 32-bit register in 64-bit mode.
         (n32 (ctri *cr0* x86)))
       (cr4
         ;; CR4 has all but the low 22 bits reserved.
         (n22 (ctri *cr4* x86)))
       (wp        (cr0Bits->wp cr0))
       (ac        (rflagsBits->ac (rflags x86)))
       (smep      (cr4Bits->smep cr4))
       (smap      (cr4Bits->smap cr4))
       (ia32-efer (n12 (msri *ia32_efer-idx* x86)))
       (nxe       (ia32_eferBits->nxe ia32-efer)))
      (or
        ;; Read fault:
        (and (equal r-w-x :r)
             (if (< cpl 3)
               (if (equal (tlb-entry->u/s tlb-entry) 0)
                 ;; Data may be read (implicitly or explicitly)
                 ;; from any supervisor-mode address.
                 nil
                 ;; Data reads from user-mode pages
                 (if (equal smap 0)
                   ;; If CR4.SMAP = 0, data may be read from
                   ;; any user-mode address.
                   nil
                   ;; If CR4.SMAP = 1: If EFLAGS.AC = 1 and the
                   ;; access is explicit, data may be read from any
                   ;; user-mode address. If EFLAGS.AC = 0 or the
                   ;; access is implicit, data may not be read from
                   ;; any user-mode address.
                   (or (equal supervisor-mode-access-type 1)
                       (equal ac 0))))
               ;; In user mode (CPL = 3), data may be read from
               ;; any linear address with a valid translation
               ;; for which the U/S flag (bit 2) is 1 in every
               ;; paging-structure entry controlling the trans-
               ;; lation.
               (equal (tlb-entry->u/s tlb-entry) 0)))
        ;; Write fault:
        (and (equal r-w-x :w)
             (if (< cpl 3)
               (if (equal (tlb-entry->u/s tlb-entry) 0)
                 ;; Data writes to supervisor-mode addresses.

                 ;; If CR0.WP = 0, data may be written to
                 ;; any supervisor-mode address.  If CR0.WP
                 ;; = 1, data may be written to any
                 ;; supervisor-mode address with a
                 ;; translation for which the R/W flag (bit
                 ;; 1) is 1 in every paging-structure entry
                 ;; controlling the translation.
                 (and (equal wp 1)
                      (equal (tlb-entry->r/w tlb-entry) 0))

                 ;; Data writes to user-mode addresses.

                 (if (equal wp 0)
                   ;; If CR4.SMAP = 0, data may be written to
                   ;; any user-mode address.  If CR4.SMAP = 1:
                   ;; If EFLAGS.AC = 1 and the access is
                   ;; explicit, data may be written to any
                   ;; user-mode address. If EFLAGS.AC = 0 or
                   ;; the access is implicit, data may not be
                   ;; written to any user-mode address.
                   (if (equal smap 0)
                     nil
                     (or (equal supervisor-mode-access-type 1)
                         (equal ac 0)))

                   ;; If CR4.SMAP = 0, data may be written to
                   ;; any user-mode address with a translation
                   ;; for which the R/W flag is 1 in every
                   ;; paging-structure entry controlling the
                   ;; translation.
                   (if (equal smap 0)
                     (equal (tlb-entry->r/w tlb-entry) 0)
                     ;; If CR4.SMAP = 1: If EFLAGS.AC = 1 and
                     ;; the access is explicit, data may be
                     ;; written to any user-mode address with a
                     ;; translation for which the R/W flag is 1
                     ;; in every paging-structure entry
                     ;; controlling the translation. If
                     ;; EFLAGS.AC = 0 or the access is implicit,
                     ;; data may not be written to any user-mode
                     ;; address.
                     (if (and (equal supervisor-mode-access-type 0)
                              (equal ac 1))
                       (equal (tlb-entry->r/w tlb-entry) 0)
                       t))))
               ;; In user mode (CPL = 3), data may be written
               ;; to any linear address with a valid
               ;; translation for which both the R/W flag and
               ;; the U/S flag are 1 in every paging-structure
               ;; entry controlling the translation.
               (or (equal (tlb-entry->u/s tlb-entry) 0)
                   (equal (tlb-entry->r/w tlb-entry) 0))))
        ;; Instruction fetch fault:
        (and (equal r-w-x :x)
             (if (< cpl 3)

               (if (equal (tlb-entry->u/s tlb-entry) 0)
                 ;; Instruction fetches from supervisor-mode addresses.

                 ;; If IA32_EFER.NXE = 0, instructions may be
                 ;; fetched from any supervisor-mode
                 ;; address. If IA32_EFER.NXE = 1,
                 ;; instructions may be fetched from any
                 ;; supervisor-mode address with a translation
                 ;; for which the XD flag (bit 63) is 0 in
                 ;; every paging-structure entry controlling
                 ;; the translation.
                 (if (equal nxe 0)
                   nil
                   (equal (tlb-entry->xd tlb-entry) 1))

                 ;; Instruction fetches from user-mode addresses.

                 (if (equal smep 0)
                   ;; If CR4.SMEP = 0, if IA32_EFER.NXE =
                   ;; 0, instructions may be fetched from
                   ;; any user-mode address, and if
                   ;; IA32_EFER.NXE = 1, instructions may
                   ;; be fetched from any user-mode address
                   ;; with a translation for which the XD
                   ;; flag is 0 in every paging-structure
                   ;; entry controlling the translation.
                   (if (equal nxe 0)
                     nil
                     (equal (tlb-entry->xd tlb-entry) 1))
                   ;; If CR4.SMEP = 1, instructions may not
                   ;; be fetched from any user-mode address.
                   t))

               ;; In user mode (CPL = 3): If IA32_EFER.NXE = 0,
               ;; instructions may be fetched from any linear
               ;; address with a valid translation for which
               ;; the U/S flag is 1 in every paging-structure
               ;; entry controlling the translation.  If
               ;; IA32_EFER.NXE = 1, instructions may be
               ;; fetched from any linear address with a valid
               ;; translation for which the U/S flag is 1 and
               ;; the XD flag is 0 in every paging-structure
               ;; entry controlling the translation.
               (or (equal (tlb-entry->u/s tlb-entry) 0)
                   (and (equal nxe 1)
                        (equal (tlb-entry->xd tlb-entry) 1))))))))

(define page-fault-err-no
  ((p-flag :type (unsigned-byte 1))
   (r-w-x  :type (member :r :w :x))
   (cpl    :type (unsigned-byte 2))
   (rsvd   :type (unsigned-byte 1))
   (smep   :type (unsigned-byte 1))
   (pae    :type (unsigned-byte 1))
   (nxe    :type (unsigned-byte 1)))

  :parents (ia32e-paging)

  :returns (errno natp :rule-classes :type-prescription)

  ;; From Section 4.7 (Page Fault Exceptions), Vol. 3A of the Intel
  ;; Manual:
  ;;
  ;; P flag (bit 0). This flag is 0 if there is no valid translation
  ;; for the linear address because the P flag was 0 in one of the
  ;; paging-structure entries used to translate that address.
  ;;
  ;; W/R (bit 1). If the access causing the page-fault exception was a
  ;; write, this flag is 1; otherwise, it is 0. This flag describes
  ;; the access causing the page-fault exception, not the access
  ;; rights specified by paging.
  ;;
  ;; U/S (bit 2). If a user-mode (CPL= 3) access caused the page-fault
  ;; exception, this flag is 1; it is 0 if a supervisor-mode (CPL < 3)
  ;; access did so. This flag describes the access causing the
  ;; page-fault exception, not the access rights specified by paging.
  ;;
  ;; RSVD flag (bit 3). This flag is 1 if there is no valid
  ;; translation for the linear address because a reserved bit was set
  ;; in one of the paging-structure entries used to translate that
  ;; address. (Because reserved bits are not checked in a
  ;; paging-structure entry whose P flag is 0, bit 3 of the error code
  ;; can be set only if bit 0 is also set.)
  ;;
  ;; Bits reserved in the paging-structure entries are reserved for
  ;; future functionality. Software developers should be aware that
  ;; such bits may be used in the future and that a paging-structure
  ;; entry that causes a page-fault exception on one processor might
  ;; not do so in the future.
  ;;
  ;; I/D flag (bit 4). This flag is 1 if (1) the access causing the
  ;; page-fault exception was an instruction fetch; and (2) either (a)
  ;; CR4.SMEP = 1; or (b) both (i) CR4.PAE = 1 (either PAE paging or
  ;; ia32e paging is in use); and (ii) IA32_EFER.NXE = 1. Otherwise,
  ;; the flag is 0. This flag describes the access causing the
  ;; page-fault exception, not the access rights specified by paging.

  (logior (if (equal p-flag 1)
              1 ;;  (ash 1 0)
            0)
          (if (equal r-w-x :w)
              2 ;;  (ash 1 1)
            0)
          (if (equal cpl 3)
              4 ;;  (ash 1 2)o
            0)
          (if (equal rsvd 1)
              8 ;;  (ash 1 3)
            0)
          (if (and (equal r-w-x :x)
                   (or (equal smep 1)
                       (and (equal pae 1)
                            (equal nxe 1))))
              16 ;;  (ash 1 4)
            0)))

(define translate-lin-addr
  ((lin-addr :type (signed-byte #.*max-linear-address-size*))
   (r-w-x :type (member :r :w :x))
   x86)
  :guard (not (app-view x86))
  :guard-hints (("Goal" :in-theory (enable tlb-entry->lowest-level-paging-entry-addr logtail)))
  :enabled t
  :inline t
  :prepwork
  ;; Guard was annoying to prove that the physical address for the dirty bit
  ;; update was valid. This makes quick work of it
  ((local (include-book "arithmetic-5/top" :dir :system)))

  (b* ((cpl (cpl x86))
       (cr4 (n22 (ctri *cr4* x86)))
       (smep      (cr4Bits->smep cr4))
       (cr3       (ctri *cr3* x86))
       (base-ppn  (cr3Bits->pdb cr3))
       (vpn (logtail 12 lin-addr))
       (ia32-efer (n12 (msri *ia32_efer-idx* x86)))
       (nxe       (ia32_eferBits->nxe ia32-efer))
       (tlb-entry (hons-get vpn (tlb x86)))
       (tlb-entry (if tlb-entry
                    (cdr tlb-entry)
                    nil))

       ;; What do we do if the XD bit is set in the tlb-entry but nxe is unset?
       ;; XD is supposed to be reserved if nxe is unset, in which case we
       ;; wouldn't have cached the entry. Should we fault with rsvd bit set?
       ;; The SDM seems ambiguous in this case, so I conservatively ignore the
       ;; TLB entry. Ignoring a TLB entry is *always* allowed, so this is
       ;; definitely correct.
       (tlb-entry (if (and tlb-entry
                           (eql (tlb-entry->xd tlb-entry) 1)
                           (eql nxe 0))
                    nil
                    tlb-entry))

       (cached? (and tlb-entry t))
       ((mv flg tlb-entry x86)
        (if tlb-entry
          (mv nil tlb-entry x86)
          (walk-table-pml4-table vpn base-ppn *initial-tlb-entry* x86)))
       ;; There was either a not-present page or rsvd-set error
       ((when flg) (mv t (page-fault-err-no (if (eql :not-present flg) 0 1)
                                            r-w-x
                                            cpl
                                            (if (eql :rsvd-set flg) 1 0)
                                            smep
                                            1
                                            nxe) 0 x86))
       (flg (check-access tlb-entry r-w-x x86))
       ;; Check if access is allowed
       ((when flg) (mv t (page-fault-err-no 1 ;; Entry was present
                                            r-w-x
                                            cpl
                                            0 ;; No rsvd bits set
                                            smep
                                            1
                                            nxe) 0 x86))
       ;; Access allowed; if this is a write and the dirty bit is cached
       ;; cleared, we must set the dirty bit
       ((mv cached? tlb-entry x86)
        (if (and (eql (tlb-entry->d tlb-entry) 0)
                 (eql r-w-x :x))
          (b* ((addr (ash (tlb-entry->lowest-level-paging-entry-addr tlb-entry) 3))
               (entry (rm-low-64 addr x86))
               (entry (!ia32e-page-tablesBits->d 1 entry))
               (x86 (wm-low-64 addr entry x86))
               (tlb-entry (!tlb-entry->d 1 tlb-entry)))
              (mv nil tlb-entry x86))
          (mv cached? tlb-entry x86)))

       ;; Update the tlb if necessary
       (x86 (if cached?
              x86
              (!tlb (hons-acons vpn tlb-entry (tlb x86)) x86))))
      ;; Translation succeeded
      (mv nil 0 (logapp 12 lin-addr (tlb-entry->ppn tlb-entry)) x86)))

(define ia32e-la-to-pa
  ((lin-addr :type (signed-byte #.*max-linear-address-size*))
   (r-w-x :type (member :r :w :x))
   x86)
  :guard (not (app-view x86))
  :returns (mv (flg booleanp)
               translation
               (x86 x86p :hyp (x86p x86)))
  (b* (((mv flg errno p-addr x86) (translate-lin-addr lin-addr r-w-x x86))
       ((when flg) (b* ((x86 (!fault (cons (list :page-fault errno lin-addr) (fault x86)) x86)))
                       (mv t 0 x86))))
      (mv nil p-addr x86))
  ///
  (defthm-unsigned-byte-p n52p-mv-nth-1-ia32e-la-to-pa
                          :hyp t
                          :bound *physical-address-size*
                          :concl (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))

                          :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
                          :gen-linear t
                          :gen-type t)

  (defthm xr-ia32e-la-to-pa
          (implies (and (not (equal fld :mem))
                        (not (equal fld :fault))
                        (not (equal fld :tlb)))
                   (equal (xr fld index (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86)))
                          (xr fld index x86)))
          :hints (("Goal" :in-theory (e/d* () ()))))

  (defthm xr-fault-ia32e-la-to-pa
          (implies (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
                   (equal (xr :fault index (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86)))
                          (xr :fault index x86)))
          :hints (("Goal" :in-theory (e/d* () ()))))

  (defthm ia32e-la-to-pa-xw-values
          (implies (and (not (equal fld :mem))
                        (not (equal fld :rflags))
                        (not (equal fld :fault))
                        (not (equal fld :ctr))
                        (not (equal fld :msr))
                        (not (equal fld :seg-visible))
                        (not (equal fld :app-view))
                        (not (equal fld :tlb)))
                   (and (equal (mv-nth 0
                                       (ia32e-la-to-pa lin-addr r-w-x
                                                       (xw fld index value x86)))
                               (mv-nth 0
                                       (ia32e-la-to-pa lin-addr r-w-x x86)))
                        (equal (mv-nth 1
                                       (ia32e-la-to-pa lin-addr r-w-x
                                                       (xw fld index value x86)))
                               (mv-nth 1
                                       (ia32e-la-to-pa lin-addr r-w-x x86))))))

  (defthm ia32e-la-to-pa-xw-rflags-not-ac
          (implies (equal (rflagsBits->ac value)
                          (rflagsBits->ac (rflags x86)))
                   (and (equal (mv-nth 0
                                       (ia32e-la-to-pa lin-addr r-w-x
                                                       (xw :rflags nil value x86)))
                               (mv-nth 0
                                       (ia32e-la-to-pa lin-addr r-w-x x86)))
                        (equal (mv-nth 1
                                       (ia32e-la-to-pa lin-addr r-w-x
                                                       (xw :rflags nil value x86)))
                               (mv-nth 1
                                       (ia32e-la-to-pa lin-addr r-w-x x86)))))
          :hints (("Goal" :in-theory (e/d (rflagsbits->ac rflagsbits-fix) ()))))

  (defthm ia32e-la-to-pa-xw-state
          (implies (and (not (equal fld :mem))
                        (not (equal fld :rflags))
                        (not (equal fld :fault))
                        (not (equal fld :ctr))
                        (not (equal fld :msr))
                        (not (equal fld :seg-visible))
                        (not (equal fld :app-view))
                        (not (equal fld :marking-view))
                        (not (equal fld :tlb)))
                   (equal (mv-nth 2
                                  (ia32e-la-to-pa lin-addr r-w-x
                                                  (xw fld index value x86)))
                          (xw fld index value
                              (mv-nth 2
                                      (ia32e-la-to-pa lin-addr r-w-x
                                                      x86)))))
          :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthm ia32e-la-to-pa-xw-rflags-state-not-ac
          (implies (equal (rflagsBits->ac value)
                          (rflagsBits->ac (rflags x86)))
                   (equal (mv-nth 2
                                  (ia32e-la-to-pa lin-addr r-w-x
                                                  (xw :rflags nil value x86)))
                          (xw :rflags nil value
                              (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86)))))
          :hints (("Goal" :in-theory (e/d* (rflagsBits->ac rflagsbits-fix) (force (force))))))

  (defrule 64-bit-modep-of-ia32e-la-to-pa
           (equal (64-bit-modep (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86)))
                  (64-bit-modep x86))
           :enable (64-bit-modep)
           :disable (force (force)))

  (defrule x86-operation-mode-of-ia32e-la-to-pa
           (equal (x86-operation-mode (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86)))
                  (x86-operation-mode x86))
           :enable x86-operation-mode
           :disable ia32e-la-to-pa)

  (defthm ia32e-la-to-pa-flg-same-if-virt-addr-same-page
          (implies (same-page lin-addr lin-addr-2)
                   (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86))
                          (mv-nth 0 (ia32e-la-to-pa lin-addr-2 r-w-x x86))))
          :hints (("Goal" :in-theory (disable logexting-maintains-same-page)
                   :use ((:instance logexting-maintains-same-page
                                    (x lin-addr) (y lin-addr-2) (n 48)))))
          :rule-classes :congruence)

  (defthm ia32e-la-to-pa-phys-addr-same-if-virt-addr-same-page
          (implies (same-page lin-addr lin-addr-2)
                   (same-page (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))
                              (mv-nth 1 (ia32e-la-to-pa lin-addr-2 r-w-x x86))))
          :hints (("Goal" :in-theory (e/d () (logexting-maintains-same-page))
                          :use ((:instance logexting-maintains-same-page
                                           (x lin-addr) (y lin-addr-2) (n 48)))))
          :rule-classes :congruence))

(local
 (defthm loghead-equality-monotone
   (implies (and
             ;; Here's a dumb bind-free, but hey, it works for my
             ;; purpose!  I can make a nicer rule in the future or I
             ;; can simply be lazy and add to the bind-free.
             (bind-free (list (list (cons 'n ''12))
                              (list (cons 'n ''21))
                              (list (cons 'n ''30)))
                        (n))
             (equal (loghead n x) 0)
             (natp n)
             (natp m)
             (natp x)
             (<= m n))
            (equal (loghead m x) 0))
   :hints (("Goal" :in-theory
            (e/d* (acl2::loghead** acl2::ihsext-inductions)
                  ())))))

(local
 (defthm negative-logand-to-positive-logand-n=64=for-now
   ;; TO-DO@Shilpi:
   ;; There are more general theorems called
   ;; negative-logand-to-positive-logand-with-natp-x and
   ;; negative-logand-to-positive-logand-with-integerp-x in
   ;; register-readers-and-writers.lisp.  Why don't they work
   ;; here? Which rule is interfering?
   (implies (and (equal n 64)
                 (unsigned-byte-p n x)
                 (integerp m)
                 ;; Only for negative values of m
                 (syntaxp (and (quotep m)
                               (let* ((m-abs (acl2::unquote m)))
                                 (< m-abs 0)))))
            (equal (logand m x)
                   (logand (logand (1- (expt 2 n)) m) x)))
   :hints (("Goal" :in-theory (e/d () (bitops::loghead-of-logand))))))

(defthm ia32e-la-to-pa-lower-12-bits
  (implies (and (natp n)
                (<= n 12)
                (x86p x86)
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86))))
           (equal
            (loghead n (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))
            (loghead n lin-addr)))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa)
                                  ()))))

(defthmd ia32e-la-to-pa-lower-12-bits-error
  (implies (and
            ;; Here's a dumb bind-free, but hey, it works for my
            ;; purposes!  I can make a nicer rule in the future or I
            ;; can simply be lazy and add to the bind-free.
            (bind-free (list (list (cons 'n ''12)))
                       (n))
            (natp n)
            (<= n 12)
            (not (equal (loghead n (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))
                        (loghead n lin-addr))))
           (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa)
                                  (loghead-equality-monotone
                                   acl2::loghead-identity
                                   unsigned-byte-p
                                   signed-byte-p
                                   force (force))))))

(defthmd ia32e-la-to-pa-lower-12-bits-value-of-address-when-error
  (implies (and (natp n)
                (<= n 12)
                (x86p x86)
                (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
           (equal
            (loghead n (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))
            0))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa) ()))))

(defrulel ia32e-la-to-pa-lower-12-bits-alt
  ;; This local rule helps in the proof of
  ;; ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-!=-all-ones
  ;; Note the very general LHS --- this generality is the reason why
  ;; this is a local rule.  I'll keep ia32e-la-to-pa-lower-12-bits
  ;; around for readability.
  (implies (and (bind-free (list (list (cons 'x86 'x86)))
                           (x86))
                (natp n)
                (<= n 12)
                (x86p x86)
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86))))
           (equal
            (loghead n lin-addr)
            (loghead n (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa) ()))))

(defthm ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-!=-all-ones
  ;; This rule comes in useful during the guard proof of rml16.
  (implies (and (x86p x86)
                (integerp lin-addr)
                (< (loghead 12 lin-addr) 4095)
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86))))
           (< (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))
              *mem-size-in-bytes-1*))
  :hints (("Goal" :in-theory (e/d () (ia32e-la-to-pa-lower-12-bits))))
  :rule-classes :linear)

(encapsulate

  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm logtail-and-loghead-equality
    (implies (and (equal (logtail n x) (logtail n y))
                  (equal (loghead n x) (loghead n y))
                  (natp x)
                  (natp y))
             (equal x y))
    :hints (("Goal" :in-theory (enable logtail loghead)))
    :rule-classes ((:forward-chaining
                    ;; These trigger terms are no good if the hyps of
                    ;; the theorem to be proved have something like
                    ;; (and (equal (logtail n x) 0)
                    ;;      (equal (logtail n x) 0))
                    ;; But, for my use case so far, the following terms
                    ;; do fine, though (equal (loghead n x) (loghead n
                    ;; y)) is not a good candidate since logheads
                    ;; appear separately, like:
                    ;; (and (equal (loghead n x) 0)
                    ;;      (equal (loghead n x) 0))
                    :trigger-terms ((equal (logtail n x) (logtail n y))
                                    ;; (equal (loghead n x) (loghead n y))
                                    )))))

(defthm loghead-monotonic-when-upper-bits-are-equal
  ;; See also the rule logtail-and-loghead-equality.
  (implies (and (< (loghead x a) (loghead x b))
                (equal (logtail x a) (logtail x b))
                (natp a)
                (natp b))
           (< a b))
  :hints
  (("Goal" :in-theory
    (e/d* (acl2::ihsext-inductions acl2::ihsext-recursive-redefs)
          (loghead-equality-monotone
           acl2::loghead-identity
           unsigned-byte-p**))))
  :rule-classes :forward-chaining)

(defthm logtail-and-loghead-inequality-with-low-bits-equal
  (implies (and (<= (logtail n x) (logtail n y))
                (equal (loghead n x) (loghead n y))
                (natp n)
                (natp x)
                (natp y))
           (<= x y))
  :hints (("Goal"
           :in-theory
           (e/d*
            (acl2::ihsext-inductions acl2::ihsext-recursive-redefs)
            (loghead-equality-monotone
             acl2::loghead-identity
             unsigned-byte-p**))))
  :rule-classes nil)

(defthm logtail-monotone-1
  (implies (and (natp a)
                (natp b)
                (<= a b))
           (<= (logtail x a) (logtail x b)))
  :hints
  (("Goal" :in-theory
    (e/d* (acl2::ihsext-inductions acl2::ihsext-recursive-redefs)))))

(defthm logtail-and-loghead-inequality
  ;; See also the rule logtail-and-loghead-equality, which is a
  ;; forward-chaining rule.  This is a :rule-classes nil instead.
  (implies (and (<= (logtail n x) (logtail n y))
                (< (loghead n x) (loghead n y))
                (natp n)
                (natp x)
                (natp y))
           (< x y))
  :hints (("Goal"
           :cases ((< (logtail n x) (logtail n y)))))
  :rule-classes nil)

(defthmd ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-<-4093-helper
  (implies (and (< (loghead 12 x) 4093)
                ;; (< x *mem-size-in-bytes*)
                (<= x *mem-size-in-bytes-1*)
                (natp x))
           (< x *mem-size-in-bytes-3*))
  :hints (("Goal"
           :in-theory (e/d () (logtail-monotone-1))
           :use ((:instance logtail-and-loghead-inequality
                            (n 12)
                            (x x)
                            (y *mem-size-in-bytes-3*))
                 (:instance logtail-monotone-1
                            (a x)
                            (x 12)
                            (b *mem-size-in-bytes-1*))))))

(defthm ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-<-4093
  ;; This rule comes in useful during the guard proof of rml32.
  (implies (and (x86p x86)
                (integerp lin-addr)
                (< (loghead 12 lin-addr) 4093)
                (not (mv-nth 0
                             (ia32e-la-to-pa lin-addr r-w-x x86))))
           (< (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))
              *mem-size-in-bytes-3*))
  :hints (("Goal" :in-theory (e/d () (ia32e-la-to-pa-lower-12-bits))
           :use ((:instance
                  ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-<-4093-helper
                  (x (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))))))
  :rule-classes :linear)

(defthmd ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-<-4089-helper
  (implies (and (< (loghead 12 x) 4089)
                ;; (< x *mem-size-in-bytes*)
                (<= x *mem-size-in-bytes-1*)
                (natp x))
           (< x *mem-size-in-bytes-7*))
  :hints (("Goal"
           :in-theory (e/d () (logtail-monotone-1))
           :use ((:instance logtail-and-loghead-inequality
                            (n 12)
                            (x x)
                            (y *mem-size-in-bytes-7*))
                 (:instance logtail-monotone-1
                            (a x)
                            (x 12)
                            (b *mem-size-in-bytes-1*))))))

(defthm ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-<-4089
  ;; This rule comes in useful during the guard proof of rml64.
  (implies (and (x86p x86)
                (integerp lin-addr)
                (< (loghead 12 lin-addr) 4089)
                (not (mv-nth 0
                             (ia32e-la-to-pa lin-addr r-w-x x86))))
           (< (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))
              *mem-size-in-bytes-7*))
  :hints (("Goal" :in-theory (e/d () (ia32e-la-to-pa-lower-12-bits))
           :use ((:instance
                  ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-<-4089-helper
                  (x (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))))))
  :rule-classes :linear)

(defthmd ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-=-4089-helper
  (implies (and (equal (loghead 12 x) 4089)
                ;; (< x *mem-size-in-bytes*)
                (<= x *mem-size-in-bytes-1*)
                (natp x))
           (<= x *mem-size-in-bytes-7*))
  :hints (("Goal"
           :in-theory (e/d () (logtail-monotone-1))
           :use ((:instance logtail-and-loghead-inequality-with-low-bits-equal
                            (n 12)
                            (x x)
                            (y *mem-size-in-bytes-7*))
                 (:instance logtail-monotone-1
                            (a x)
                            (x 12)
                            (b *mem-size-in-bytes-1*))))))

(defthm ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-=-4089
  ;; This rule comes in useful during the guard proof of rml64.
  (implies (and (x86p x86)
                (integerp lin-addr)
                (equal (loghead 12 lin-addr) 4089)
                (not (mv-nth 0
                             (ia32e-la-to-pa lin-addr r-w-x x86))))
           (<= (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))
               *mem-size-in-bytes-7*))
  :hints (("Goal" :in-theory (e/d () (ia32e-la-to-pa-lower-12-bits))
           :use ((:instance
                  ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-=-4089-helper
                  (x (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))))))
  :rule-classes :linear)

(defthmd ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-=-4090-helper
  (implies (and (equal (loghead 12 x) 4090)
                ;; (< x *mem-size-in-bytes*)
                (<= x *mem-size-in-bytes-1*)
                (natp x))
           (<= x *mem-size-in-bytes-6*))
  :hints (("Goal"
           :in-theory (e/d () (logtail-monotone-1))
           :use ((:instance logtail-and-loghead-inequality-with-low-bits-equal
                            (n 12)
                            (x x)
                            (y *mem-size-in-bytes-6*))
                 (:instance logtail-monotone-1
                            (a x)
                            (x 12)
                            (b *mem-size-in-bytes-1*))))))

(defthm ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-=-4090
  ;; This rule comes in useful during the guard proof of rml64.
  (implies (and (x86p x86)
                (integerp lin-addr)
                (equal (loghead 12 lin-addr) 4090)
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86))))
           (<= (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))
               *mem-size-in-bytes-6*))
  :hints (("Goal" :in-theory (e/d () (ia32e-la-to-pa-lower-12-bits))
           :use ((:instance
                  ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-=-4090-helper
                  (x (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))))))
  :rule-classes :linear)

(defthmd ia32e-la-to-pa-<-*mem-size-in-bytes-15*-when-low-12-bits-<-4081-helper
  (implies (and (< (loghead 12 x) 4081)
                ;; (< x *mem-size-in-bytes*)
                (<= x *mem-size-in-bytes-1*)
                (natp x))
           (< x *mem-size-in-bytes-15*))
  :hints (("Goal"
           :in-theory (e/d () (logtail-monotone-1))
           :use ((:instance logtail-and-loghead-inequality
                            (n 12)
                            (x x)
                            (y *mem-size-in-bytes-15*))
                 (:instance logtail-monotone-1
                            (a x)
                            (x 12)
                            (b *mem-size-in-bytes-1*))))))

(defthm ia32e-la-to-pa-<-*mem-size-in-bytes-15*-when-low-12-bits-<-4081
  ;; This rule comes in useful during the guard proof of rml128.
  (implies (and (x86p x86)
                (integerp lin-addr)
                (< (loghead 12 lin-addr) 4081)
                (not (mv-nth 0
                             (ia32e-la-to-pa lin-addr r-w-x x86))))
           (< (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))
              *mem-size-in-bytes-15*))
  :hints (("Goal" :in-theory (e/d () (ia32e-la-to-pa-lower-12-bits))
           :use ((:instance
                  ia32e-la-to-pa-<-*mem-size-in-bytes-15*-when-low-12-bits-<-4081-helper
                  (x (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))))))
  :rule-classes :linear)

(defthmd ia32e-la-to-pa-<-*mem-size-in-bytes-15*-when-low-12-bits-=-4081-helper
  (implies (and (equal (loghead 12 x) 4081)
                ;; (< x *mem-size-in-bytes*)
                (<= x *mem-size-in-bytes-1*)
                (natp x))
           (<= x *mem-size-in-bytes-15*))
  :hints (("Goal"
           :in-theory (e/d () (logtail-monotone-1))
           :use ((:instance logtail-and-loghead-inequality-with-low-bits-equal
                            (n 12)
                            (x x)
                            (y *mem-size-in-bytes-15*))
                 (:instance logtail-monotone-1
                            (a x)
                            (x 12)
                            (b *mem-size-in-bytes-1*))))))

(defthm ia32e-la-to-pa-<-*mem-size-in-bytes-15*-when-low-12-bits-=-4081
  ;; This rule comes in useful during the guard proof of rml128.
  (implies (and (x86p x86)
                (integerp lin-addr)
                (equal (loghead 12 lin-addr) 4081)
                (not (mv-nth 0
                             (ia32e-la-to-pa lin-addr r-w-x x86))))
           (<= (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86))
               *mem-size-in-bytes-15*))
  :hints (("Goal" :in-theory (e/d () (ia32e-la-to-pa-lower-12-bits))
           :use ((:instance
                  ia32e-la-to-pa-<-*mem-size-in-bytes-15*-when-low-12-bits-=-4081-helper
                  (x (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))))))
  :rule-classes :linear)

;; ======================================================================

(define la-to-pa
  ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
   (r-w-x     :type (member  :r :w :x)
              "Indicates whether this translation is on the behalf of a read, write, or instruction fetch")
   (x86 "x86 state"))

  :inline t
  :no-function t
  :enabled t

  :guard (not (app-view x86))
  :parents (ia32e-paging)

  :short "Top-level page translation function"

  (if (mbt (and (canonical-address-p lin-addr)
                (not (app-view x86))))
      (ia32e-la-to-pa lin-addr r-w-x x86)
    (mv (list :ia32e-paging-invalid-linear-address-or-not-in-sys-view
              lin-addr)
        0 x86)))

;; ======================================================================
