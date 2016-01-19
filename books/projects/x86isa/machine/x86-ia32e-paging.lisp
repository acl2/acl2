;; AUTHORS:
;; Robert Krug <rkrug@cs.utexas.edu>
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "x86-physical-memory" :ttags (:undef-flg))

;; [Shilpi]: For now, I've removed nested paging and all paging modes
;; except IA-32e paging from our model.

;; ======================================================================

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

(defsection ia32e-paging
  :parents (machine)
  :short "Specification of IA-32e Paging"
  )

(defthm loghead-zero-smaller
  (implies (and (equal (loghead n x) 0)
                (natp n)
                (<= m n))
           (equal (loghead m x) 0))
  :hints (("Goal" :in-theory (e/d*
                              (acl2::ihsext-recursive-redefs
                               acl2::ihsext-inductions)
                              ()))))

;; ======================================================================

(define good-lin-addr-p (lin-addr x86)

  :parents (ia32e-paging)

  (b* ((cr0 (the (unsigned-byte 32) (n32 (ctri *cr0* x86))))
       (cr4 (the (unsigned-byte 21) (n21 (ctri *cr4* x86))))
       ;; Remember that *ia32_efer-idx* and *ia32_efer* are
       ;; different.  The latter is the "address" of the register on
       ;; the real machine and the former is the index of the
       ;; register in the x86 stobj.
       (ia32-efer (the (unsigned-byte 12)
                    (n12 (msri *ia32_efer-idx* x86)))))

      (cond ((equal (cr0-slice :cr0-pg cr0) 0)
             ;; Paging is off
             (n32p lin-addr))
            ((equal (cr4-slice :cr4-pae cr4) 0)
             ;; 32-bit paging
             (n32p lin-addr))
            ((equal (ia32_efer-slice :ia32_efer-lme ia32-efer) 0)
             ;; PAE paging
             (n32p lin-addr))
            (t
             ;; IA32e paging
             (canonical-address-p lin-addr)))))

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

(define page-fault-exception (addr err-no x86)

  :parents (ia32e-paging)

  :returns (mv flg zero (x86 x86p :hyp :guard))

  ;; From Section 4.7 (Page Fault Exceptions), Vol. 3A of the Intel
  ;; Manual:

  ;; Page-fault exceptions occur only due to an attempt to use a linear
  ;; address. Failures to load the PDPTE registers with PAE paging (see
  ;; Section 4.4.1) cause general-protection exceptions (#GP(0)) and not
  ;; page-fault exceptions.

  (b* ((old-faults (fault x86))
       (new-faults (cons (list :page-fault err-no addr) old-faults))
       (x86 (!fault new-faults x86)))
    ;; [Shilpi]: I replaced (list :page-fault-exception err-no addr)
    ;; with t below because in the old world, the flag would differ
    ;; for every error, thereby disallowing dealing with all
    ;; page-faulting situations in one case, which slowed reasoning
    ;; down. There's no loss of information because the fault field
    ;; contains the error number and the address at which a fault
    ;; occurred.
    (mv t 0 x86))
  ///

  (defthm mv-nth-0-page-fault-exception
    (mv-nth 0 (page-fault-exception addr err-no x86)))

  (defthm mv-nth-1-page-fault-exception
    (equal (mv-nth 1 (page-fault-exception addr err-no x86))
           0))

  (defthm xr-page-fault-exception
    (implies (not (equal fld :fault))
             (equal (xr fld index (mv-nth 2 (page-fault-exception addr err-no x86)))
                    (xr fld index x86))))

  (defthm page-fault-exception-xw-values
    (implies (not (equal fld :fault))
             (and (equal (mv-nth 0 (page-fault-exception addr err-no (xw fld index value x86)))
                         (mv-nth 0 (page-fault-exception addr err-no x86)))
                  (equal (mv-nth 1 (page-fault-exception addr err-no (xw fld index value x86)))
                         0))))

  (defthm page-fault-exception-xw-state
    (implies (not (equal fld :fault))
             (equal (mv-nth 2 (page-fault-exception addr err-no (xw fld index value x86)))
                    (xw fld index value (mv-nth 2 (page-fault-exception addr err-no x86)))))))

(define page-present
  ((entry :type (unsigned-byte 64)))
  :enabled t
  :returns (bit (unsigned-byte-p 1 bit) :hyp :guard)
  (ia32e-page-tables-slice :p entry)

  ///

  (defthm-usb n01p-page-present
    :hyp (unsigned-byte-p 64 val)
    :bound 1
    :concl (page-present val)
    :gen-type t
    :gen-linear t))

(define page-size
  ((entry :type (unsigned-byte 64)))
  :enabled t
  :returns (bit (unsigned-byte-p 1 bit) :hyp :guard)
  (ia32e-page-tables-slice :ps entry)

  ///

  (defthm-usb n01p-page-size
    :hyp (unsigned-byte-p 64 val)
    :bound 1
    :concl (page-size val)
    :gen-type t
    :gen-linear t))

(define page-read-write
  ((entry :type (unsigned-byte 64)))
  :enabled t
  :returns (bit (unsigned-byte-p 1 bit) :hyp :guard)
  (ia32e-page-tables-slice :r/w entry)

  ///

  (defthm-usb n01p-page-read-write
    :hyp (unsigned-byte-p 64 val)
    :bound 1
    :concl (page-read-write val)
    :gen-type t
    :gen-linear t))

(define page-user-supervisor
  ((entry :type (unsigned-byte 64)))
  :enabled t
  :returns (bit (unsigned-byte-p 1 bit) :hyp :guard)
  (ia32e-page-tables-slice :u/s entry)

  ///

  (defthm-usb n01p-page-user-supervisor
    :hyp (unsigned-byte-p 64 val)
    :bound 1
    :concl (page-user-supervisor val)
    :gen-type t
    :gen-linear t))

(define page-execute-disable
  ((entry :type (unsigned-byte 64)))
  :enabled t
  :returns (bit (unsigned-byte-p 1 bit) :hyp :guard)
  (ia32e-page-tables-slice :xd entry)

  ///

  (defthm-usb n01p-page-execute-disable
    :hyp (unsigned-byte-p 64 val)
    :bound 1
    :concl (page-execute-disable val)
    :gen-type t
    :gen-linear t))

(define accessed-bit
  ((entry :type (unsigned-byte 64)))
  :enabled t
  :returns (bit (unsigned-byte-p 1 bit) :hyp :guard)
  (ia32e-page-tables-slice :a entry)

  ///

  (defthm-usb n01p-accessed-bit
    :hyp (unsigned-byte-p 64 val)
    :bound 1
    :concl (accessed-bit val)
    :gen-type t
    :gen-linear t))

(define dirty-bit
  ((entry :type (unsigned-byte 64)))
  :enabled t
  :returns (bit (unsigned-byte-p 1 bit) :hyp :guard)
  (ia32e-page-tables-slice :d entry)

  ///

  (defthm-usb n01p-dirty-bit
    :hyp (unsigned-byte-p 64 val)
    :bound 1
    :concl (dirty-bit val)
    :gen-type t
    :gen-linear t))

(define set-accessed-bit
  ((entry :type (unsigned-byte 64)))
  :enabled t
  :returns (a-entry (unsigned-byte-p 64 a-entry) :hyp :guard)
  (!ia32e-page-tables-slice :a 1 entry)

  ///

  (defthm-usb n64p-set-accessed-bit
    :hyp (unsigned-byte-p 64 val)
    :bound 64
    :concl (set-accessed-bit val)
    :gen-type t
    :gen-linear t))

(define set-dirty-bit
  ((entry :type (unsigned-byte 64)))
  :enabled t
  :returns (d-entry (unsigned-byte-p 64 d-entry) :hyp :guard)
  (!ia32e-page-tables-slice :d 1 entry)

  ///

  (defthm-usb n64p-set-dirty-bit
    :hyp (unsigned-byte-p 64 val)
    :bound 64
    :concl (set-dirty-bit val)
    :gen-type t
    :gen-linear t))

;; ======================================================================

;; We define inlined functions that compute the entry address for a
;; particular paging data structure, given the base address of the
;; structure and the original linear address.  We do this so that
;; during reasoning, we see these functions in checkpoints instead of
;; confusing arithmetic expressions involving logtail, loghead, etc.

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (defthm adding-7-to-shifted-bits-helper
     (implies (and (syntaxp (quotep n))
                   (natp n)
                   (equal (loghead 12 base-addr) 0)
                   (unsigned-byte-p 52 base-addr)
                   (equal (logtail 12 n) (1- (ash 1 52))))
              (equal (logand n base-addr)
                     base-addr))
     :hints (("Goal" :in-theory (e/d (logtail loghead) ())
              :use ((:instance break-logand-into-loghead-and-logtail
                               (x n)
                               (y base-addr)
                               (n 12)))))))

  (defthm adding-7-to-shifted-bits
    (implies (and (equal (loghead 12 base-addr) 0)
                  (unsigned-byte-p 52 base-addr)
                  (unsigned-byte-p 9 x))
             (<
              (+ 7
                 (logior (logand 18446744073709547527 base-addr)
                         (ash x 3)))
              *mem-size-in-bytes*))
    :hints (("Goal" :in-theory (e/d (loghead) ())))))

(encapsulate
  ()

  (local (include-book "centaur/bitops/signed-byte-p" :dir :system))

  (define page-table-entry-addr
    ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
     (base-addr :type (unsigned-byte #.*physical-address-size*)))
    :parents (ia32e-paging)

    :guard (equal (loghead 12 base-addr) 0)
    :guard-hints (("Goal" :in-theory (e/d ()
                                          (unsigned-byte-p
                                           signed-byte-p
                                           member-equal
                                           not))))
    :inline t

    (mbe :logic (part-install (part-select lin-addr :low 12 :high 20)
                              base-addr :low 3 :high 11)
         :exec (the (unsigned-byte #.*physical-address-size*)
                 (logior (logand base-addr (lognot (ash 511 3)))
                         (ash (the (unsigned-byte 9)
                                (logand 511
                                        (the (signed-byte 36)
                                          (ash lin-addr -12))))
                              3))))

    ///

    (defthm natp-page-table-entry-addr
      (implies (natp base-addr)
               (natp (page-table-entry-addr lin-addr base-addr)))
      :hints (("Goal" :in-theory (e/d* (page-table-entry-addr) nil)))
      :rule-classes (:rewrite :type-prescription))

    (defthm-usb *physical-address-size*p-page-table-entry-addr
      :hyp (and (unsigned-byte-p *physical-address-size*   base-addr)
                (signed-byte-p   *max-linear-address-size* lin-addr))
      :bound *physical-address-size*
      :concl (page-table-entry-addr lin-addr base-addr)
      :hints (("Goal" :in-theory (e/d ()
                                      (unsigned-byte-p
                                       signed-byte-p
                                       member-equal
                                       not))))
      :hints-l (("Goal" :in-theory (e/d ()
                                        (page-table-entry-addr))))
      :gen-linear t)

    (defthm page-table-entry-addr-is-a-multiple-of-8
      (implies (equal (loghead 12 base-addr) 0)
               (equal (loghead 3 (page-table-entry-addr lin-addr base-addr))
                      0)))

    (defthm-usb adding-7-to-page-table-entry-addr
      :hyp (and (unsigned-byte-p *physical-address-size*   base-addr)
                (signed-byte-p   *max-linear-address-size* lin-addr)
                (equal (loghead 12 base-addr) 0))
      :bound *physical-address-size*
      :concl (+ 7 (page-table-entry-addr lin-addr base-addr))
      :hints-l (("Goal" :in-theory (e/d ()
                                        (page-table-entry-addr))))
      :gen-linear t
      :gen-type t))

  (define page-directory-entry-addr
    ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
     (base-addr :type (unsigned-byte #.*physical-address-size*)))
    :parents (ia32e-paging)

    :guard (equal (loghead 12 base-addr) 0)
    :guard-hints (("Goal" :in-theory (e/d ()
                                          (unsigned-byte-p
                                           signed-byte-p
                                           member-equal
                                           not))))
    :inline t

    (mbe
     :logic
     (part-install (part-select lin-addr :low 21 :high 29)
                   base-addr
                   :low 3 :high 11)
     :exec
     (the (unsigned-byte #.*physical-address-size*)
       (logior (the (unsigned-byte #.*physical-address-size*)
                 (logand base-addr
                         (lognot 4088)))
               (the (unsigned-byte 12)
                 (ash
                  (the (unsigned-byte 9)
                    (logand 511
                            (ash lin-addr -21)))
                  3)))))

    ///

    (defthm natp-page-directory-entry-addr
      (implies (natp base-addr)
               (natp (page-directory-entry-addr lin-addr base-addr)))
      :hints (("Goal" :in-theory (e/d* (page-directory-entry-addr) nil)))
      :rule-classes (:rewrite :type-prescription))

    (defthm-usb *physical-address-size*p-page-directory-entry-addr
      :hyp (and (unsigned-byte-p *physical-address-size*   base-addr)
                (signed-byte-p   *max-linear-address-size* lin-addr))
      :bound *physical-address-size*
      :concl (page-directory-entry-addr lin-addr base-addr)
      :hints (("Goal" :in-theory (e/d ()
                                      (unsigned-byte-p
                                       signed-byte-p
                                       member-equal
                                       not))))
      :hints-l (("Goal" :in-theory (e/d ()
                                        (page-directory-entry-addr))))
      :gen-linear t)

    (defthm page-directory-entry-addr-is-a-multiple-of-8
      (implies (equal (loghead 12 base-addr) 0)
               (equal (loghead 3 (page-directory-entry-addr lin-addr base-addr))
                      0)))

    (defthm-usb adding-7-to-page-directory-entry-addr
      :hyp (and (unsigned-byte-p *physical-address-size*   base-addr)
                (signed-byte-p   *max-linear-address-size* lin-addr)
                (equal (loghead 12 base-addr) 0))
      :bound *physical-address-size*
      :concl (+ 7 (page-directory-entry-addr lin-addr base-addr))
      :gen-linear t
      :gen-type t
      :hints-l (("Goal" :in-theory (e/d () (page-directory-entry-addr))))))

  (define page-dir-ptr-table-entry-addr
    ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
     (base-addr :type (unsigned-byte #.*physical-address-size*)))
    :parents (ia32e-paging)

    :guard (equal (loghead 12 base-addr) 0)
    :guard-hints (("Goal" :in-theory (e/d ()
                                          (unsigned-byte-p
                                           signed-byte-p
                                           member-equal
                                           not))))
    :inline t

    (mbe
     :logic
     (part-install (part-select lin-addr :low 30 :high 38)
                   base-addr :low 3 :high 11)
     :exec
     (the (unsigned-byte #.*physical-address-size*)
       (logior (the (unsigned-byte #.*physical-address-size*)
                 (logand base-addr (lognot (ash 511 3))))
               (the (unsigned-byte 12)
                 (ash (the (unsigned-byte 9)
                        (logand 511 (ash lin-addr -30)))
                      3)))))

    ///

    (defthm natp-page-dir-ptr-table-entry-addr
      (implies (natp base-addr)
               (natp (page-dir-ptr-table-entry-addr lin-addr base-addr)))
      :hints (("Goal" :in-theory (e/d* (page-dir-ptr-table-entry-addr) nil)))
      :rule-classes (:rewrite :type-prescription))

    (defthm-usb *physical-address-size*p-page-dir-ptr-table-entry-addr
      :hyp (and (unsigned-byte-p *physical-address-size*   base-addr)
                (signed-byte-p   *max-linear-address-size* lin-addr))
      :bound *physical-address-size*
      :concl (page-dir-ptr-table-entry-addr lin-addr base-addr)
      :hints (("Goal" :in-theory (e/d ()
                                      (unsigned-byte-p
                                       signed-byte-p
                                       member-equal
                                       not))))
      :hints-l (("Goal" :in-theory (e/d ()
                                        (page-dir-ptr-table-entry-addr))))
      :gen-linear t)

    (defthm page-dir-ptr-table-entry-addr-is-a-multiple-of-8
      (implies (equal (loghead 12 base-addr) 0)
               (equal (loghead 3 (page-dir-ptr-table-entry-addr lin-addr base-addr))
                      0)))

    (defthm-usb adding-7-to-page-dir-ptr-table-entry-addr
      :hyp (and (unsigned-byte-p *physical-address-size*   base-addr)
                (signed-byte-p   *max-linear-address-size* lin-addr)
                (equal (loghead 12 base-addr) 0))
      :bound *physical-address-size*
      :concl (+ 7 (page-dir-ptr-table-entry-addr lin-addr base-addr))
      :hints-l (("Goal" :in-theory (e/d ()
                                        (page-dir-ptr-table-entry-addr))))
      :gen-linear t
      :gen-type t))

  (define pml4-table-entry-addr
    ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
     (base-addr :type (unsigned-byte #.*physical-address-size*)))
    :parents (ia32e-paging)

    :guard (equal (loghead 12 base-addr) 0)
    :guard-hints (("Goal" :in-theory (e/d ()
                                          (unsigned-byte-p
                                           signed-byte-p
                                           member-equal
                                           not))))
    :inline t

    (mbe
     :logic
     (part-install
      (part-select lin-addr :low 39 :high 47)
      base-addr :low 3 :high 11)
     :exec
     (the
         (unsigned-byte #.*physical-address-size*)
       (logior
        (the (unsigned-byte #.*physical-address-size*)
          (logand base-addr (lognot (ash 511 3))))
        (the (unsigned-byte 12)
          (ash (the (unsigned-byte 9)
                 (logand 511 (ash lin-addr -39))) 3)))))

    ///

    (defthm natp-pml4-table-entry-addr
      (implies (natp base-addr)
               (natp (pml4-table-entry-addr lin-addr base-addr)))
      :hints (("Goal" :in-theory (e/d* (pml4-table-entry-addr) nil)))
      :rule-classes (:rewrite :type-prescription))

    (defthm-usb *physical-address-size*p-pml4-table-entry-addr
      :hyp (and (unsigned-byte-p *physical-address-size*   base-addr)
                (signed-byte-p   *max-linear-address-size* lin-addr))
      :bound *physical-address-size*
      :concl (pml4-table-entry-addr lin-addr base-addr)
      :hints (("Goal" :in-theory (e/d ()
                                      (unsigned-byte-p
                                       signed-byte-p
                                       member-equal
                                       not))))
      :hints-l (("Goal" :in-theory (e/d ()
                                        (pml4-table-entry-addr))))
      :gen-linear t)

    (defthm pml4-table-entry-addr-is-a-multiple-of-8
      (implies (equal (loghead 12 base-addr) 0)
               (equal (loghead 3 (pml4-table-entry-addr lin-addr base-addr))
                      0)))

    (defthm-usb adding-7-to-pml4-table-entry-addr
      :hyp (and (unsigned-byte-p *physical-address-size*   base-addr)
                (signed-byte-p   *max-linear-address-size* lin-addr)
                (equal (loghead 12 base-addr) 0))
      :bound *physical-address-size*
      :concl (+ 7 (pml4-table-entry-addr lin-addr base-addr))
      :gen-linear t
      :gen-type t
      :hints-l (("Goal" :in-theory (e/d ()
                                        (pml4-table-entry-addr)))))))

(in-theory (e/d () (adding-7-to-shifted-bits)))

;; ======================================================================

(local
 (defthm loghead-and-logsquash
   (implies (and (equal (loghead n x) 0)
                 (unsigned-byte-p m x))
            (equal (bitops::logsquash n x) x))
   :hints (("Goal"
            :in-theory (e/d* (bitops::ihsext-recursive-redefs
                              bitops::ihsext-inductions)
                             ())))))

(define page-table-entry-no-page-fault-p
  ((lin-addr :type (signed-byte   #.*max-linear-address-size*))
   (entry    :type (unsigned-byte 64))
   (u-s-acc   :type (unsigned-byte  1))
   (wp        :type (unsigned-byte  1))
   (smep      :type (unsigned-byte  1))
   (nxe       :type (unsigned-byte  1))
   (r-w-x     :type (member  :r :w :x))
   (cpl       :type (unsigned-byte  2))
   x86)
  :inline t
  :returns (mv flg val (x86 x86p :hyp (x86p x86)))
  :guard (not (programmer-level-mode x86))

  (b* ((entry (mbe :logic (loghead 64 entry)
                   :exec entry))
       (page-present (mbe :logic (page-present entry)
                          :exec (ia32e-page-tables-slice :p entry)))
       ((when (equal page-present 0))
        ;; Page not present fault:
        (let ((err-no (page-fault-err-no
                       page-present r-w-x cpl
                       0      ;; rsvd
                       smep 1 ;; pae
                       nxe)))
          (page-fault-exception lin-addr err-no x86)))

       ;; We now extract the rest of the relevant bit fields from the
       ;; entry.  Note that we ignore fields related to the cache or
       ;; TLB, since we aren't modeling caches yet.
       (read-write      (mbe :logic (page-read-write entry)
                             :exec (ia32e-page-tables-slice :r/w entry)))
       (user-supervisor (mbe :logic (page-user-supervisor entry)
                             :exec (ia32e-page-tables-slice :u/s entry)))
       (execute-disable (mbe :logic (page-execute-disable entry)
                             :exec (ia32e-page-tables-slice :xd  entry)))

       (rsvd
        (mbe
         :logic
         (if (or
              ;; [Shilpi]: In our specification, the physical
              ;; address size is 52.  Thus, there are no reserved
              ;; bits between the physical address of the 4K page
              ;; and the XD bit in the entry.  However, we will
              ;; disagree a bit with the specs, such as they are,
              ;; in the Intel manuals, by checking the "ignored"
              ;; part of the entry from but 52 to 62.
              (not (equal
                    (part-select entry :low
                                 *physical-address-size* :high 62)
                    0))
              (and (equal nxe 0)
                   (not (equal execute-disable 0))))
             1 0)
         :exec
         (if (or
              (not (equal (logand (+ -1 (ash 1 (+ 63 (- #.*physical-address-size*))))
                                  (the (unsigned-byte 28)
                                    (ash entry (- #.*physical-address-size*))))
                          0))
              (and (equal nxe 0)
                   (not (equal
                         (the (unsigned-byte 1)
                           (logand 1
                                   (the (unsigned-byte 1)
                                     (ash entry (- 63)))))
                         0))))
             1 0)))
       ((when (equal rsvd 1))
        ;; Reserved bits fault:
        (let ((err-no (page-fault-err-no page-present
                                         r-w-x
                                         cpl
                                         rsvd
                                         smep
                                         1 ;; pae
                                         nxe)))
          (page-fault-exception lin-addr err-no x86)))

       ((when (or
               ;; Read fault:
               (and (equal r-w-x :r)
                    (if (< cpl 3)
                        ;; In supervisor mode (CPL < 3), data may be
                        ;; read from any linear address with a valid
                        ;; translation.
                        nil
                      ;; In user mode (CPL = 3), Data may be read from
                      ;; any linear address with a valid translation
                      ;; for which the U/S flag (bit 2) is 1 in every
                      ;; paging-structure entry controlling the trans-
                      ;; lation.
                      (equal user-supervisor 0)))
               ;; Write fault
               (and (equal r-w-x :w)
                    (if (< cpl 3)
                        ;; In supervisor mode (CPL < 3): If CR0.WP =
                        ;; 0, data may be written to any linear
                        ;; address with a valid translation.  If
                        ;; CR0.WP = 1, data may be written to any
                        ;; linear address with a valid translation for
                        ;; which the R/W flag (bit 1) is 1 in every
                        ;; paging-structure entry controlling the
                        ;; translation.
                        (and (equal wp 1)
                             (equal read-write 0))
                      ;; In user mode (CPL = 3), Data may be written
                      ;; to any linear address with a valid
                      ;; translation for which both the R/W flag and
                      ;; the U/S flag are 1 in every paging-structure
                      ;; entry controlling the translation.
                      (or (equal user-supervisor 0)
                          (equal read-write 0))))
               ;; Instruction fetch fault:
               (and (equal r-w-x :x)
                    (if (< cpl 3)
                        ;; In supervisor mode (CPL < 3):
                        ;;
                        ;; 1) If IA32_EFER.NXE = 0:  If CR0.WP = 0, data
                        ;; may be written to any linear address with a
                        ;; valid translation.  If CR0.WP = 1, data may
                        ;; be written to any linear address with a
                        ;; valid translation for which the R/W flag
                        ;; (bit 1) is 1 in every paging-structure entry
                        ;; controlling the translation.
                        ;;
                        ;; 2) If IA32_EFER.NXE = 1: If CR4.SMEP = 0,
                        ;; instructions may be fetched from any linear
                        ;; address with a valid translation for which
                        ;; the XD flag (bit 63) is 0 in every
                        ;; paging-structure entry controlling the
                        ;; translation.  If CR4.SMEP = 1, instructions
                        ;; may be fetched from any linear address with
                        ;; a valid translation for which (1) the U/S
                        ;; flag is 0 in at least one of the
                        ;; paging-structure entries controlling the
                        ;; translation; and (2) the XD flag is 0 in
                        ;; every paging-structure entry controlling
                        ;; the translation.
                        (if (equal nxe 0)
                            (and (equal smep 1)
                                 (equal u-s-acc 1)
                                 (equal user-supervisor 1))
                          (if (equal smep 0)
                              (equal execute-disable 1)
                            (or (equal execute-disable 1)
                                (and (equal u-s-acc 1)
                                     (equal user-supervisor 1)))))
                      ;; In user mode (CPL = 3): If IA32_EFER.NXE = 0,
                      ;; instructions may be fetched from any linear
                      ;; address with a valid translation for which the
                      ;; U/S flag is 1 in every paging-structure entry
                      ;; controlling the translation.  If IA32_EFER.NXE
                      ;; = 1, instructions may be fetched from any
                      ;; linear address with a valid translation for
                      ;; which the U/S flag is 1 and the XD flag is 0
                      ;; in every paging-structure entry controlling
                      ;; the translation.
                      (or (equal user-supervisor 0)
                          (and (equal nxe 1)
                               (equal execute-disable 1)))))))
        (let ((err-no (page-fault-err-no page-present
                                         r-w-x
                                         cpl
                                         rsvd
                                         smep
                                         1 ;; pae
                                         nxe)))
          (page-fault-exception lin-addr err-no x86))))
    (mv nil 0 x86))

  ///

  (local (in-theory (e/d (page-fault-exception) ())))

  (defthm mv-nth-1-page-table-entry-no-page-fault-p-value
    (equal (mv-nth 1
                   (page-table-entry-no-page-fault-p
                    lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86))
           0))

  (defthm xr-page-table-entry-no-page-fault-p
    (implies (not (equal fld :fault))
             (equal (xr fld index
                        (mv-nth 2
                                (page-table-entry-no-page-fault-p
                                 lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86)))
                    (xr fld index x86))))

  (defthm page-table-entry-no-page-fault-p-xw-values
    (implies (not (equal fld :fault))
             (and (equal (mv-nth 0
                                 (page-table-entry-no-page-fault-p
                                  lin-addr entry u-s-acc wp smep nxe r-w-x cpl
                                  (xw fld index value x86)))
                         (mv-nth 0
                                 (page-table-entry-no-page-fault-p
                                  lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86)))
                  (equal (mv-nth 1
                                 (page-table-entry-no-page-fault-p
                                  lin-addr entry u-s-acc wp smep nxe r-w-x cpl
                                  (xw fld index value x86)))
                         (mv-nth 1
                                 (page-table-entry-no-page-fault-p
                                  lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86))))))

  (defthm page-table-entry-no-page-fault-p-xw-state
    (implies (not (equal fld :fault))
             (equal (mv-nth 2
                            (page-table-entry-no-page-fault-p
                             lin-addr entry u-s-acc wp smep nxe r-w-x cpl
                             (xw fld index value x86)))
                    (xw fld index value
                        (mv-nth 2
                                (page-table-entry-no-page-fault-p
                                 lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86)))))))

(define ia32e-la-to-pa-page-table
  ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
   (base-addr :type (unsigned-byte #.*physical-address-size*))
   (u-s-acc   :type (unsigned-byte  1))
   (wp        :type (unsigned-byte  1))
   (smep      :type (unsigned-byte  1))
   (nxe       :type (unsigned-byte  1))
   (r-w-x     :type (member  :r :w :x))
   (cpl       :type (unsigned-byte  2))
   (x86))

  :parents (ia32e-paging)

  :guard (and (not (programmer-level-mode x86))
              (canonical-address-p lin-addr)
              ;; 4K-aligned --- the base address is
              ;; the 40 bits wide address obtained
              ;; from the referencing PDE, shifted
              ;; left by 12.
              (equal (loghead 12 base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d ()
                                        (unsigned-byte-p
                                         signed-byte-p
                                         member-equal
                                         not))))

  ;; Reference: Vol. 3A, Section 4.5 (Pg. 4-22) of the Feb'14 Intel
  ;; Manual.

  (if (mbt (not (programmer-level-mode x86)))

      (b* (
           ;; Fix the inputs of this function without incurring execution
           ;; overhead.
           (lin-addr (mbe :logic (logext 48 (loghead 48 lin-addr))
                          :exec lin-addr))
           (base-addr (mbe :logic (part-install
                                   0
                                   (loghead *physical-address-size* base-addr)
                                   :low 0 :width 12)
                           :exec base-addr))

           ;; First, we get the PTE (page table entry) address. A PTE is
           ;; selected using the physical address defined as follows:
           ;;     Bits 51:12 are from the PDE (base-addr here).
           ;;     Bits 11:3 are bits 20:12 of the linear address.
           ;;     Bits 2:0 are all 0.

           (p-entry-addr
            (the (unsigned-byte #.*physical-address-size*)
              (page-table-entry-addr lin-addr base-addr)))

           ;;  [Shilpi]: Removed nested paging specification at this
           ;;  point.

           ;; Now we can read the PTE.
           (entry (the (unsigned-byte 64) (rm-low-64 p-entry-addr x86)))

           ((mv fault-flg val x86)
            (page-table-entry-no-page-fault-p
             lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86))
           ((when fault-flg)
            (mv 'Page-Fault val x86))

           ;; No errors, so we proceed with the address translation.

           ;; Get accessed and dirty bits:
           (accessed        (mbe :logic (accessed-bit entry)
                                 :exec (ia32e-page-tables-slice :a entry)))
           (dirty           (mbe :logic (dirty-bit entry)
                                 :exec (ia32e-page-tables-slice :d entry)))
           ;; Compute accessed and dirty bits:
           (entry (if (equal accessed 0)
                      (mbe :logic (set-accessed-bit entry)
                           :exec (!ia32e-page-tables-slice :a 1 entry))
                    entry))
           (entry (if (and (equal dirty 0)
                           (equal r-w-x :w))
                      (mbe :logic (set-dirty-bit entry)
                           :exec (!ia32e-page-tables-slice :d 1 entry))
                    entry))
           ;; Update x86 (to reflect accessed and dirty bits change), if needed:
           (x86 (if (or (equal accessed 0)
                        (and (equal dirty 0)
                             (equal r-w-x :w)))
                    (wm-low-64 p-entry-addr entry x86)
                  x86)))

        ;; Return physical address and the modified x86 state.  Note that the
        ;; base address of the 4K frame would be just (ash
        ;; (ia32e-pte-4K-page-slice :pte-page entry) 12).
        (mv nil

            (mbe

             :logic
             (part-install
              (part-select lin-addr :low 0 :high 11)
              (ash (ia32e-pte-4K-page-slice :pte-page entry) 12)
              :low 0 :high 11)

             :exec
             (the (unsigned-byte #.*physical-address-size*)
               (logior
                (the (unsigned-byte #.*physical-address-size*)
                  (logand
                   (the (unsigned-byte #.*physical-address-size*)
                     (ash
                      (the (unsigned-byte 40)
                        (logand (the (unsigned-byte 40) 1099511627775)
                                (the (unsigned-byte 52)
                                  (ash (the (unsigned-byte 64) entry)
                                       (- 12)))))
                      12))
                   -4096))
                (the (unsigned-byte 12)
                  (logand 4095 lin-addr)))))
            x86))

    (mv t 0 x86))


  ///

  (defthm-usb n52p-mv-nth-1-ia32e-la-to-pa-page-table
    :hyp t
    :bound *physical-address-size*
    :concl (mv-nth 1
                   (ia32e-la-to-pa-page-table
                    lin-addr base-addr u-s-acc wp smep nxe r-w-x cpl
                    x86))

    :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
    :gen-linear t
    :hints-l (("Goal" :in-theory (e/d (unsigned-byte-p) ())))
    :gen-type t)

  (defthm x86p-mv-nth-2-ia32e-la-to-pa-page-table
    (implies (x86p x86)
             (x86p
              (mv-nth 2
                      (ia32e-la-to-pa-page-table
                       lin-addr base-addr u-s-acc wp smep nxe r-w-x cpl
                       x86)))))

  (defthm xr-ia32e-la-to-pa-page-table
    (implies (and (not (equal fld :mem))
                  (not (equal fld :fault)))
             (equal (xr fld index
                        (mv-nth 2
                                (ia32e-la-to-pa-page-table
                                 lin-addr base-addr u-s-acc wp smep nxe r-w-x cpl
                                 x86)))
                    (xr fld index x86))))

  (defthm ia32e-la-to-pa-page-table-xw-values
    (implies (and (not (equal fld :mem))
                  (not (equal fld :fault))
                  (not (equal fld :programmer-level-mode)))
             (and (equal (mv-nth 0
                                 (ia32e-la-to-pa-page-table
                                  lin-addr base-addr u-s-acc wp smep nxe r-w-x cpl
                                  (xw fld index value x86)))
                         (mv-nth 0
                                 (ia32e-la-to-pa-page-table
                                  lin-addr base-addr u-s-acc wp smep nxe r-w-x cpl
                                  x86)))
                  (equal (mv-nth 1
                                 (ia32e-la-to-pa-page-table
                                  lin-addr base-addr u-s-acc wp smep nxe r-w-x cpl
                                  (xw fld index value x86)))
                         (mv-nth 1
                                 (ia32e-la-to-pa-page-table
                                  lin-addr base-addr u-s-acc wp smep nxe r-w-x cpl
                                  x86))))))

  (defthm ia32e-la-to-pa-page-table-xw-state
    (implies (and (not (equal fld :mem))
                  (not (equal fld :fault))
                  (not (equal fld :programmer-level-mode)))
             (equal (mv-nth 2
                            (ia32e-la-to-pa-page-table
                             lin-addr base-addr u-s-acc wp smep nxe r-w-x cpl
                             (xw fld index value x86)))
                    (xw fld index value
                        (mv-nth 2
                                (ia32e-la-to-pa-page-table
                                 lin-addr base-addr u-s-acc wp smep nxe r-w-x cpl
                                 x86)))))))

;; ----------------------------------------------------------------------

(define paging-entry-no-page-fault-p
  ((lin-addr :type (signed-byte   #.*max-linear-address-size*))
   (entry    :type (unsigned-byte 64))
   (wp        :type (unsigned-byte  1))
   (smep      :type (unsigned-byte  1))
   (nxe       :type (unsigned-byte  1))
   (r-w-x     :type (member  :r :w :x))
   (cpl       :type (unsigned-byte  2))
   x86)
  :inline t
  :guard (not (programmer-level-mode x86))
  :returns (mv flg val (x86 x86p :hyp (x86p x86)))

  (b* ((entry (mbe :logic (loghead 64 entry)
                   :exec entry))
       (page-present (mbe :logic (page-present entry)
                          :exec (ia32e-page-tables-slice :p entry)))
       ((when (equal page-present 0))
        ;; Page not present fault:
        (let ((err-no (page-fault-err-no
                       page-present r-w-x cpl
                       0      ;; rsvd
                       smep 1 ;; pae
                       nxe)))
          (page-fault-exception lin-addr err-no x86)))

       ;; We now extract the rest of the relevant bit fields from the
       ;; entry.  Note that we ignore those fields having to do with
       ;; the cache or TLB, since we are not modeling caches yet.
       (read-write      (mbe :logic (page-read-write entry)
                             :exec (ia32e-page-tables-slice :r/w entry)))
       (user-supervisor (mbe :logic (page-user-supervisor entry)
                             :exec (ia32e-page-tables-slice :u/s entry)))
       (execute-disable (mbe :logic (page-execute-disable entry)
                             :exec (ia32e-page-tables-slice :xd  entry)))

       (page-size       (mbe :logic (page-size entry)
                             :exec (ia32e-page-tables-slice :ps  entry)))

       (rsvd
        ;; At this point, we know that the page is present.
        (mbe :logic  (if (or (and (equal page-size 1)
                                  (not (equal (part-select entry :low 13 :high 20) 0)))
                             (not (equal (part-select entry
                                                      :low *physical-address-size*
                                                      :high 62)
                                         0))
                             (and (equal nxe 0)
                                  (not (equal execute-disable 0))))
                         1
                       0)
             :exec  (if (or (and (equal page-size 1)
                                 (not (equal (the (unsigned-byte 8)
                                               (logand 255
                                                       (the (unsigned-byte 51)
                                                         (ash entry (- 13)))))
                                             0)))
                            (not (equal
                                  (the
                                      (unsigned-byte 12)
                                    (logand (the (unsigned-byte 11)
                                              (1- (the (unsigned-byte 12)
                                                    (ash 1 (- 63
                                                              #.*physical-address-size*)))))
                                            (the (unsigned-byte 12)
                                              (ash entry (- #.*physical-address-size*)))))
                                  0))
                            (and (equal nxe 0)
                                 (not (equal (ia32e-page-tables-slice :xd entry) 0))))
                        1
                      0)))
       ((when (equal rsvd 1))
        ;; Reserved bits fault.
        (let ((err-no (page-fault-err-no
                       page-present r-w-x cpl rsvd smep
                       1 ;; pae
                       nxe)))
          (page-fault-exception lin-addr err-no x86)))

       ((when (or
               ;; Read fault:
               (and (equal r-w-x :r)
                    (if (< cpl 3)
                        ;; In supervisor mode (CPL < 3), data may be
                        ;; read from any linear address with a valid
                        ;; translation.
                        nil
                      ;; In user mode (CPL = 3), data may be read from
                      ;; any linear address with a valid translation
                      ;; for which the U/S flag (bit 2) is 1 in every
                      ;; paging-structure entry controlling the trans-
                      ;; lation.
                      (equal user-supervisor 0)))
               ;; Write fault:
               (and (equal r-w-x :w)
                    (if (< cpl 3)
                        ;; In supervisor mode (CPL < 3): If CR0.WP =
                        ;; 0, data may be written to any linear
                        ;; address with a valid translation.  If
                        ;; CR0.WP = 1, data may be written to any
                        ;; linear address with a valid translation for
                        ;; which the R/W flag (bit 1) is 1 in every
                        ;; paging-structure entry controlling the
                        ;; translation.
                        (and (equal wp 1)
                             (equal read-write 0))
                      ;; In user mode (CPL = 3), Data may be written
                      ;; to any linear address with a valid
                      ;; translation for which both the R/W flag and
                      ;; the U/S flag are 1 in every paging-structure
                      ;; entry controlling the translation.
                      (or (equal user-supervisor 0)
                          (equal read-write 0))))
               ;; Instruction fetch fault:
               (and (equal r-w-x :x)
                    (if (< cpl 3)
                        ;; In supervisor mode (CPL < 3):
                        ;;
                        ;; 1) If IA32_EFER.NXE = 0: If CR0.WP = 0,
                        ;; data may be written to any linear address
                        ;; with a valid translation.  If CR0.WP = 1,
                        ;; data may be written to any linear address
                        ;; with a valid translation for which the R/W
                        ;; flag (bit 1) is 1 in every paging-structure
                        ;; entry controlling the translation.
                        ;;
                        ;; 2) If IA32_EFER.NXE = 1: If CR4.SMEP = 0,
                        ;; instructions may be fetched from any linear
                        ;; address with a valid translation for which
                        ;; the XD flag (bit 63) is 0 in every
                        ;; paging-structure entry controlling the
                        ;; translation.  If CR4.SMEP = 1, instructions
                        ;; may be fetched from any linear address with
                        ;; a valid translation for which (1) the U/S
                        ;; flag is 0 in at least one of the
                        ;; paging-structure entries controlling the
                        ;; translation; and (2) the XD flag is 0 in
                        ;; every paging-structure entry controlling
                        ;; the translation.
                        (and (equal nxe 1)
                             (equal execute-disable 1))
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
                      (or (equal user-supervisor 0)
                          (and (equal nxe 1)
                               (equal execute-disable 1)))))))
        (let ((err-no (page-fault-err-no
                       page-present r-w-x cpl rsvd smep
                       1 ; pae
                       nxe)))
          (page-fault-exception lin-addr err-no x86))))
    (mv nil 0 x86))

  ///

  (local (in-theory (e/d (page-fault-exception) ())))

  (defthm mv-nth-1-paging-entry-no-page-fault-p-value
    (equal (mv-nth 1
                   (paging-entry-no-page-fault-p
                    lin-addr entry wp smep nxe r-w-x cpl x86))
           0))

  (defthm xr-paging-entry-no-page-fault-p
    (implies (not (equal fld :fault))
             (equal (xr fld index
                        (mv-nth 2
                                (paging-entry-no-page-fault-p
                                 lin-addr entry wp smep nxe r-w-x cpl x86)))
                    (xr fld index x86))))

  (defthm paging-entry-no-page-fault-p-xw-values
    (implies (not (equal fld :fault))
             (and (equal (mv-nth 0
                                 (paging-entry-no-page-fault-p
                                  lin-addr entry wp smep nxe r-w-x cpl
                                  (xw fld index value x86)))
                         (mv-nth 0
                                 (paging-entry-no-page-fault-p
                                  lin-addr entry wp smep nxe r-w-x cpl x86)))
                  (equal (mv-nth 1
                                 (paging-entry-no-page-fault-p
                                  lin-addr entry wp smep nxe r-w-x cpl
                                  (xw fld index value x86)))
                         (mv-nth 1
                                 (paging-entry-no-page-fault-p
                                  lin-addr entry wp smep nxe r-w-x cpl x86))))))

  (defthm paging-entry-no-page-fault-p-xw-state
    (implies (not (equal fld :fault))
             (equal (mv-nth 2
                            (paging-entry-no-page-fault-p
                             lin-addr entry wp smep nxe r-w-x cpl
                             (xw fld index value x86)))
                    (xw fld index value
                        (mv-nth 2
                                (paging-entry-no-page-fault-p
                                 lin-addr entry wp smep nxe r-w-x cpl x86)))))))


(define ia32e-la-to-pa-page-directory
  ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
   (base-addr :type (unsigned-byte #.*physical-address-size*))
   (wp        :type (unsigned-byte  1))
   (smep      :type (unsigned-byte  1))
   (nxe       :type (unsigned-byte  1))
   (r-w-x     :type (member  :r :w :x))
   (cpl       :type (unsigned-byte  2))
   (x86))

  :parents (ia32e-paging)

  :guard (and (not (programmer-level-mode x86))
              (canonical-address-p lin-addr)
              ;; 4K-aligned --- the base address is
              ;; the 40 bits wide address obtained
              ;; from the referencing PDE, shifted
              ;; left by 12.
              (equal (loghead 12 base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d ()
                                        (unsigned-byte-p
                                         signed-byte-p
                                         member-equal
                                         not))))

  ;; Reference: Vol. 3A, Section 4.5 (Pg. 4-22) of the Feb'14 Intel
  ;; Manual.

  (if (mbt (not (programmer-level-mode x86)))

      (b* (
           ;; Fix the inputs of this function without incurring execution
           ;; overhead.
           (lin-addr (mbe :logic (logext 48 (loghead 48 lin-addr))
                          :exec lin-addr))
           (base-addr (mbe :logic (part-install
                                   0
                                   (loghead *physical-address-size* base-addr)
                                   :low 0 :width 12)
                           :exec base-addr))
           ;; First, we get the PDE (page directory entry) address. A PDE
           ;; is selected using the physical address defined as follows:
           ;;     Bits 51:12 are from the PDPTE (base-addr here).
           ;;     Bits 11:3 are bits 29:21 of the linear address.
           ;;     Bits 2:0 are all 0.

           (p-entry-addr
            (the (unsigned-byte #.*physical-address-size*)
              (page-directory-entry-addr lin-addr base-addr)))

           ;;  [Shilpi]: Removed nested paging specification at this
           ;;  point.

           ;; Now we can read the PTE.
           (entry (the (unsigned-byte 64) (rm-low-64 p-entry-addr x86)))

           ((mv fault-flg val x86)
            (paging-entry-no-page-fault-p lin-addr entry wp smep nxe r-w-x cpl x86))
           ((when fault-flg)
            (mv 'Page-Fault val x86)))

        ;; No errors at this level, so we proceed with the translation:

        (if (mbe :logic (equal (page-size entry) 1)
                 :exec (equal (ia32e-page-tables-slice :ps entry) 1))
            ;; 2MB page
            (b* (
                 ;; Get accessed and dirty bits:
                 (accessed        (mbe :logic (accessed-bit entry)
                                       :exec (ia32e-pde-2MB-page-slice :pde-a entry)))
                 (dirty           (mbe :logic (dirty-bit entry)
                                       :exec (ia32e-pde-2MB-page-slice :pde-d entry)))

                 ;; Compute accessed and dirty bits:
                 (entry (if (equal accessed 0)
                            (mbe :logic (set-accessed-bit entry)
                                 :exec (!ia32e-pde-2MB-page-slice :pde-a 1 entry))
                          entry))
                 (entry (if (and (equal dirty 0)
                                 (equal r-w-x :w))
                            (mbe :logic (set-dirty-bit entry)
                                 :exec (!ia32e-pde-2MB-page-slice :pde-d 1 entry))
                          entry))
                 ;; Update x86 (to reflect accessed and dirty bits change), if needed:
                 (x86 (if (or (equal accessed 0)
                              (and (equal dirty 0)
                                   (equal r-w-x :w)))
                          (wm-low-64 p-entry-addr entry x86)
                        x86)))
              ;; Return address of 2MB page frame and the modified x86 state.
              (mv nil
                  (mbe
                   :logic
                   (part-install
                    (part-select lin-addr :low 0 :high 20)
                    (ash (ia32e-pde-2MB-page-slice :pde-page entry) 21)
                    :low 0 :high 20)
                   :exec
                   (the
                       (unsigned-byte 52)
                     (logior
                      (the
                          (unsigned-byte 52)
                        (logand (the
                                    (unsigned-byte 52)
                                  (ash (the (unsigned-byte 31)
                                         (ia32e-pde-2mb-page-slice :pde-page entry))
                                       21))
                                (lognot (1- (ash 1 21)))))
                      (the
                          (unsigned-byte 21)
                        (logand (1- (ash 1 21)) lin-addr)))))
                  x86))
          ;; Go to the next level of page table structure (PT, which
          ;; references a 4KB page)
          (b* ((page-table-base-addr
                (ash (ia32e-pde-pg-table-slice :pde-pt entry) 12))
               ((mv flag
                    (the (unsigned-byte #.*physical-address-size*) p-addr)
                    x86)
                (ia32e-la-to-pa-page-table
                 lin-addr page-table-base-addr
                 (mbe :logic (page-user-supervisor entry)
                      :exec (ia32e-page-tables-slice :u/s entry))
                 wp smep nxe r-w-x cpl x86))

               ((when flag)
                ;; Error, so do not update accessed bit.
                (mv flag 0 x86))

               ;; Get accessed bit.  Dirty bit is ignored when PDE
               ;; references the PT.
               (accessed        (mbe :logic (accessed-bit entry)
                                     :exec (ia32e-page-tables-slice :a entry)))
               ;; Update accessed bit, if needed.
               (entry (if (equal accessed 0)
                          (mbe :logic (set-accessed-bit entry)
                               :exec (!ia32e-page-tables-slice :a 1 entry))
                        entry))
               ;; Update x86, if needed.
               (x86 (if (equal accessed 0)
                        (wm-low-64 p-entry-addr entry x86)
                      x86)))
            (mv nil p-addr x86))))

    (mv t 0 x86))

  ///

  (defthm-usb n52p-mv-nth-1-ia32e-la-to-pa-page-directory
    :hyp t
    :bound *physical-address-size*
    :concl (mv-nth 1
                   (ia32e-la-to-pa-page-directory
                    lin-addr base-addr wp smep nxe r-w-x cpl x86))

    :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
    :otf-flg t
    :gen-linear t
    :hints-l (("Goal" :in-theory (e/d (unsigned-byte-p) ())))
    :gen-type t
    :hints-t (("Goal" :in-theory (e/d (unsigned-byte-p) (not)))))

  (defthm x86p-mv-nth-2-ia32e-la-to-pa-page-directory
    (implies (x86p x86)
             (x86p
              (mv-nth 2
                      (ia32e-la-to-pa-page-directory
                       lin-addr base-addr wp smep nxe r-w-x cpl
                       x86)))))

  (defthm xr-ia32e-la-to-pa-page-directory
    (implies (and (not (equal fld :mem))
                  (not (equal fld :fault)))
             (equal (xr fld index
                        (mv-nth 2
                                (ia32e-la-to-pa-page-directory
                                 lin-addr base-addr wp smep nxe r-w-x cpl
                                 x86)))
                    (xr fld index x86))))

  (defthm ia32e-la-to-pa-page-directory-xw-values
    (implies (and (not (equal fld :mem))
                  (not (equal fld :fault))
                  (not (equal fld :programmer-level-mode)))
             (and (equal (mv-nth 0
                                 (ia32e-la-to-pa-page-directory
                                  lin-addr base-addr wp smep nxe r-w-x cpl
                                  (xw fld index value x86)))
                         (mv-nth 0
                                 (ia32e-la-to-pa-page-directory
                                  lin-addr base-addr wp smep nxe r-w-x cpl
                                  x86)))
                  (equal (mv-nth 1
                                 (ia32e-la-to-pa-page-directory
                                  lin-addr base-addr wp smep nxe r-w-x cpl
                                  (xw fld index value x86)))
                         (mv-nth 1
                                 (ia32e-la-to-pa-page-directory
                                  lin-addr base-addr wp smep nxe r-w-x cpl
                                  x86))))))

  (defthm ia32e-la-to-pa-page-directory-xw-state
    (implies (and (not (equal fld :mem))
                  (not (equal fld :fault))
                  (not (equal fld :programmer-level-mode)))
             (equal (mv-nth 2
                            (ia32e-la-to-pa-page-directory
                             lin-addr base-addr wp smep nxe r-w-x cpl
                             (xw fld index value x86)))
                    (xw fld index value
                        (mv-nth 2
                                (ia32e-la-to-pa-page-directory
                                 lin-addr base-addr wp smep nxe r-w-x cpl
                                 x86)))))))

;; ----------------------------------------------------------------------

(define ia32e-la-to-pa-page-dir-ptr-table
  ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
   (base-addr :type (unsigned-byte #.*physical-address-size*))
   (wp        :type (unsigned-byte  1))
   (smep      :type (unsigned-byte  1))
   (nxe       :type (unsigned-byte  1))
   (r-w-x     :type (member  :r :w :x))
   (cpl       :type (unsigned-byte  2))
   (x86))

  :parents (ia32e-paging)

  :guard (and (not (programmer-level-mode x86))
              (canonical-address-p lin-addr)
              ;; 4K-aligned --- the base address is
              ;; the 40 bits wide address obtained
              ;; from the referencing PDE, shifted
              ;; left by 12.
              (equal (loghead 12 base-addr) 0))

  :guard-hints (("Goal" :in-theory (e/d ()
                                        (unsigned-byte-p
                                         signed-byte-p
                                         member-equal
                                         not))))

  ;; Reference: Vol. 3A, Section 4.5 (Pg. 4-22) of the Feb'14 Intel
  ;; Manual.

  (if (mbt (not (programmer-level-mode x86)))

      (b* (
           ;; Fix the inputs of this function without incurring execution
           ;; overhead.
           (lin-addr (mbe :logic (logext 48 (loghead 48 lin-addr))
                          :exec lin-addr))
           (base-addr (mbe :logic (part-install
                                   0
                                   (loghead *physical-address-size* base-addr)
                                   :low 0 :width 12)
                           :exec base-addr))

           ;; First, we get the PDPTE (page directory pointer table entry)
           ;; address.  A PDPTE is selected using the physical address
           ;; defined as follows:
           ;;   Bits 51:12 are from the PML4E.
           ;;   Bits 11:3 are bits 38:30 of the linear address.
           ;;   Bits 2:0 are all 0.

           (p-entry-addr
            (the (unsigned-byte #.*physical-address-size*)
              (page-dir-ptr-table-entry-addr lin-addr base-addr)))

           ;;  [Shilpi]: Removed nested paging specification at this
           ;;  point.

           ;; Now we can read the PDPTE.
           (entry (the (unsigned-byte 64) (rm-low-64 p-entry-addr x86)))

           ((mv fault-flg val x86)
            (paging-entry-no-page-fault-p lin-addr entry wp smep nxe r-w-x cpl x86))
           ((when fault-flg)
            (mv 'Page-Fault val x86)))

        ;; No errors at this level, so we proceed with the translation.

        (if (mbe :logic (equal (page-size entry) 1)
                 :exec (equal (ia32e-page-tables-slice :ps entry) 1))
            ;; 1GB page
            (b* (
                 ;; Get accessed and dirty bits:
                 (accessed        (mbe :logic (accessed-bit entry)
                                       :exec (ia32e-pdpte-1GB-page-slice :pdpte-a entry)))
                 (dirty           (mbe :logic (dirty-bit entry)
                                       :exec (ia32e-pdpte-1GB-page-slice :pdpte-d entry)))
                 ;; Compute accessed and dirty bits:
                 (entry (if (equal accessed 0)
                            (mbe :logic (set-accessed-bit entry)
                                 :exec (!ia32e-pdpte-1GB-page-slice :pdpte-a 1 entry))
                          entry))
                 (entry (if (and (equal dirty 0)
                                 (equal r-w-x :w))
                            (mbe :logic (set-dirty-bit entry)
                                 :exec (!ia32e-pdpte-1GB-page-slice :pdpte-d 1 entry))
                          entry))
                 ;; Update x86 (to reflect accessed and dirty bits change), if needed:
                 (x86 (if (or (equal accessed 0)
                              (and (equal dirty 0)
                                   (equal r-w-x :w)))
                          (wm-low-64 p-entry-addr entry x86)
                        x86)))
              ;;  Return address of 1GB page frame and the modified x86 state.
              (mv nil
                  (mbe
                   :logic
                   (part-install
                    (part-select lin-addr :low 0 :high 29)
                    (ash (ia32e-pdpte-1GB-page-slice :pdpte-page entry) 30)
                    :low 0 :high 29)
                   :exec
                   (the
                       (unsigned-byte 52)
                     (logior
                      (the
                          (unsigned-byte 52)
                        (logand (the
                                    (unsigned-byte 52)
                                  (ash
                                   (the (unsigned-byte 22)
                                     (ia32e-pdpte-1GB-page-slice :pdpte-page entry))
                                   30))
                                (lognot (1- (ash 1 30)))))
                      (the (unsigned-byte 30)
                        (logand (1- (ash 1 30)) lin-addr)))))
                  x86))

          ;; Go to the next level of page table structure (PD, which
          ;; will reference a 2MB page or a 4K page, eventually).
          (b* ((page-directory-base-addr
                (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd entry) 12))
               ((mv flag
                    (the (unsigned-byte #.*physical-address-size*) p-addr)
                    x86)
                (ia32e-la-to-pa-page-directory
                 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))

               ((when flag)
                ;; Error, so do not update accessed bit
                (mv flag 0 x86))

               ;; Get accessed bit. Dirty bit is ignored when PDPTE
               ;; references the PD.
               (accessed        (mbe :logic (accessed-bit entry)
                                     :exec (ia32e-page-tables-slice :a entry)))
               ;; Update accessed bit, if needed.
               (entry (if (equal accessed 0)
                          (mbe :logic (set-accessed-bit entry)
                               :exec (!ia32e-page-tables-slice :a 1 entry))
                        entry))
               ;; Update x86, if needed.
               (x86 (if (equal accessed 0)
                        (wm-low-64 p-entry-addr entry x86)
                      x86)))
            (mv nil p-addr x86))))

    (mv t 0 x86))

  ///
  (defthm-usb n52p-mv-nth-1-ia32e-la-to-pa-page-dir-ptr-table
    :hyp t
    :bound *physical-address-size*
    :concl (mv-nth 1
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr base-addr wp smep nxe r-w-x cpl x86))

    :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
    :otf-flg t
    :gen-linear t
    :hints-l (("Goal" :in-theory (e/d (unsigned-byte-p) ())))
    :gen-type t
    :hints-t (("Goal" :in-theory (e/d (unsigned-byte-p) (not)))))

  (defthm x86p-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table
    (implies (x86p x86)
             (x86p
              (mv-nth 2
                      (ia32e-la-to-pa-page-dir-ptr-table
                       lin-addr base-addr wp smep nxe r-w-x cpl
                       x86)))))

  (defthm xr-ia32e-la-to-pa-page-dir-ptr-table
    (implies (and (not (equal fld :mem))
                  (not (equal fld :fault)))
             (equal (xr fld index
                        (mv-nth 2
                                (ia32e-la-to-pa-page-dir-ptr-table
                                 lin-addr base-addr wp smep nxe r-w-x cpl
                                 x86)))
                    (xr fld index x86))))

  (defthm ia32e-la-to-pa-page-dir-ptr-table-xw-values
    (implies (and (not (equal fld :mem))
                  (not (equal fld :fault))
                  (not (equal fld :programmer-level-mode)))
             (and (equal (mv-nth 0
                                 (ia32e-la-to-pa-page-dir-ptr-table
                                  lin-addr base-addr wp smep nxe r-w-x cpl
                                  (xw fld index value x86)))
                         (mv-nth 0
                                 (ia32e-la-to-pa-page-dir-ptr-table
                                  lin-addr base-addr wp smep nxe r-w-x cpl
                                  x86)))
                  (equal (mv-nth 1
                                 (ia32e-la-to-pa-page-dir-ptr-table
                                  lin-addr base-addr wp smep nxe r-w-x cpl
                                  (xw fld index value x86)))
                         (mv-nth 1
                                 (ia32e-la-to-pa-page-dir-ptr-table
                                  lin-addr base-addr wp smep nxe r-w-x cpl
                                  x86))))))

  (defthm ia32e-la-to-pa-page-dir-ptr-table-xw-state
    (implies (and (not (equal fld :mem))
                  (not (equal fld :fault))
                  (not (equal fld :programmer-level-mode)))
             (equal (mv-nth 2
                            (ia32e-la-to-pa-page-dir-ptr-table
                             lin-addr base-addr wp smep nxe r-w-x cpl
                             (xw fld index value x86)))
                    (xw fld index value
                        (mv-nth 2
                                (ia32e-la-to-pa-page-dir-ptr-table
                                 lin-addr base-addr wp smep nxe r-w-x cpl
                                 x86)))))))

;; ----------------------------------------------------------------------

(define ia32e-la-to-pa-pml4-table
  ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
   (base-addr :type (unsigned-byte #.*physical-address-size*))
   (wp        :type (unsigned-byte  1))
   (smep      :type (unsigned-byte  1))
   (nxe       :type (unsigned-byte  1))
   (r-w-x     :type (member  :r :w :x))
   (cpl       :type (unsigned-byte  2))
   (x86))

  :parents (ia32e-paging)

  :guard (and (not (programmer-level-mode x86))
              (canonical-address-p lin-addr)
              ;; 4K-aligned --- the base address is
              ;; the 40 bits wide address obtained
              ;; from the referencing PDE, shifted
              ;; left by 12.
              (equal (loghead 12 base-addr) 0))

  :guard-hints (("Goal" :in-theory (e/d ()
                                        (unsigned-byte-p
                                         signed-byte-p
                                         member-equal
                                         not))))

  ;; Reference: Vol. 3A, Section 4.5 (Pg. 4-22) of the Feb'14 Intel
  ;; Manual.

  (if (mbt (not (programmer-level-mode x86)))

      (b* (

           ;; Fix the inputs of this function without incurring execution
           ;; overhead.
           (lin-addr (mbe :logic (logext 48 (loghead 48 lin-addr))
                          :exec lin-addr))
           (base-addr (mbe :logic (part-install
                                   0
                                   (loghead *physical-address-size* base-addr)
                                   :low 0 :width 12)
                           :exec base-addr))

           ;; First, we get the address of the PML4E.  A PML4E is selected
           ;; using the physical address defined as follows:
           ;;   Bits 51:12 are from CR3.
           ;;   Bits 11:3 are bits 47:39 of the linear address.
           ;;   Bits 2:0 are all 0.
           (p-entry-addr
            (the (unsigned-byte #.*physical-address-size*)
              (pml4-table-entry-addr lin-addr base-addr)))

           ;; Now, we can read the PML4E.
           (entry (the (unsigned-byte 64) (rm-low-64 p-entry-addr x86)))

           ((mv fault-flg val x86)
            (paging-entry-no-page-fault-p lin-addr entry wp smep nxe r-w-x cpl x86))
           ((when fault-flg)
            (mv 'Page-Fault val x86))

           ;; No errors at this level, so we proceed with the translation.
           ;; We go to the next level of page table structure, i.e., PDPT.

           (page-dir-ptr-table-base-addr
            (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12))
           ((mv flag
                (the (unsigned-byte #.*physical-address-size*) p-addr)
                x86)
            (ia32e-la-to-pa-page-dir-ptr-table
             lin-addr page-dir-ptr-table-base-addr wp smep nxe r-w-x cpl x86))

           ((when flag)
            ;; Error, so do not update accessed bit.
            (mv flag 0 x86))

           ;; Get accessed bit. Dirty bit is ignored when PDPTE
           ;; references the PDPT.
           (accessed        (mbe :logic (accessed-bit entry)
                                 :exec (ia32e-page-tables-slice :a entry)))
           ;; Update accessed bit, if needed.
           (entry (if (equal accessed 0)
                      (mbe :logic (set-accessed-bit entry)
                           :exec (!ia32e-page-tables-slice :a 1 entry))
                    entry))
           ;; Update x86, if needed.
           (x86 (if (equal accessed 0)
                    (wm-low-64 p-entry-addr entry x86)
                  x86)))
        (mv nil p-addr x86))

    (mv t 0 x86))

  ///

  (defthm-usb n52p-mv-nth-1-ia32e-la-to-pa-pml4-table
    :hyp t
    :bound *physical-address-size*
    :concl (mv-nth 1
                   (ia32e-la-to-pa-pml4-table
                    lin-addr base-addr wp smep nxe r-w-x cpl x86))

    :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
    :otf-flg t
    :gen-linear t
    :hints-l (("Goal" :in-theory (e/d (unsigned-byte-p) ())))
    :gen-type t
    :hints-t (("Goal" :in-theory (e/d (unsigned-byte-p) (not)))))

  (defthm x86p-mv-nth-2-ia32e-la-to-pa-pml4-table
    (implies (x86p x86)
             (x86p
              (mv-nth 2
                      (ia32e-la-to-pa-pml4-table
                       lin-addr base-addr wp smep nxe r-w-x cpl
                       x86)))))

  (defthm xr-ia32e-la-to-pa-pml4-table
    (implies (and (not (equal fld :mem))
                  (not (equal fld :fault)))
             (equal (xr fld index
                        (mv-nth 2
                                (ia32e-la-to-pa-pml4-table
                                 lin-addr base-addr wp smep nxe r-w-x cpl
                                 x86)))
                    (xr fld index x86))))

  (defthm ia32e-la-to-pa-pml4-table-xw-values
    (implies (and (not (equal fld :mem))
                  (not (equal fld :fault))
                  (not (equal fld :programmer-level-mode)))
             (and (equal (mv-nth 0
                                 (ia32e-la-to-pa-pml4-table
                                  lin-addr base-addr wp smep nxe r-w-x cpl
                                  (xw fld index value x86)))
                         (mv-nth 0
                                 (ia32e-la-to-pa-pml4-table
                                  lin-addr base-addr wp smep nxe r-w-x cpl
                                  x86)))
                  (equal (mv-nth 1
                                 (ia32e-la-to-pa-pml4-table
                                  lin-addr base-addr wp smep nxe r-w-x cpl
                                  (xw fld index value x86)))
                         (mv-nth 1
                                 (ia32e-la-to-pa-pml4-table
                                  lin-addr base-addr wp smep nxe r-w-x cpl
                                  x86))))))

  (defthm ia32e-la-to-pa-pml4-table-xw-state
    (implies (and (not (equal fld :mem))
                  (not (equal fld :fault))
                  (not (equal fld :programmer-level-mode)))
             (equal (mv-nth 2
                            (ia32e-la-to-pa-pml4-table
                             lin-addr base-addr wp smep nxe r-w-x cpl
                             (xw fld index value x86)))
                    (xw fld index value
                        (mv-nth 2
                                (ia32e-la-to-pa-pml4-table
                                 lin-addr base-addr wp smep nxe r-w-x cpl
                                 x86)))))))

;; ----------------------------------------------------------------------

(define ia32e-la-to-pa
  ((lin-addr :type (signed-byte   #.*max-linear-address-size*)
             "Canonical linear address to be mapped to a physical address")
   (r-w-x     :type (member  :r :w :x)
              "Indicates whether this translation is on the behalf of a read, write, or instruction fetch")
   (cpl       :type (unsigned-byte  2)
              "Current privilege level (0-3), obtained from the CS segment selector [1:0]")
   (x86 "x86 state"))

  :parents (ia32e-paging)

  :guard (and (not (programmer-level-mode x86))
              (canonical-address-p lin-addr))

  :guard-hints (("Goal" :in-theory (e/d (
                                         acl2::bool->bit)
                                        (unsigned-byte-p
                                         signed-byte-p
                                         member-equal
                                         not))))


  ;; If lin-addr is not canonical, we should throw a general
  ;; protection exception (#GP(0)).  (Or a stack fault (#SS) as
  ;; appropriate?)

  (if (mbt (not (programmer-level-mode x86)))

      (b* ((lin-addr (mbe :logic (logext 48 (loghead 48 lin-addr))
                          :exec lin-addr))
           (cr0
            ;; CR0 is still a 32-bit register in 64-bit mode.
            (n32 (ctri *cr0* x86)))
           (cr4
            ;; CR4 has all but the low 21 bits reserved.
            (n21 (ctri *cr4* x86)))
           ;; ia32-efer has all but the low 12 bits reserved.
           (ia32-efer (n12 (msri *ia32_efer-idx* x86)))
           (wp        (cr0-slice :cr0-wp cr0))
           (smep      (cr4-slice :cr4-smep cr4))
           (nxe       (ia32_efer-slice :ia32_efer-nxe ia32-efer))
           (cr3       (ctri *cr3* x86))
           (pml4-table-base-addr
            (mbe
             :logic
             (ash (cr3-slice :cr3-pdb cr3) 12)
             :exec
             (the (unsigned-byte 52)
               (ash (the (unsigned-byte 40) (cr3-slice :cr3-pdb cr3)) 12)))))
        (ia32e-la-to-pa-pml4-table lin-addr pml4-table-base-addr wp smep nxe r-w-x cpl x86))

    (mv t 0 x86))

  ///

  (defthm-usb n52p-mv-nth-1-ia32e-la-to-pa
    :hyp t
    :bound *physical-address-size*
    :concl (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86))

    :hints (("Goal" :in-theory (e/d ()
                                    (force (force) unsigned-byte-p))))
    :otf-flg t
    :gen-linear t
    :hints-l (("Goal" :in-theory (e/d (unsigned-byte-p) (force (force)))))
    :gen-type t
    :hints-t (("Goal" :in-theory (e/d (unsigned-byte-p)
                                      (force (force) not)))))

  (defthm x86p-mv-nth-2-ia32e-la-to-pa
    (implies (x86p x86)
             (x86p (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))))

  (defthm xr-ia32e-la-to-pa
    (implies (and (not (equal fld :mem))
                  (not (equal fld :fault)))
             (equal (xr fld index
                        (mv-nth 2
                                (ia32e-la-to-pa
                                 lin-addr r-w-x cpl x86)))
                    (xr fld index x86)))
    :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthm ia32e-la-to-pa-xw-values
    (implies (and (not (equal fld :mem))
                  (not (equal fld :fault))
                  (not (equal fld :ctr))
                  (not (equal fld :msr))
                  (not (equal fld :programmer-level-mode)))
             (and (equal (mv-nth 0
                                 (ia32e-la-to-pa lin-addr r-w-x cpl
                                                 (xw fld index value x86)))
                         (mv-nth 0
                                 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
                  (equal (mv-nth 1
                                 (ia32e-la-to-pa lin-addr r-w-x cpl
                                                 (xw fld index value x86)))
                         (mv-nth 1
                                 (ia32e-la-to-pa lin-addr r-w-x cpl x86))))))

  (defthm ia32e-la-to-pa-xw-state
    (implies (and (not (equal fld :mem))
                  (not (equal fld :fault))
                  (not (equal fld :ctr))
                  (not (equal fld :msr))
                  (not (equal fld :programmer-level-mode)))
             (equal (mv-nth 2
                            (ia32e-la-to-pa lin-addr r-w-x cpl
                                            (xw fld index value x86)))
                    (xw fld index value
                        (mv-nth 2
                                (ia32e-la-to-pa lin-addr r-w-x cpl
                                                x86)))))
    :hints (("Goal" :in-theory (e/d* () (force (force)))))))

;; ======================================================================

(local
 (defthm loghead-equality-monotone
   (implies (and
             ;; Here's a dumb bind-free, but hey, it works for my
             ;; purpose!  I can make a nicer rule in the future or I
             ;; can simply be lazy and add to the bind-free.
             (bind-free (list (list (cons 'n ''12)))
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

(defthm page-table-lower-12-bits
  (implies (and (natp n)
                (<= n 12)
                (not (mv-nth
                      0
                      (ia32e-la-to-pa-page-table
                       lin-addr base-addr
                       u-s-acc wp smep nxe r-w-x cpl x86))))
           (equal
            (loghead n
                     (mv-nth 1
                             (ia32e-la-to-pa-page-table
                              lin-addr base-addr u-s-acc wp smep nxe
                              r-w-x cpl x86)))
            (loghead n lin-addr)))
  :hints
  (("Goal" :in-theory (e/d (ia32e-la-to-pa-page-table )
                           (unsigned-byte-p)))))

(defthm page-table-lower-12-bits-error
  (implies (and (natp n)
                (<= n 12)
                (x86p x86)
                (not (equal (loghead n
                                     (mv-nth 1 (ia32e-la-to-pa-page-table
                                                lin-addr base-addr
                                                u-s-acc wp smep nxe r-w-x cpl x86)))
                            (loghead n lin-addr))))
           (mv-nth 0 (ia32e-la-to-pa-page-table
                      lin-addr base-addr u-s-acc wp smep nxe r-w-x cpl x86)))
  :hints (("Goal" :in-theory (e/d (
                                   ia32e-la-to-pa-page-table)
                                  (unsigned-byte-p)))))

(defthm page-table-lower-12-bits-value-of-address-when-error
  (implies (and (natp n)
                (<= n 12)
                (mv-nth
                 0
                 (ia32e-la-to-pa-page-table
                  lin-addr base-addr
                  u-s-acc wp smep nxe r-w-x cpl x86)))
           (equal
            (loghead n
                     (mv-nth 1
                             (ia32e-la-to-pa-page-table
                              lin-addr base-addr u-s-acc wp smep nxe
                              r-w-x cpl x86)))
            0))
  :hints
  (("Goal" :in-theory (e/d (ia32e-la-to-pa-page-table )
                           (unsigned-byte-p)))))

(local
 (defthm negative-logand-to-positive-logand-n=64=for-now
   ;; TO-DO@Shilpi:
   ;; There are more general theorems called
   ;; negative-logand-to-positive-logand-with-natp-x and
   ;; negative-logand-to-positive-logand-with-integerp-x in
   ;; x86-register-readers-and-writers.lisp.  Why don't they work
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

(defthm page-directory-lower-12-bits
  (implies (and (natp n)
                (<= n 12)
                (not (mv-nth
                      0
                      (ia32e-la-to-pa-page-directory
                       lin-addr base-addr wp smep nxe r-w-x cpl x86))))
           (equal
            (loghead n
                     (mv-nth
                      1
                      (ia32e-la-to-pa-page-directory
                       lin-addr base-addr wp smep nxe r-w-x cpl x86)))
            (loghead n lin-addr)))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa-page-directory
                                   )
                                  (unsigned-byte-p)))))

(defthm page-directory-lower-12-bits-error
  (implies (and (natp n)
                (<= n 12)
                (not (equal
                      (loghead n
                               (mv-nth
                                1
                                (ia32e-la-to-pa-page-directory
                                 lin-addr base-addr wp smep nxe r-w-x cpl x86)))
                      (loghead n lin-addr))))
           (mv-nth
            0
            (ia32e-la-to-pa-page-directory
             lin-addr base-addr wp smep nxe r-w-x cpl x86)))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa-page-directory
                                   )
                                  (unsigned-byte-p)))))

(defthm page-directory-lower-12-bits-value-of-address-when-error
  (implies (and (natp n)
                (<= n 12)
                (mv-nth
                 0
                 (ia32e-la-to-pa-page-directory
                  lin-addr base-addr wp smep nxe r-w-x cpl x86)))
           (equal
            (loghead n
                     (mv-nth
                      1
                      (ia32e-la-to-pa-page-directory
                       lin-addr base-addr wp smep nxe r-w-x cpl x86)))
            0))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa-page-directory
                                   )
                                  (unsigned-byte-p)))))

(defthm page-dir-ptr-table-lower-12-bits
  (implies (and (natp n)
                (<= n 12)
                (not (mv-nth
                      0
                      (ia32e-la-to-pa-page-dir-ptr-table
                       lin-addr base-addr wp smep nxe r-w-x cpl x86))))
           (equal
            (loghead
             n
             (mv-nth
              1
              (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr base-addr wp smep nxe r-w-x cpl x86)))
            (loghead n lin-addr)))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                                  (unsigned-byte-p)))))

(defthm page-dir-ptr-table-lower-12-bits-error
  (implies (and (natp n)
                (<= n 12)
                (not (equal
                      (loghead
                       n
                       (mv-nth
                        1
                        (ia32e-la-to-pa-page-dir-ptr-table
                         lin-addr base-addr wp smep nxe r-w-x cpl x86)))
                      (loghead n lin-addr))))
           (mv-nth
            0
            (ia32e-la-to-pa-page-dir-ptr-table
             lin-addr base-addr wp smep nxe r-w-x cpl x86)))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                                  (unsigned-byte-p)))))

(defthm page-dir-ptr-table-lower-12-bits-value-of-address-when-error
  (implies (and (natp n)
                (<= n 12)
                (mv-nth
                 0
                 (ia32e-la-to-pa-page-dir-ptr-table
                  lin-addr base-addr wp smep nxe r-w-x cpl x86)))
           (equal
            (loghead
             n
             (mv-nth
              1
              (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr base-addr wp smep nxe r-w-x cpl x86)))
            0))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                                  (unsigned-byte-p)))))

(defthm pml4-lower-12-bits
  (implies (and (natp n)
                (<= n 12)
                (not (mv-nth
                      0
                      (ia32e-la-to-pa-pml4-table
                       lin-addr pml4-table-base-addr wp smep nxe r-w-x cpl x86))))
           (equal
            (loghead
             n
             (mv-nth
              1
              (ia32e-la-to-pa-pml4-table
               lin-addr pml4-table-base-addr wp smep nxe r-w-x cpl x86)))
            (loghead n lin-addr)))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                                  (unsigned-byte-p)))))

(defthm pml4-lower-12-bits-error
  (implies (and (natp n)
                (<= n 12)
                (not (equal
                      (loghead
                       n
                       (mv-nth
                        1
                        (ia32e-la-to-pa-pml4-table
                         lin-addr pml4-table-base-addr wp smep nxe r-w-x cpl x86)))
                      (loghead n lin-addr))))
           (mv-nth
            0
            (ia32e-la-to-pa-pml4-table
             lin-addr pml4-table-base-addr wp smep nxe r-w-x cpl x86)))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                                  (unsigned-byte-p)))))

(defthm pml4-lower-12-bits-value-of-address-when-error
  (implies (and (natp n)
                (<= n 12)
                (mv-nth
                 0
                 (ia32e-la-to-pa-pml4-table
                  lin-addr pml4-table-base-addr wp smep nxe r-w-x cpl x86)))
           (equal
            (loghead
             n
             (mv-nth
              1
              (ia32e-la-to-pa-pml4-table
               lin-addr pml4-table-base-addr wp smep nxe r-w-x cpl x86)))
            0))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                                  (unsigned-byte-p)))))

(defthm ia32e-la-to-pa-lower-12-bits
  (implies (and (natp n)
                (<= n 12)
                (x86p x86)
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86))))
           (equal
            (loghead n (mv-nth 1 (ia32e-la-to-pa
                                  lin-addr r-w-x cpl x86)))
            (loghead n lin-addr)))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa)
                                  ()))))

(defthm ia32e-la-to-pa-lower-12-bits-error
  (implies (and
            ;; Here's a dumb bind-free, but hey, it works for my
            ;; purposes!  I can make a nicer rule in the future or I
            ;; can simply be lazy and add to the bind-free.
            (bind-free (list (list (cons 'n ''12)))
                       (n))
            (natp n)
            (<= n 12)
            (not (equal (loghead n (mv-nth 1 (ia32e-la-to-pa
                                              lin-addr r-w-x cpl x86)))
                        (loghead n lin-addr))))
           (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa)
                                  (force (force))))))

(defthm ia32e-la-to-pa-lower-12-bits-value-of-address-when-error
  (implies (and (natp n)
                (<= n 12)
                (x86p x86)
                (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
           (equal
            (loghead n (mv-nth 1 (ia32e-la-to-pa
                                  lin-addr r-w-x cpl x86)))
            0))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa)
                                  ()))))

(defthml ia32e-la-to-pa-lower-12-bits-alt
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
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86))))
           (equal
            (loghead n lin-addr)
            (loghead n (mv-nth 1 (ia32e-la-to-pa
                                  lin-addr r-w-x cpl x86)))))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa)
                                  ()))))

(defthm ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-!=-all-ones
  ;; This rule comes in useful during the guard proof of rm16.
  (implies (and (x86p x86)
                (integerp lin-addr)
                (< (loghead 12 lin-addr) 4095)
                (not (mv-nth 0
                             (ia32e-la-to-pa lin-addr r-w-x cpl x86))))
           (< (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
              *mem-size-in-bytes-1*))
  :hints (("Goal" :in-theory
           (e/d () (ia32e-la-to-pa-lower-12-bits))))
  :rule-classes :linear)

(defthm loghead-monotonic-when-upper-bits-are-equal
  ;; See also the rule logtail-and-loghead-equality.
  (implies (and (< (loghead x a) (loghead x b))
                (equal (logtail x a) (logtail x b))
                (natp a)
                (natp b))
           (< a b))
  :hints
  (("Goal" :in-theory
    (e/d* (acl2::ihsext-inductions acl2::ihsext-recursive-redefs))))
  :rule-classes :forward-chaining)

(defthm logtail-and-loghead-inequality
  ;; See also the rule logtail-and-loghead-equality, which is a
  ;; forward-chaining rule.  This is a :rule-classes nil instead.
  (implies (and (<= (logtail n x) (logtail n y))
                (< (loghead n x) (loghead n y))
                (natp n)
                (natp x)
                (natp y))
           (< x y))
  :hints (("Goal" :cases ((< (logtail n x) (logtail n y)))))
  :rule-classes nil)

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
            (acl2::ihsext-inductions acl2::ihsext-recursive-redefs))))
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
  ;; This rule comes in useful during the guard proof of rm32.
  (implies (and (x86p x86)
                (integerp lin-addr)
                (< (loghead 12 lin-addr) 4093)
                (not (mv-nth 0
                             (ia32e-la-to-pa lin-addr r-w-x cpl x86))))
           (< (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
              *mem-size-in-bytes-3*))
  :hints (("Goal" :in-theory (e/d () (ia32e-la-to-pa-lower-12-bits))
           :use ((:instance
                  ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-<-4093-helper
                  (x (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))))))
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
  ;; This rule comes in useful during the guard proof of rm64.
  (implies (and (x86p x86)
                (integerp lin-addr)
                (< (loghead 12 lin-addr) 4089)
                (not (mv-nth 0
                             (ia32e-la-to-pa lin-addr r-w-x cpl x86))))
           (< (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
              *mem-size-in-bytes-7*))
  :hints (("Goal" :in-theory (e/d () (ia32e-la-to-pa-lower-12-bits))
           :use ((:instance
                  ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-<-4089-helper
                  (x (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))))))
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
  ;; This rule comes in useful during the guard proof of rm64.
  (implies (and (x86p x86)
                (integerp lin-addr)
                (equal (loghead 12 lin-addr) 4089)
                (not (mv-nth 0
                             (ia32e-la-to-pa lin-addr r-w-x cpl x86))))
           (<= (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
               *mem-size-in-bytes-7*))
  :hints (("Goal" :in-theory (e/d () (ia32e-la-to-pa-lower-12-bits))
           :use ((:instance
                  ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-=-4089-helper
                  (x (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))))))
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
  ;; This rule comes in useful during the guard proof of rm64.
  (implies (and (x86p x86)
                (integerp lin-addr)
                (equal (loghead 12 lin-addr) 4090)
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86))))
           (<= (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
               *mem-size-in-bytes-6*))
  :hints (("Goal" :in-theory (e/d () (ia32e-la-to-pa-lower-12-bits))
           :use ((:instance
                  ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-=-4090-helper
                  (x (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))))))
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
  ;; This rule comes in useful during the guard proof of rm128.
  (implies (and (x86p x86)
                (integerp lin-addr)
                (< (loghead 12 lin-addr) 4081)
                (not (mv-nth 0
                             (ia32e-la-to-pa lin-addr r-w-x cpl x86))))
           (< (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
              *mem-size-in-bytes-15*))
  :hints (("Goal" :in-theory (e/d () (ia32e-la-to-pa-lower-12-bits))
           :use ((:instance
                  ia32e-la-to-pa-<-*mem-size-in-bytes-15*-when-low-12-bits-<-4081-helper
                  (x (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))))))
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
  ;; This rule comes in useful during the guard proof of rm128.
  (implies (and (x86p x86)
                (integerp lin-addr)
                (equal (loghead 12 lin-addr) 4081)
                (not (mv-nth 0
                             (ia32e-la-to-pa lin-addr r-w-x cpl x86))))
           (<= (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
               *mem-size-in-bytes-15*))
  :hints (("Goal" :in-theory (e/d () (ia32e-la-to-pa-lower-12-bits))
           :use ((:instance
                  ia32e-la-to-pa-<-*mem-size-in-bytes-15*-when-low-12-bits-=-4081-helper
                  (x (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))))))
  :rule-classes :linear)

;; ======================================================================

(define la-to-pa
  ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
   (r-w-x     :type (member  :r :w :x)
              "Indicates whether this translation is on the behalf of a read, write, or instruction fetch")
   (cpl       :type (unsigned-byte  2)
              "Current privilege level (0-3), obtained from the CS segment selector [1:0]")
   (x86 "x86 state"))

  :inline t
  :enabled t

  :guard (not (programmer-level-mode x86))
  :parents (ia32e-paging)

  :short "Top-level page translation function"

  (if (mbt (and (canonical-address-p lin-addr)
                (not (programmer-level-mode x86))))
      (ia32e-la-to-pa lin-addr r-w-x cpl x86)
    (mv (list :ia32e-paging-invalid-linear-address-or-not-in-programmer-level-mode
              lin-addr)
        0 x86)))

;; ======================================================================

(in-theory (e/d* () (set-accessed-bit
                     set-dirty-bit
                     page-present
                     page-size
                     page-read-write
                     page-user-supervisor
                     page-execute-disable)))

;; ======================================================================
