; Rules about memory
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA") ;; unlike most books, this one is in the X86ISA package

;; Some theorems about linear memory operations in the x86 model, including RB,
;; RB-1, RML-size, and RML-<xx> where <xx> is 08/16/32/48/64/80/128.

(include-book "projects/x86isa/machine/linear-memory" :dir :system)
(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system) ; todo: use byte-listp instead below?
(include-book "kestrel/bv/bvcat" :dir :system)
(local (include-book "support-bv"))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/rules" :dir :system)) ; for slice-too-high-is-0-new (todo: move it)
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
;(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

(in-theory (disable rb rb-1 rml-size))

(defthm mv-nth-0-of-rb-1-of-xw
  (implies (not (equal :mem fld))
           (equal (mv-nth 0 (rb-1 n addr r-x (xw fld index val x86)))
                  (mv-nth 0 (rb-1 n addr r-x x86))))
  :hints (("Goal" :in-theory (e/d (rb-1) ()))))

(defthm mv-nth-1-of-rb-1-of-xw
  (implies (not (equal :mem fld))
           (equal (mv-nth 1 (rb-1 n addr r-x (xw fld index val x86)))
                  (mv-nth 1 (rb-1 n addr r-x x86))))
  :hints (("Goal" :in-theory (e/d (rb-1) (x86p-xw)))))

(defthm mv-nth-0-of-rb-of-xw-when-app-view
  (implies (and (not (equal fld :mem))
                (not (equal fld :app-view))
                (app-view x86))
           (equal (mv-nth 0 (rb n addr r-x (xw fld index val x86)))
                  (mv-nth 0 (rb n addr r-x x86))))
  :hints (("Goal" :in-theory (e/d (rb) (rb-1)))))

(defthm mv-nth-0-of-rml-size-of-xw-when-app-view
  (implies (and (not (equal fld :mem))
                (not (equal fld :app-view))
                (app-view x86))
           (equal (mv-nth 0 (rml-size nbytes addr r-x (xw fld index val x86)))
                  (mv-nth 0 (rml-size nbytes addr r-x x86))))
  :hints (("Goal" :in-theory (enable rml-size
                                     rml16
                                     rml32
                                     rml48
                                     rml64
                                     rml80
                                     rml128))))

;TODO: The r-x param of rb-1 is irrelevant (drop it?)
;; This clearly shows that the param is irrelevant, but this would loop as a rewrite rule.
(defthm rb-1-rx-irrel
  (equal (rb-1 n addr r-x     x86)
         (rb-1 n addr r-x-alt x86))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable rb-1))))

;; Take advance of the fact that the r-w-x param is irrelevant to normalize it.
(defthm rb-1-when-not-r
  (implies (not (eq :r r-x))
           (equal (rb-1 n addr r-x x86)
                  (rb-1 n addr :r x86)))
  :hints (("Goal" :in-theory (enable rb-1))))

;avoids all the special cases in rml-size
(defthm rml-size-becomes-rb
  (implies (and (app-view x86)
                (canonical-address-p addr)
                (canonical-address-p (+ -1 addr nbytes)))
           (equal (rml-size nbytes addr r-x x86)
                  (rb nbytes addr r-x x86)))
  :hints (("Goal" :in-theory (enable rml-size
                                     rml08
                                     rml16
                                     rml32
                                     rml48
                                     rml64
                                     rml80
                                     rml128
                                     rml256))))

(defthm mv-nth-1-of-rml-size-of-0
  (equal (mv-nth 1 (rml-size 0 addr r-x x86))
         0)
  :hints (("Goal" :in-theory (enable rml-size))))

;; Take advance of the fact that the r-w-x param is irrelevant to normalize it.

(defthm mv-nth-1-of-rb-1-when-not-natp-cheap
  (implies (not (natp n))
           (equal (mv-nth 1 (rb-1 n addr r-x x86))
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable rb-1))))

; better than x86isa::size-of-rb-1
(defthm unsigned-byte-p-of-mv-nth-1-of-rb-1
  (implies (and (<= (* 8 n) m)
                (natp m)
                (x86p x86))
           (unsigned-byte-p m (mv-nth 1 (rb-1 n addr r-x x86))))
  :hints (("Goal" :use (:instance size-of-rb-1 (m (* 8 n)))
           :in-theory (e/d (ash ifix)
                           (size-of-rb-1)))))

(defthm mv-nth-2-of-rb-1-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rb-1 n addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rb-1))))

(defthm mv-nth-2-of-rb-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rb n addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rb))))

(defthm mv-nth-2-of-rml08-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml08 addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml08))))

(defthm mv-nth-2-of-rml16-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml16 addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml16))))

(defthm mv-nth-2-of-rml32-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml32 addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml32))))

(defthm mv-nth-2-of-rml48-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml48 addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml48))))

(defthm mv-nth-2-of-rml64-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml64 addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml64))))

(defthm mv-nth-2-of-rml80-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml80 addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml80))))

(defthm mv-nth-2-of-rml128-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml128 addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml128))))

(defthm mv-nth-2-of-rml-size-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml-size nbytes addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml-size))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Material on combine-bytes is here because it is defined in projects/x86isa/machine/linear-memory.lisp

;; (defthm byte-listp-becomes-all-unsigned-byte-p
;;   (equal (byte-listp bytes)
;;          (and (acl2::all-unsigned-byte-p 8 bytes)
;;               (true-listp bytes)))
;;   :hints (("Goal" :in-theory (enable acl2::all-unsigned-byte-p byte-listp))))

(local
  (defun combine-bytes-n-induct (bytes n)
    (if (endp bytes)
        (list bytes n)
      (combine-bytes-n-induct (cdr bytes) (+ -8 n)))))

(defthm unsigned-byte-p-of-combine-bytes-better
  (implies (and (acl2::all-unsigned-byte-p 8 bytes)
                (natp n)
                (>= n (* 8 (len bytes))))
           (unsigned-byte-p n (combine-bytes bytes)))
  :hints (("Goal" :induct (combine-bytes-n-induct bytes n)
           :in-theory (e/d (combine-bytes)
                           (x86isa::natp-combine-bytes ;bad (forcing)
                            )))))

;not true.  gross!
;; (DEFTHM NATP-COMBINE-BYTES-better
;;   (NATP (COMBINE-BYTES BYTES))
;;   :RULE-CLASSES :TYPE-PRESCRIPTION
;;   :hints (("Goal" :in-theory (e/d (COMBINE-BYTES) ( NATP-COMBINE-BYTES)))))

;also uses better bvops
(defthmd combine-bytes-unroll-better
  (implies (and (not (endp bytes))
                (true-listp bytes) ;todo drop
                (acl2::all-unsigned-byte-p 8 bytes))
           (equal (combine-bytes bytes)
                  (acl2::bvcat (* 8 (- (len bytes) 1))
                               (combine-bytes (cdr bytes))
                               8
                               (car bytes)
                               )))
  :hints (("Goal" :induct (COMBINE-BYTES BYTES)
           :expand (COMBINE-BYTES BYTES)
           :in-theory (e/d (COMBINE-BYTES
                            (:induction combine-bytes)
                            ACL2::SLICE-TOO-HIGH-IS-0-NEW)
                           (;ACL2::UNSIGNED-BYTE-P-LOGIOR ;caused forcing
                            )))))

(defthm unsigned-byte-p-of-combine-bytes-lemma
  (implies (byte-listp bytes)
           (unsigned-byte-p (* 8 (len bytes))
                            (combine-bytes bytes)))
  :hints (("Goal" :in-theory (enable combine-bytes byte-listp))))

(defthm slice-of-combine-bytes
  (implies (and (natp n)
                (< n (len bytes))
                (byte-listp bytes) ;too bad
                )
           (equal (acl2::slice (+ 7 (* 8 n)) (* 8 n) (x86isa::combine-bytes bytes))
                  (acl2::bvchop 8 (nth n bytes))))
  :hints (("Goal" :in-theory (e/d (x86isa::combine-bytes
                                   ACL2::BVCAT-RECOMBINE
                                   ;;logapp
                                   ;;ACL2::SLICE-OF-SUM-CASES
                                   (:i nth)
                                   BYTE-LISTP)
                                  (;acl2::nth-of-cdr
                                   )))))

;; generalize to multi-byte read
;; See also x86isa::rb-returns-no-error-app-view
(defthmd mv-nth-0-of-rb-of-1
  (implies (app-view x86)
           (equal (mv-nth 0 (rb 1 x86isa::addr x86isa::r-x x86))
                  (if (canonical-address-p x86isa::addr)
                      nil
                    'rb-1)))
  :hints (("Goal" :in-theory (enable rb rb-1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These have much simpler RHSes than the definitions:
;; TODO: try enabling these.  But see rules like rml512-becomes-read instead!

;; for some reason the 128 and 256 functions are not as nice as the others
;; we assume app-view here to be able to get a nice, simple RHS
;; also simplified the MBEs/MBTs and removed the THEs
(defthmd rml128-when-app-view
  (implies (app-view x86)
           (equal (rml128 lin-addr r-x x86)
                  (if (canonical-address-p lin-addr)
                      (let* ((15+lin-addr (+ 15 lin-addr)))
                        (if (canonical-address-p 15+lin-addr)
                            (rb 16 lin-addr r-x x86)
                          (mv 'rml128 0 x86)))
                    (mv 'rml128 0 x86))))
  :hints (("Goal" :in-theory (enable rml128))))

(defthmd rml256-when-app-view
  (implies (app-view x86)
           (equal (rml256 lin-addr r-x x86)
                  (if (canonical-address-p lin-addr)
                      (let* ((31+lin-addr (+ 31 lin-addr)))
                        (if (canonical-address-p 31+lin-addr)
                            (rb 32 lin-addr r-x x86)
                          (mv 'rml256 0 x86)))
                    (mv 'rml256 0 x86))))
  :hints (("Goal" :in-theory (enable rml256))))

;todo: simplify rhs (of this and others)
(defthmd rml512-when-app-view
  (implies (app-view x86)
           (equal (rml512 lin-addr r-x x86)
                  (if (canonical-address-p lin-addr)
                      (let* ((63+lin-addr (+ 63 lin-addr)))
                        (if (canonical-address-p 63+lin-addr)
                            (rb 64 lin-addr r-x x86)
                          (mv 'rml512 0 x86)))
                    (mv 'rml512 0 x86))))
  :hints (("Goal" :in-theory (enable rml512))))

;todo: simplify rhs
(defthmd wml128-when-app-view
  (implies (app-view x86)
           (equal (wml128 lin-addr val x86)
                  (if (canonical-address-p lin-addr)
                      (let* ((15+lin-addr (+ 15 lin-addr)))
                        (if (canonical-address-p 15+lin-addr)
                            (wb 16 lin-addr :w val x86)
                          (mv 'wml128 x86)))
                    (mv 'wml128 x86))))
  :hints (("Goal" :in-theory (enable wml128))))

;todo: simplify rhs
(defthmd wml256-when-app-view
  (implies (app-view x86)
           (equal (wml256 lin-addr val x86)
                  (if (canonical-address-p lin-addr)
                      (let* ((31+lin-addr (+ 31 lin-addr)))
                        (if (canonical-address-p 31+lin-addr)
                            (wb 32 lin-addr :w val x86)
                          (mv 'wml256 x86)))
                    (mv 'wml256 x86))))
  :hints (("Goal" :in-theory (enable wml256))))

(defthmd wml512-when-app-view
  (implies (app-view x86)
           (equal (wml512 lin-addr val x86)
                  (if (and (canonical-address-p lin-addr)
                           (canonical-address-p (+ 63 lin-addr)))
                      (wb 64 lin-addr :w val x86)
                    (mv 'wml512 x86))))
  :hints (("Goal" :in-theory (enable wml512))))
