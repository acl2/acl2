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
(local (include-book "kestrel/lists-light/nth" :dir :system))
;(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

(in-theory (disable rb rb-1 rml-size))

(defthm mv-nth-0-of-rb-1-of-xw
  (implies (not (equal :mem fld))
           (equal (mv-nth 0 (rb-1 n addr r-x (xw fld index val x86)))
                  (mv-nth 0 (rb-1 n addr r-x x86))))
  :hints (("Goal" :in-theory (enable rb-1))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rules about reading part of the value returned by RB-1 or RB.  Since bytes
;; are read in little-endian order, the low bytes of a read are a shorter read
;; at the same address, and the high bytes are a read at a later address.

(defthm rb-1-when-zp
  (implies (zp n)
           (equal (rb-1 n addr r-x x86)
                  (mv nil 0 x86)))
  :hints (("Goal" :in-theory (enable rb-1))))

(defthm mv-nth-1-of-rb-1-when-not-canonical-address-p
  (implies (not (canonical-address-p addr))
           (equal (mv-nth 1 (rb-1 n addr r-x x86))
                  0))
  :hints (("Goal" :in-theory (enable rb-1))))

(local (include-book "kestrel/bv/bvcat" :dir :system))
(local (include-book "kestrel/bv/ash" :dir :system))
(local (include-book "kestrel/bv/intro" :dir :system))
(local (include-book "kestrel/bv/bvor" :dir :system))
(local (include-book "kestrel/bv/slice" :dir :system))
(local (include-book "kestrel/bv/logtail" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

(local
 (defthm ash-of-8-becomes-bvcat
   (implies (and (unsigned-byte-p size rest)
                 (natp size))
            (equal (ash rest 8)
                   (acl2::bvcat size rest 8 0)))
   :hints (("Goal" :use (:instance acl2::ash-becomes-bvcat (acl2::x rest) (acl2::amt 8) (acl2::xsize size))
            :in-theory (e/d (acl2::unsigned-byte-p-forced) (acl2::ash-becomes-bvcat))))))

(local
 (defthm logior-of-bvcat-of-0
   (implies (and (unsigned-byte-p 8 byte)
                 (natp size))
            (equal (logior byte (acl2::bvcat size rest 8 0))
                   (acl2::bvcat size rest 8 byte)))
   :hints (("Goal" :use (:instance acl2::logior-becomes-bvor-when-unsigned-byte-p-arg1
                                   (acl2::size (+ 8 size)) (acl2::x byte) (acl2::y (acl2::bvcat size rest 8 0)))
            :in-theory (disable acl2::logior-becomes-bvor-when-unsigned-byte-p-arg1)))))

(local
 (defthm logior-of-ash-8-becomes-bvcat
   (implies (and (unsigned-byte-p 8 byte)
                 (unsigned-byte-p size rest)
                 (natp size))
            (equal (logior byte (ash rest 8))
                   (acl2::bvcat size rest 8 byte)))))

(local
 (defthm logtail-when-unsigned-byte-p-8
   (implies (and (unsigned-byte-p 8 x)
                 (<= 8 n)
                 (integerp n))
            (equal (logtail n x)
                   0))))

;; Unrolls rb-1 by one byte, expressing the result using bvcat.  Used in :use
;; hints below, because as a rewrite rule it can loop.
(local
 (defthmd mv-nth-1-of-rb-1-unroll
   (implies (posp n)
            (equal (mv-nth 1 (rb-1 n addr r-x x86))
                   (if (canonical-address-p addr)
                       (acl2::bvcat (* 8 (+ -1 n))
                                    (mv-nth 1 (rb-1 (+ -1 n) (+ 1 addr) r-x x86))
                                    8
                                    (mv-nth 1 (rvm08 addr x86)))
                     0)))
   :hints (("Goal" :expand (rb-1 n addr r-x x86)
            :use (:instance logior-of-ash-8-becomes-bvcat
                            (byte (mv-nth 1 (rvm08 addr x86)))
                            (rest (mv-nth 1 (rb-1 (+ -1 n) (+ 1 addr) r-x x86)))
                            (size (* 8 (+ -1 n))))
            :in-theory (disable rvm08 logior-of-ash-8-becomes-bvcat)))))

(local
 (defun rb-1-double-induct (n n2 addr)
   (if (or (zp n) (zp n2))
       (list n n2 addr)
     (rb-1-double-induct (+ -1 n) (+ -1 n2) (+ 1 addr)))))

;; The low N bytes of a read of N2 bytes.
(local
 (defthm bvchop-of-mv-nth-1-of-rb-1-helper
   (implies (and (<= n n2)
                 (natp n)
                 (natp n2))
            (equal (acl2::bvchop (* 8 n) (mv-nth 1 (rb-1 n2 addr r-x x86)))
                   (mv-nth 1 (rb-1 n addr r-x x86))))
   :hints (("Goal" :induct (rb-1-double-induct n n2 addr)
            :in-theory (disable rb-1 rvm08))
           ("Subgoal *1/2" :use ((:instance mv-nth-1-of-rb-1-unroll)
                                 (:instance mv-nth-1-of-rb-1-unroll (n n2)))
            :in-theory (disable rb-1 rvm08 acl2::bvcat-equal-rewrite acl2::bvcat-equal-rewrite-alt)))))

(local
 (defthm not-signed-byte-p-48-of-+-when-not-signed-byte-p-48-of-+-of-1
   (implies (and (not (signed-byte-p 48 (+ 1 addr)))
                 (signed-byte-p 48 addr)
                 (posp k))
            (not (signed-byte-p 48 (+ k addr))))
   :hints (("Goal" :in-theory (enable signed-byte-p)))))

;; All but the low K bytes of a read.
(local
 (defthm logtail-of-mv-nth-1-of-rb-1-helper
   (implies (and (canonical-address-p addr)
                 (natp k))
            (equal (logtail (* 8 k) (mv-nth 1 (rb-1 n addr r-x x86)))
                   (mv-nth 1 (rb-1 (- n k) (+ k addr) r-x x86))))
   :hints (("Goal" :induct (rb-1-double-induct k n addr)
            :in-theory (disable rb-1 rvm08))
           ("Subgoal *1/2" :cases ((canonical-address-p (+ 1 addr)))
            :use ((:instance mv-nth-1-of-rb-1-unroll)
                  (:instance not-signed-byte-p-48-of-+-when-not-signed-byte-p-48-of-+-of-1))
            :in-theory (disable rb-1 rvm08 acl2::bvcat-equal-rewrite acl2::bvcat-equal-rewrite-alt)))))

;; Taking the low bytes of a read gives a shorter read.
(defthm bvchop-of-mv-nth-1-of-rb-1
  (implies (and (integerp (/ size 8)) ; size is a multiple of 8
                (<= size (* 8 n))
                (integerp n))
           (equal (acl2::bvchop size (mv-nth 1 (rb-1 n addr r-x x86)))
                  (mv-nth 1 (rb-1 (/ size 8) addr r-x x86))))
  :hints (("Goal" :use (:instance bvchop-of-mv-nth-1-of-rb-1-helper
                                  (n (/ size 8))
                                  (n2 n))
           :in-theory (disable bvchop-of-mv-nth-1-of-rb-1-helper rb-1))))

;; Dropping the low bytes of a read gives a read at a later address.
(defthm logtail-of-mv-nth-1-of-rb-1
  (implies (and (integerp (/ pos 8)) ; pos is a multiple of 8
                (natp pos)
                (canonical-address-p addr))
           (equal (logtail pos (mv-nth 1 (rb-1 n addr r-x x86)))
                  (mv-nth 1 (rb-1 (- n (/ pos 8)) (+ (/ pos 8) addr) r-x x86))))
  :hints (("Goal" :use (:instance logtail-of-mv-nth-1-of-rb-1-helper
                                  (k (/ pos 8)))
           :in-theory (disable logtail-of-mv-nth-1-of-rb-1-helper rb-1))))

;; Taking some of the bytes of a read gives a shorter read, possibly at a later address.
(local
 (defthm slice-of-mv-nth-1-of-rb-1-helper
   (implies (and (<= high-bytes n)
                 (natp low-bytes)
                 (integerp high-bytes)
                 (integerp n)
                 (canonical-address-p addr))
            (equal (acl2::slice (+ -1 (* 8 high-bytes)) (* 8 low-bytes) (mv-nth 1 (rb-1 n addr r-x x86)))
                   (mv-nth 1 (rb-1 (- high-bytes low-bytes) (+ low-bytes addr) r-x x86))))
   :hints (("Goal" :cases ((< high-bytes low-bytes))
            :use (:instance bvchop-of-mv-nth-1-of-rb-1-helper
                            (n (- high-bytes low-bytes))
                            (n2 (- n low-bytes))
                            (addr (+ low-bytes addr)))
            :in-theory (e/d (acl2::slice) (rb-1 bvchop-of-mv-nth-1-of-rb-1-helper bvchop-of-mv-nth-1-of-rb-1))))))

(defthm slice-of-mv-nth-1-of-rb-1
  (implies (and (integerp (/ low 8)) ; low is a multiple of 8
                (integerp (/ (+ 1 high) 8)) ; high+1 is a multiple of 8
                (< high (* 8 n))
                (natp low)
                (integerp n)
                (canonical-address-p addr))
           (equal (acl2::slice high low (mv-nth 1 (rb-1 n addr r-x x86)))
                  (mv-nth 1 (rb-1 (- (/ (+ 1 high) 8) (/ low 8)) (+ (/ low 8) addr) r-x x86))))
  :hints (("Goal" :use (:instance slice-of-mv-nth-1-of-rb-1-helper
                                  (low-bytes (/ low 8))
                                  (high-bytes (/ (+ 1 high) 8)))
           :in-theory (disable slice-of-mv-nth-1-of-rb-1-helper rb-1))))

;; Versions of the above for RB, which is RB-1 in the app-view:

(defthm bvchop-of-mv-nth-1-of-rb
  (implies (and (integerp (/ size 8)) ; size is a multiple of 8
                (<= size (* 8 n))
                (integerp n)
                (app-view x86))
           (equal (acl2::bvchop size (mv-nth 1 (rb n addr r-x x86)))
                  (mv-nth 1 (rb (/ size 8) addr r-x x86))))
  :hints (("Goal" :in-theory (enable rb))))

(defthm logtail-of-mv-nth-1-of-rb
  (implies (and (integerp (/ pos 8)) ; pos is a multiple of 8
                (natp pos)
                (canonical-address-p addr)
                (app-view x86))
           (equal (logtail pos (mv-nth 1 (rb n addr r-x x86)))
                  (mv-nth 1 (rb (- n (/ pos 8)) (+ (/ pos 8) addr) r-x x86))))
  :hints (("Goal" :in-theory (enable rb))))

(defthm slice-of-mv-nth-1-of-rb
  (implies (and (integerp (/ low 8)) ; low is a multiple of 8
                (integerp (/ (+ 1 high) 8)) ; high+1 is a multiple of 8
                (< high (* 8 n))
                (natp low)
                (integerp n)
                (canonical-address-p addr)
                (app-view x86))
           (equal (acl2::slice high low (mv-nth 1 (rb n addr r-x x86)))
                  (mv-nth 1 (rb (- (/ (+ 1 high) 8) (/ low 8)) (+ (/ low 8) addr) r-x x86))))
  :hints (("Goal" :in-theory (enable rb))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reading memory that was not written by a write.

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;; Distinct canonical addresses are distinct after chopping to 48 bits.
(local
 (defthm equal-of-bvchop-48-and-bvchop-48-when-signed-byte-p-48
   (implies (and (signed-byte-p 48 a)
                 (signed-byte-p 48 b))
            (equal (equal (acl2::bvchop 48 a) (acl2::bvchop 48 b))
                   (equal a b)))
   :hints (("Goal" :cases ((and (< a 0) (< b 0))
                           (and (< a 0) (<= 0 b))
                           (and (<= 0 a) (< b 0)))
            :in-theory (enable acl2::bvchop signed-byte-p acl2::mod-sum-cases)))))

(defthm mv-nth-1-of-rvm08-of-mv-nth-1-of-wvm08-diff
  (implies (not (equal addr addr2))
           (equal (mv-nth 1 (rvm08 addr (mv-nth 1 (wvm08 addr2 val x86))))
                  (mv-nth 1 (rvm08 addr x86))))
  :hints (("Goal" :in-theory (enable rvm08 wvm08))))

(local
 (defun wb-1-induct (n addr value x86)
   (declare (xargs :stobjs x86 :verify-guards nil))
   (if (zp n)
       (mv nil x86)
     (if (not (canonical-address-p addr))
         (mv t x86)
       (mv-let (flg0 x86)
         (wvm08 addr (loghead 8 value) x86)
         (if flg0
             (mv flg0 x86)
           (wb-1-induct (1- n) (1+ addr) (logtail 8 value) x86)))))))

(defthm mv-nth-1-of-rvm08-of-mv-nth-1-of-wb-1-disjoint
  (implies (or (< addr addr2)
               (<= (+ n addr2) addr))
           (equal (mv-nth 1 (rvm08 addr (mv-nth 1 (wb-1 n addr2 w value x86))))
                  (mv-nth 1 (rvm08 addr x86))))
  :hints (("Goal" :induct (wb-1-induct n addr2 value x86)
           :in-theory (disable rvm08 wvm08))))

(defthm mv-nth-1-of-rb-1-of-mv-nth-1-of-wb-1-disjoint
  (implies (or (<= (+ n2 addr2) addr)
               (<= (+ n addr) addr2))
           (equal (mv-nth 1 (rb-1 n addr r-x (mv-nth 1 (wb-1 n2 addr2 w value x86))))
                  (mv-nth 1 (rb-1 n addr r-x x86))))
  :hints (("Goal" :induct (rb-1 n addr r-x x86)
           :in-theory (e/d (rb-1) (rvm08 wb-1)))))

(defthm mv-nth-1-of-rb-of-mv-nth-1-of-wb-disjoint
  (implies (and (or (<= (+ n2 addr2) addr)
                    (<= (+ n addr) addr2))
                (app-view x86))
           (equal (mv-nth 1 (rb n addr r-x (mv-nth 1 (wb n2 addr2 w value x86))))
                  (mv-nth 1 (rb n addr r-x x86))))
  :hints (("Goal" :in-theory (e/d (rb wb) (rb-1 wb-1)))))
