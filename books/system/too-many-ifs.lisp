; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore (original date April, 2010)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Logic Admission and Guard Verification of too-many-ifs pre- and post-rewrite.

; (certify-book "too-many-ifs")

(in-package "ACL2")

(include-book "tools/flag" :dir :system)

(include-book "arithmetic/top-with-meta" :dir :system)

(make-flag pseudo-termp-flg
           pseudo-termp
           :flag-var flg
           :flag-mapping ((pseudo-termp term)
                          (pseudo-term-listp list))
           :defthm-macro-name defthm-pseudo-termp
           :local t)

(verify-termination var-counts1)

(make-flag var-counts1-flg
           var-counts1
           :flag-var flg
           :flag-mapping ((var-counts1 term)
                          (var-counts1-lst list))
           :defthm-macro-name defthm-var-counts1
           :local t)

(defthm-var-counts1 natp-var-counts1
  (term
   (implies (natp acc)
            (natp (var-counts1 arg rhs acc)))
   :rule-classes :type-prescription)
  (list
   (implies (natp acc)
            (natp (var-counts1-lst arg lst acc)))
   :rule-classes :type-prescription)
  :hints (("Goal" :induct (var-counts1-flg flg rhs arg lst acc))))

(verify-guards var-counts1)

(verify-termination var-counts) ; and guards

;;; Since the comment about var-counts says that var-counts returns a list of
;;; nats as long as lhs-args, I prove those facts, speculatively.

; Except, we reason instead about integer-listp.  See the comment just above
; the commented-out definition of nat-listp in the source code (file
; rewrite.lisp).
; (verify-termination nat-listp)

(defthm integer-listp-var-counts
  (integer-listp (var-counts lhs-args rhs)))

(defthm len-var-counts
  (equal (len (var-counts lhs-args rhs))
         (len lhs-args)))

(verify-termination count-ifs) ; and guards

(verify-termination too-many-ifs0) ; and guards

(verify-termination too-many-ifs-pre-rewrite-builtin) ; and guards

(verify-termination occur-cnt-bounded)

(make-flag occur-cnt-bounded-flg
           occur-cnt-bounded
           :flag-var flg
           :flag-mapping ((occur-cnt-bounded term)
                          (occur-cnt-bounded-lst list))
           :defthm-macro-name defthm-occur-cnt-bounded
           :local t)

(defthm-occur-cnt-bounded integerp-occur-cnt-bounded
  (term
   (implies (and (integerp a)
                 (integerp m))
            (integerp (occur-cnt-bounded term1 term2 a m bound-m)))
   :rule-classes :type-prescription)
  (list
   (implies (and (integerp a)
                 (integerp m))
            (integerp (occur-cnt-bounded-lst term1 lst a m bound-m)))
   :rule-classes :type-prescription)
  :hints (("Goal" :induct (occur-cnt-bounded-flg flg term2 term1 lst a m bound-m))))

(defthm-occur-cnt-bounded signed-byte-p-30-occur-cnt-bounded-flg
  (term
   (implies (and (force (signed-byte-p 30 a))
                 (signed-byte-p 30 m)
                 (signed-byte-p 30 (+ bound-m m))
                 (force (<= 0 a))
                 (<= 0 m)
                 (<= 0 bound-m)
                 (<= a (+ bound-m m)))
            (and (<= -1 (occur-cnt-bounded term1 term2 a m bound-m))
                 (<= (occur-cnt-bounded term1 term2 a m bound-m) (+ bound-m m))))
   :rule-classes :linear)
  (list
   (implies (and (force (signed-byte-p 30 a))
                 (signed-byte-p 30 m)
                 (signed-byte-p 30 (+ bound-m m))
                 (force (<= 0 a))
                 (<= 0 m)
                 (<= 0 bound-m)
                 (<= a (+ bound-m m)))
            (and (<= -1 (occur-cnt-bounded-lst term1 lst a m bound-m))
                 (<= (occur-cnt-bounded-lst term1 lst a m bound-m) (+ bound-m m))))
   :rule-classes :linear)
  :hints (("Goal" :induct (occur-cnt-bounded-flg flg term2 term1 lst a m bound-m))))

(verify-guards occur-cnt-bounded)

(verify-termination too-many-ifs1) ; and guards

(verify-termination too-many-ifs-post-rewrite-builtin) ; and guards
