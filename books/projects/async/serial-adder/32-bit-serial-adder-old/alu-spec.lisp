;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau (derived from the FM9001 work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; The ACL2 source code for the FM9001 work is available at
;; https://github.com/acl2/acl2/tree/master/books/projects/fm9001.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; January 2019

;; The high level specification of the ALU

(in-package "ADE")

(include-book "constants")
(include-book "../../hard-spec")

;; ======================================================================

;; CVZBV is used to construct all of the values returned by the ALU
;; specification V-ALU.

(defun cvzbv (carry overflow vector)
  (declare (xargs :guard t))
  (cons carry (cons overflow (cons (v-zp vector) vector))))

(defun c (cvzbv)
  (declare (xargs :guard (true-listp cvzbv)))
  (car cvzbv))

(defun v (cvzbv)
  (declare (xargs :guard (true-listp cvzbv)))
  (cadr cvzbv))

(defun bv (cvzbv)
  (declare (xargs :guard (true-listp cvzbv)))
  (cdddr cvzbv))

(defun n (cvzbv)
  (declare (xargs :guard (true-listp cvzbv)))
  (v-negp (bv cvzbv)))

(defun zb (cvzbv)
  (declare (xargs :guard (true-listp cvzbv)))
  (caddr cvzbv))

(defthm booleanp-n
  (implies (bvp (bv v))
           (booleanp (n v)))
  :rule-classes :type-prescription)

(defthm booleanp-zp-cvzbv
  (booleanp (zb (cvzbv c v bv)))
  :rule-classes :type-prescription)

(defthm booleanp-bvp-cvzbv
  (and
   (equal (booleanp (c (cvzbv c v bv)))
          (booleanp c))
   (equal (booleanp (v (cvzbv c v bv)))
          (booleanp v))
   (equal (bvp (bv (cvzbv c v bv)))
          (bvp bv))))

(defthmd bvp-cvzbv
  (implies (and (true-listp cvzbv)
                (booleanp (c cvzbv))
                (booleanp (v cvzbv))
                (booleanp (zb cvzbv))
                (bvp (bv cvzbv)))
           (bvp cvzbv))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(in-theory (disable c v n zb bv))

;; Specification abbreviations for V-ALU.

(defun cvzbv-v-ror (c a)
  (declare (xargs :guard (true-listp a)))
  (cvzbv (if (atom a) c (nth 0 a))
         nil
         (v-ror a c)))

(defun cvzbv-v-adder (c a b)
  (declare (xargs :guard (and (consp a)
                              (true-listp a)
                              (consp b)
                              (true-listp b))))
  (cvzbv (v-adder-carry-out c a b)
         (v-adder-overflowp c a b)
         (v-adder-output    c a b)))

(defun cvzbv-v-lsl (a)
  (declare (xargs :guard (and (consp a)
                              (true-listp a))))
  (cvzbv-v-adder nil a a))

(defun cvzbv-v-subtracter (c a b)
  (declare (xargs :guard (and (consp a)
                              (true-listp a)
                              (consp b)
                              (true-listp b))))
  (cvzbv (v-subtracter-carry-out c a b)
         (v-subtracter-overflowp c a b)
         (v-subtracter-output    c a b)))

(defun cvzbv-inc (a)
  (declare (xargs :guard (and (consp a)
                              (true-listp a))
                  :guard-hints (("Goal" :in-theory (enable nat-to-v)))))
  (cvzbv-v-adder t a (nat-to-v 0 (len a))))

(defun cvzbv-neg (a)
  (declare (xargs :guard (and (consp a)
                              (true-listp a))
                  :guard-hints (("Goal" :in-theory (enable nat-to-v)))))
  (cvzbv-v-subtracter nil a (nat-to-v 0 (len a))))

(defun cvzbv-dec (a)
  (declare (xargs :guard (and (consp a)
                              (true-listp a))
                  :guard-hints (("Goal" :in-theory (enable nat-to-v)))))
  (cvzbv-v-subtracter t (nat-to-v 0 (len a)) a))

(defun cvzbv-v-not (a)
  (declare (xargs :guard t))
  (cvzbv nil nil (v-not a)))

(defun cvzbv-v-asr (a)
  (declare (xargs :guard (true-listp a)))
  (cvzbv (if (consp a) (nth 0 a) nil)
         nil
         (v-asr a)))

(defun cvzbv-v-lsr (a)
  (declare (xargs :guard (true-listp a)))
  (cvzbv (if (listp a) (nth 0 a) nil)
         nil
         (v-lsr a)))

;; V-ALU c a b op
;; The programmer's view of the ALU

(defun v-alu (c a b op)
  (declare (xargs :guard (and (consp a)
                              (true-listp a)
                              (consp b)
                              (true-listp b))))
  (cond ((equal op *v0000*) (cvzbv nil nil (v-buf a)))
        ((equal op *v0001*) (cvzbv-inc a))
        ((equal op *v0010*) (cvzbv-v-adder c a b))
        ((equal op *v0011*) (cvzbv-v-adder nil a b))
        ((equal op *v0100*) (cvzbv-neg a))
        ((equal op *v0101*) (cvzbv-dec a))
        ((equal op *v0110*) (cvzbv-v-subtracter c a b))
        ((equal op *v0111*) (cvzbv-v-subtracter nil a b))
        ((equal op *v1000*) (cvzbv-v-ror c a))
        ((equal op *v1001*) (cvzbv-v-asr a))
        ((equal op *v1010*) (cvzbv-v-lsr a))
        ((equal op *v1011*) (cvzbv nil nil (v-xor a b)))
        ((equal op *v1100*) (cvzbv nil nil (v-or  a b)))
        ((equal op *v1101*) (cvzbv nil nil (v-and a b)))
        ((equal op *v1110*) (cvzbv-v-not a))
        (t                  (cvzbv nil nil (v-buf a)))))

(defthm true-listp-v-alu
  (true-listp (v-alu c a b op))
  :rule-classes :type-prescription)

(defthm booleanp-c-v-alu
  (implies (and (booleanp c)
                (bvp a)
                (not (equal (len a) 0)))
           (booleanp (c (v-alu c a b op))))
  :hints (("Goal" :in-theory (enable c bvp)))
  :rule-classes :type-prescription)

(defthm booleanp-v-v-alu
  (implies (and (booleanp c)
                (bvp a)
                (not (equal (len a) 0)))
           (booleanp (v (v-alu c a b op))))
  :hints (("Goal" :in-theory (enable v)))
  :rule-classes :type-prescription)

(defthm booleanp-zb-v-alu
  (booleanp (zb (v-alu c a b op)))
  :hints (("Goal" :in-theory (enable zb)))
  :rule-classes :type-prescription)

(defthm bvp-bv-v-alu
  (implies (bvp a)
           (bvp (bv (v-alu c a b op))))
  :hints (("Goal" :in-theory (enable bv)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-v-alu
  (implies (and (bvp a)
                (booleanp c)
                (not (equal (len a) 0)))
           (bvp (v-alu c a b op)))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm len-cvzbv-adder
  (equal (len (cvzbv-v-adder c a b))
         (+ 3 (len a))))

(defthm len-cvzbv-subtracter
  (equal (len (cvzbv-v-subtracter c a b))
         (+ 3 (len a))))

(defthm len-v-alu
  (implies (equal (len b) (len a))
           (equal (len (v-alu c a b op))
                  (+ 3 (len a)))))

(defthm len-bv
  (implies (<= 3 (len x))
           (equal (len (bv x))
                  (- (len x) 3)))
  :hints (("Goal" :in-theory (enable bv))))

(defthm bvp-bv
  (implies (bvp x)
           (bvp (bv x)))
  :hints (("Goal" :in-theory (enable bv bvp)))
  :rule-classes (:rewrite :type-prescription))

(in-theory (disable v-alu))

;; UNARY-OP-CODE-P op-code

;; Recognizes ALU op-codes which are unary operations on the A operand. For
;; unary ALU op-codes, the B operand is arbitrary. We also define a
;; "1-argument" version of V-ALU which is equivalent to V-ALU when the ALU
;; op-code is unary.

(defun unary-op-code-p (op-code)
  (declare (xargs :guard t))
  (or (equal op-code *v0000*)            ;Move
      (equal op-code *v0001*)            ;Inc
      (equal op-code *v0100*)            ;Neg
      (equal op-code *v0101*)            ;Dec
      (equal op-code *v1000*)            ;ROR
      (equal op-code *v1001*)            ;ASR
      (equal op-code *v1010*)            ;LSR
      (equal op-code *v1110*)            ;Not
      (equal op-code *v1111*)            ;Move-15
      ))

(defthm booleanp-unary-op-code-p
  (booleanp (unary-op-code-p op-code))
  :rule-classes :type-prescription)

(in-theory (disable unary-op-code-p))

;; V-ALU-1 op-code
;; The 1-arg ALU

(defun v-alu-1 (c a op-code)
  (declare (xargs :guard (and (consp a)
                              (true-listp a))))
  (v-alu c a a op-code))

(defthm bvp-v-alu-1
  (implies (and (bvp a)
                (booleanp c)
                (not (equal (len a) 0)))
           (bvp (v-alu-1 c a op)))
  :rule-classes (:rewrite :type-prescription))

(defthm len-v-alu-1
  (equal (len (v-alu-1 c a op))
         (+ 3 (len a))))

(defthmd unary-op-code-p->v-alu=v-alu-1
  (implies (unary-op-code-p op-code)
           (equal (v-alu c a b op-code)
                  (v-alu-1 c a op-code)))
  :hints (("Goal" :in-theory (enable unary-op-code-p v-alu))))

(in-theory (disable v-alu-1))

;; ALU-INC-OP
;; ALU-DEC-OP

;; These abbreviations are used for those cases where the processor ALU is used
;; for register pre-decrement and post-increment operations.

(defun alu-inc-op ()
  (declare (xargs :guard t))
  *v0001*)

(defthm bvp-alu-inc-op
  (bvp (alu-inc-op))
  :rule-classes (:rewrite :type-prescription))

(defthm len-alu-inc-op
  (equal (len (alu-inc-op)) 4))

(defthm bv-v-alu-alu-inc-op
  (equal (bv (v-alu c a b (alu-inc-op)))
         (v-inc a))
  :hints (("Goal" :in-theory (enable bv v-alu v-inc))))

(in-theory (disable alu-inc-op))

(defun alu-dec-op ()
  (declare (xargs :guard t))
  *v0101*)

(defthm bvp-alu-dec-op
  (bvp (alu-dec-op))
  :rule-classes (:rewrite :type-prescription))

(defthm len-alu-dec-op
  (equal (len (alu-dec-op)) 4))

(defthm bv-v-alu-alu-dec-op
  (equal (bv (v-alu c a b (alu-dec-op)))
         (v-dec a))
  :hints (("Goal" :in-theory (enable bv v-alu v-dec))))

(in-theory (disable alu-dec-op))

