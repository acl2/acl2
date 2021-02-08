;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

;; CORE-ALU is the hardware implementation of the high-level specification
;; V-ALU.  In addition to the functions provided by V-ALU, CORE-ALU also can be
;; forced to 0, and includes INC B and DEC B operations for address
;; calculations.  Note that the control lines for the function generators (MPG)
;; are supplied by the control logic.
;;;
;; Since CORE-ALU is defined in terms of F$FAST-ZERO, only ALU sizes of >= 3
;; bits have the desired properties.

(in-package "FM9001")

(include-book "fast-zero")
(include-book "post-alu")
(include-book "pre-alu")
(include-book "tv-alu-help")

(local (include-book "list-rewrites"))

;; ======================================================================

(defun f$core-alu (c a b zero mpg op tree)
  (let ((op0 (car op))
        (op1 (cadr op))
        (op2 (caddr op))
        (op3 (cadddr op)))
    (let ((last-bit (1- (len a))))
      (let ((alu-help (f$tv-alu-help c a b mpg tree)))
        (let ((alu-p   (car alu-help))
              (alu-g   (cadr alu-help))
              (alu-sum (cddr alu-help)))
          (let ((alu-carry (f$t-carry c alu-p alu-g))
                (out (f$shift-or-buf c alu-sum (nth (1- (len a)) a)
                                     zero op0 op1 op2 op3)))
            (cons (f$carry-out-help (nth 0 a) alu-carry zero op0 op1 op2 op3)
                  (cons (f$overflow-help (nth last-bit alu-sum)
                                         (nth last-bit a)
                                         (nth last-bit b)
                                         zero op0 op1 op2 op3)
                        (cons (f$fast-zero out)
                              out)))))))))

(defthm len-f$core-alu
  (equal (len (f$core-alu c a b zero mpg op tree))
         (+ 3 (tree-size tree))))

(defun core-alu (c a b zero mpg op tree)
  (declare (xargs :guard (and (true-listp a)
                              (consp a)
                              (true-listp b)
                              (true-listp mpg)
                              (true-listp op))))
  (let ((op0 (car op))
        (op1 (cadr op))
        (op2 (caddr op))
        (op3 (cadddr op)))
    (let ((last-bit (1- (len a))))
      (let ((alu-help (tv-alu-help c a b mpg tree)))
        (let ((alu-p   (car alu-help))
              (alu-g   (cadr alu-help))
              (alu-sum (cddr alu-help)))
          (let ((alu-carry (t-carry c alu-p alu-g))
                (out (shift-or-buf c alu-sum (nth (1- (len a)) a)
                                   zero op0 op1 op2 op3)))
            (cons (carry-out-help (nth 0 a) alu-carry zero op0 op1 op2 op3)
                  (cons (overflow-help (nth last-bit alu-sum)
                                       (nth last-bit a)
                                       (nth last-bit b)
                                       zero op0 op1 op2 op3)
                        (cons (v-zp out)
                              out)))))))))

(defthm f$core-alu=core-alu
  (implies (and (booleanp c)
                (bvp a) (equal (len a) (tree-size tree))
                (bvp b) (equal (len b) (tree-size tree))
                (>= (len a) 3)
                (booleanp zero)
                (bvp mpg)
                (bvp op))
           (equal (f$core-alu c a b zero mpg op tree)
                  (core-alu c a b zero mpg op tree)))
  :hints (("Goal"
           :use (bvp-tv-alu-help
                 len-tv-alu-help)
           :in-theory (e/d (bvp
                            tree-size)
                           (bvp-tv-alu-help
                            len-tv-alu-help)))))

(in-theory (disable f$core-alu))

(defthm len-core-alu
  (equal (len (core-alu c a b zero mpg op tree))
         (+ 3 (tree-size tree))))

(defthm bvp-core-alu
  (bvp (core-alu c a b zero mpg op tree))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-c-core-alu
  (booleanp (c (core-alu c a b zero mpg op tree)))
  :hints (("Goal" :in-theory (enable c)))
  :rule-classes :type-prescription)

(defthm booleanp-v-core-alu
  (booleanp (v (core-alu c a b zero mpg op tree)))
  :hints (("Goal" :in-theory (enable v)))
  :rule-classes :type-prescription)

(defthm booleanp-zp-core-alu
  (booleanp (zp (core-alu c a b zero mpg op tree)))
  :hints (("Goal" :in-theory (enable zp)))
  :rule-classes :type-prescription)

(defthm booleanp-bv-core-alu
  (bvp (bv (core-alu c a b zero mpg op tree)))
  :hints (("Goal" :in-theory (enable bv)))
  :rule-classes (:rewrite :type-prescription))

(defthm nth-v-not-alt
  (implies (and (<= 0 n)
                (< n (len l))
                (bvp l))
           (equal (nth n (v-not l))
                  (b-not (nth n l))))
  :hints (("Goal" :in-theory (enable bvp v-not))))

(defthmd core-alu-works-for-all-normal-cases
  (and

   (implies
    (and (bv2p a b)
         (equal (len a) (tree-size tree))
         (booleanp c))
    (equal (v-alu c a b *v0000*)
           (core-alu (carry-in-help (cons c (cons nil *v0000*)))
                     a b nil (mpg *v000000*) *v0000* tree)))

   (implies
    (and (bv2p a b)
         (equal (len a) (tree-size tree))
         (booleanp c))
    (equal (v-alu c a b *v0001*)
           (core-alu (carry-in-help (cons c (cons nil *v0001*)))
                     a b nil (mpg *v000100*) *v0001* tree)))

   (implies
    (and (bv2p a b)
         (equal (len a) (tree-size tree))
         (booleanp c))
    (equal (v-alu c a b *v0010*)
           (core-alu (carry-in-help (cons c (cons nil *v0010*)))
                     a b nil (mpg *v001000*) *v0010* tree)))

   (implies
    (and (bv2p a b)
         (equal (len a) (tree-size tree))
         (booleanp c))
    (equal (v-alu c a b *v0011*)
           (core-alu (carry-in-help (cons c (cons nil *v0011*)))
                     a b nil (mpg *v001100*) *v0011* tree)))

   (implies
    (and (bv2p a b)
         (equal (len a) (tree-size tree))
         (booleanp c))
    (equal (v-alu c a b *v0100*)
           (core-alu (carry-in-help (cons c (cons nil *v0100*)))
                     a b nil (mpg *v010000*) *v0100* tree)))

   (implies
    (and (bv2p a b)
         (equal (len a) (tree-size tree))
         (booleanp c))
    (equal (v-alu c a b *v0101*)
           (core-alu (carry-in-help (cons c (cons nil *v0101*)))
                     a b nil (mpg *v010100*) *v0101* tree)))

   (implies
    (and (bv2p a b)
         (equal (len a) (tree-size tree))
         (booleanp c))
    (equal (v-alu c a b *v0110*)
           (core-alu (carry-in-help (cons c (cons nil *v0110*)))
                     a b nil (mpg *v011000*) *v0110* tree)))

   (implies
    (and (bv2p a b)
         (equal (len a) (tree-size tree))
         (booleanp c))
    (equal (v-alu c a b *v0111*)
           (core-alu (carry-in-help (cons c (cons nil *v0111*)))
                     a b nil (mpg *v011100*) *v0111* tree)))

   (implies
    (and (bv2p a b)
         (equal (len a) (tree-size tree))
         (booleanp c))
    (equal (v-alu c a b *v1000*)
           (core-alu (carry-in-help (cons c (cons nil *v1000*)))
                     a b nil (mpg *v100000*) *v1000* tree)))

   (implies
    (and (bv2p a b)
         (equal (len a) (tree-size tree))
         (booleanp c))
    (equal (v-alu c a b *v1001*)
           (core-alu (carry-in-help (cons c (cons nil *v1001*)))
                     a b nil (mpg *v100100*) *v1001* tree)))

   (implies
    (and (bv2p a b)
         (equal (len a) (tree-size tree))
         (booleanp c))
    (equal (v-alu c a b *v1010*)
           (core-alu (carry-in-help (cons c (cons nil *v1010*)))
                     a b nil (mpg *v101000*) *v1010* tree)))

   ;; The one below breaks with the new CARRY-OUT-HELP.
   (implies
    (and (bv2p a b)
         (equal (len a) (tree-size tree))
         (booleanp c))
    (equal (v-alu c a b *v1011*)
           (core-alu (carry-in-help (cons c (cons nil *v1011*)))
                     a b nil (mpg *v101100*) *v1011* tree)))

   (implies
    (and (bv2p a b)
         (equal (len a) (tree-size tree))
         (booleanp c))
    (equal (v-alu c a b *v1100*)
           (core-alu (carry-in-help (cons c (cons nil *v1100*)))
                     a b nil (mpg *v110000*) *v1100* tree)))

   (implies
    (and (bv2p a b)
         (equal (len a) (tree-size tree))
         (booleanp c))
    (equal (v-alu c a b *v1101*)
           (core-alu (carry-in-help (cons c (cons nil *v1101*)))
                     a b nil (mpg *v110100*) *v1101* tree)))

   (implies
    (and (bv2p a b)
         (equal (len a) (tree-size tree))
         (booleanp c))
    (equal (v-alu c a b *v1110*)
           (core-alu (carry-in-help (cons c (cons nil *v1110*)))
                     a b nil (mpg *v111000*) *v1110* tree)))

   (implies
    (and (bv2p a b)
         (equal (len a) (tree-size tree))
         (booleanp c))
    (equal (v-alu c a b *v1111*)
           (core-alu (carry-in-help (cons c (cons nil *v1111*)))
                     a b nil (mpg *v111100*) *v1111* tree))))
  :hints (("Goal"
           :in-theory (enable v-alu
                              carry-in-help
                              overflow-help
                              carry-out-help
                              tv-alu-help-tv-neg-works
                              tv-alu-help-v-and-works
                              tv-alu-help-v-or-works
                              tv-alu-help-v-xor-works
                              tv-alu-help-v-not-works
                              tv-alu-help-v-buf-works
                              tv-alu-help-tv-adder-works
                              tv-alu-help-tv-subtracter-works
                              tv-alu-help-tv-inc-a-works
                              tv-alu-help-tv-dec-a-works
                              tv-alu-help-tv-neg-works
                              tv-adder-as-p-g-sum))))

(defthm cases-on-a-4-bit-bvp
  (implies (and (bvp op)
                (equal (len op) 4)
                (cond ((equal op *v0000*) p)
                      ((equal op *v0001*) p)
                      ((equal op *v0010*) p)
                      ((equal op *v0011*) p)
                      ((equal op *v0100*) p)
                      ((equal op *v0101*) p)
                      ((equal op *v0110*) p)
                      ((equal op *v0111*) p)
                      ((equal op *v1000*) p)
                      ((equal op *v1001*) p)
                      ((equal op *v1010*) p)
                      ((equal op *v1011*) p)
                      ((equal op *v1100*) p)
                      ((equal op *v1101*) p)
                      ((equal op *v1110*) p)
                      ((equal op *v1111*) p)
                      (t t)))
           p)
  :hints (("Goal"
           :use (:instance equal-len-4-as-collected-nth
                           (l op))
           :in-theory (enable bvp)))
  :rule-classes nil)

(defthm core-alu-is-v-alu
  (implies (and (bv2p a b)
                (equal (len a) (tree-size tree))
                (bvp op)
                (equal (len op) 4)
                (not zero)
                (equal mpg (mpg (cons zero (cons nil op))))
                (booleanp c))
           (equal (core-alu (carry-in-help (cons c (cons nil op)))
                            a b zero mpg op tree)
                  (v-alu c a b op)))
  :hints (("Goal"
           :use (:instance cases-on-a-4-bit-bvp
                           (p (equal (core-alu (carry-in-help (cons c (cons nil op)))
                                               a b zero mpg op tree)
                                     (v-alu c a b op))))
           :in-theory (e/d (core-alu-works-for-all-normal-cases)
                           (core-alu)))))

(defthm core-alu-works-for-zero-case
  (implies (and (equal (len a) (tree-size tree))
                zero)
           (equal (core-alu t a b zero *v1000000* op tree)
                  (cvzbv nil nil (make-list (len a)))))
  :hints (("Goal" :in-theory (enable tv-alu-help-zero
                                     overflow-help
                                     carry-out-help))))

(defthm core-alu-works-as-inc-b
  (implies (and (bv2p a b)
                (equal (len a) (tree-size tree))
                (not zero)
                swap)
           (equal (bv (core-alu (carry-in-help
                                 (cons c (cons zero (alu-inc-op))))
                                a b zero
                                (mpg (cons zero (cons swap (alu-inc-op))))
                                (alu-inc-op) tree))
                  (v-inc b)))
  :hints (("Goal" :in-theory (enable alu-inc-op v-inc bv mpg
                                     carry-in-help
                                     decode-gen
                                     decode-prop
                                     tv-alu-help-tv-inc-b-works
                                     tv-adder-as-p-g-sum))))

(defthm core-alu-works-as-dec-b
  (implies (and (bv2p a b)
                (equal (len a) (tree-size tree))
                (not zero)
                swap)
           (equal (bv (core-alu (carry-in-help (cons c (cons zero (alu-dec-op))))
                                a b zero
                                (mpg (cons zero (cons swap (alu-dec-op))))
                                (alu-dec-op) tree))
                  (v-dec b)))
  :hints (("Goal" :in-theory (enable alu-dec-op v-dec bv mpg
                                     carry-in-help
                                     decode-gen
                                     decode-prop
                                     tv-alu-help-tv-dec-b-works
                                     tv-adder-as-p-g-sum))))

(in-theory (disable core-alu))

;; ======================================================================

;; CORE-ALU*

(destructuring-lemma
 core-alu* (tree)
 (declare (xargs :guard t))
 ;; Bindings
 ((a-names       (sis 'a 0 (tree-size tree)))
  (b-names       (sis 'b 0 (tree-size tree)))
  (mpg-names     (sis 'mpg 0 7))
  (op-names      (sis 'op 0 4))
  (alu-out-names (sis 'alu-out 0 (tree-size tree)))
  (out-names     (sis 'out 0 (tree-size tree)))
  (last-a        (si 'a (1- (tree-size tree))))
  (last-b        (si 'b (1- (tree-size tree))))
  (last-alu-out  (si 'alu-out (1- (tree-size tree)))))
 ;; Name
 (si 'core-alu (tree-number tree))
 ;;  Inputs
 (cons 'c (append a-names (append b-names
                                  (cons 'zero
                                        (append mpg-names op-names)))))
 ;; Outputs
 (cons 'carry (cons 'overflow (cons 'zerop out-names)))
 ;; States
 nil
 ;; Body
 (list
  (list 'm-alu
        (cons 'p (cons 'g alu-out-names))
        (si 'tv-alu-help (tree-number tree))
        (cons 'c (append a-names (append b-names mpg-names))))
  (list 'm-alu-carry
        '(alu-carry)
        't-carry
        '(c p g))
  (list 'm-carry-out-help
        '(carry)
        'carry-out-help
        (cons (si 'a 0)
              (list 'alu-carry 'zero
                    (si 'op 0) (si 'op 1) (si 'op 2) (si 'op 3))))
  (list 'm-overflow-help
        '(overflow)
        'overflow-help
        (list last-alu-out last-a last-b 'zero
              (si 'op 0) (si 'op 1) (si 'op 2) (si 'op 3)))
  (list 'm-shift
        out-names
        (si 'tv-shift-or-buf (tree-number tree))
        (cons 'c (append alu-out-names
                         (list last-a 'zero
                               (si 'op 0) (si 'op 1)
                               (si 'op 2) (si 'op 3)))))
  (list 'm-zerop
        '(zerop)
        (si 'fast-zero (tree-size tree))
        out-names)))

(defund core-alu& (netlist tree)
  (and (equal (assoc (si 'core-alu (tree-number tree)) netlist)
              (core-alu* tree))
       (let ((netlist
              (delete-to-eq (si 'core-alu (tree-number tree)) netlist)))
         (and (tv-alu-help&     netlist tree)
              (t-carry&         netlist)
              (carry-out-help&  netlist)
              (overflow-help&   netlist)
              (tv-shift-or-buf& netlist tree)
              (fast-zero&       netlist (tree-size tree))))))

(defun core-alu$netlist (tree)
  (cons
   (core-alu* tree)
   (union$ (tv-alu-help$netlist tree)
           *t-carry*
           *carry-out-help*
           *overflow-help*
           (tv-shift-or-buf$netlist tree)
           (fast-zero$netlist (tree-size tree))
           :test 'equal)))

(not-primp-lemma core-alu)

(defthmd core-alu$value
  (implies (and (core-alu& netlist tree)
                (equal (len a) (tree-size tree))
                (equal (len b) (tree-size tree))
                (>= (len a) 3)
                (true-listp a) (true-listp b)
                (true-listp op) (equal (len op) 4)
                (true-listp mpg) (equal (len mpg) 7))
           (equal (se (si 'core-alu (tree-number tree))
                      (cons c (append a (append b (cons zero
                                                        (append mpg op)))))
                      sts netlist)
                  (f$core-alu c a b zero mpg op tree)))
  :hints (("Goal"
           :in-theory (e/d (se-rules
                             core-alu&
                             core-alu*$destructure
                             not-primp-core-alu
                             tv-alu-help$value
                             t-carry$value
                             carry-out-help$value
                             overflow-help$value
                             tv-shift-or-buf$value
                             fast-zero$value
                             f$core-alu)
                            ((si)
                             (sis)
                             tv-disabled-rules)))))


