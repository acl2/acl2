;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

;; CARRY and OVERFLOW help, and TV-SHIFT-OR-BUF.

(in-package "FM9001")

(include-book "macros")
(include-book "tv-if")

;; ======================================================================

;; CARRY-OUT-HELP

(fn-to-module
 carry-out-help
 (a0 result zero op0 op1 op2 op3)
 (declare (xargs :guard t))
 (let ((result- (b-not result))
       (zero-   (b-not zero))
       (op0-    (b-not op0))
       (op1-    (b-not op1))
       (op2-    (b-not op2))
       (op3-    (b-not op3)))
   (let ((op0    (b-not op0-))
         (op1    (b-not op1-))
         (op2    (b-not op2-))
         (op3    (b-not op3-)))

     (b-and (b-nand3 (b-nand4 op3- (b-nand op0- op1-) op2- result)
                     (b-nand3 op3- op2 result-)
                     (b-nand4 op3 op2- (b-nand op0 op1) a0))
            zero-))))

(defthm carry-out-help-congruence
  (implies x
           (equal (equal (carry-out-help x a zero op0 op1 op2 op3)
                         (carry-out-help t a zero op0 op1 op2 op3))
                  t))
  :hints (("Goal" :in-theory (enable carry-out-help))))

(defthmd carry-out-help$value-zero
  (implies (carry-out-help& netlist)
           (equal (se 'carry-out-help
                      (list a0 result t op0 op1 op2 op3)
                      sts netlist)
                  (list nil)))
  :hints (("Goal" :in-theory (enable carry-out-help$value
                                     f$carry-out-help))))

;; OVERFLOW-HELP

;; This logic is optimized for speed on the basis that RN will arrive last.

(fn-to-module
 overflow-help
 (rn an bn zero op0 op1 op2 op3)
 (declare (xargs :guard t))
 (let ((an-   (b-not an))
       (zero- (b-not zero))
       (op1-  (b-not op1))
       (op2-  (b-not op2))
       (op3-  (b-not op3)))
   (let ((an   (b-not an-))
         ;;(zero (b-not zero-))
         (op2  (b-not op2-)))
     (b-if rn
           (b-nor (b-nand (b-nor (b-nand3 op3-
                                          (b-or3 op1- op2- (b-xor an bn))
                                          (b-nand3 op1- op2 an-))
                                 (b-nand (b-nand3 op1 op2- (b-xor an bn))
                                         (b-nand3 op1- op2- an)))
                          zero-)
                  (b-nand3 (b-nand op2 an-)
                           (b-nand3 op0 op1- an)
                           (b-nand op2- an)))
           (b-nor (b-nand (b-nor (b-nand3 op3-
                                          (b-or3 op1- op2- (b-xor an bn))
                                          (b-nand3 op1- op2 an-))
                                 (b-nand (b-nand3 op1 op2- (b-xor an bn))
                                         (b-nand3 op1- op2- an)))
                          zero-)
                  (b-not (b-nand3 (b-nand op2 an-)
                                  (b-nand3 op0 op1- an)
                                  (b-nand op2- an))))))))

(defthmd overflow-help$value-zero
  (implies (and (overflow-help& netlist)
                (booleanp rn))
           (equal (se 'overflow-help
                      (list rn an bn t op0 op1 op2 op3)
                      sts netlist)
                  (list nil)))
  :hints (("Goal" :in-theory (enable overflow-help$value
                                      f$overflow-help
                                      f-gates))))

;; ======================================================================

;; THE SHIFT UNIT

;; V-SHIFT-RIGHT-NAMES -- Like V-SHIFT-RIGHT, but doesn't BOOL-FIX the vector.
;; Used to create a "shifted" list of names to be used as the shifted input to
;; the shift mutiplexor.

(defun v-shift-right-names (a si)
  (declare (xargs :guard (true-listp a)))
  (if (atom a)
      nil
    (append (cdr a) (list si))))

(defthm len-v-shift-right-names
  (equal (len (v-shift-right-names a si))
         (len a)))

;; (defthm true-listp-v-shift-right-names
;;   (true-listp (v-shift-right-names a si))
;;   :rule-classes :type-prescription)

(defthm assoc-eq-values-v-shift-right
  (equal (v-threefix (assoc-eq-values (v-shift-right-names a si) alist))
         (fv-shift-right (assoc-eq-values a alist)
                         (assoc-eq-value si alist)))
  :hints (("Goal" :in-theory (enable v-threefix-append
                                     fv-shift-right))))

;;  SHIFT-OR-BUF-CNTL

(fn-to-module
 shift-or-buf-cntl
 (c an zero op0 op1 op2 op3)
 (declare (xargs :guard t))
 (let ((op0- (b-not op0))
       (op1- (b-not op1))
       (op2- (b-not op2)))
   (let ((decode-ror (b-and op0- op1-))
         (decode-asr op0))
     (let ((ror-si (b-and decode-ror c))
           (asr-si (b-and decode-asr an)))
       (b* ((si (b-or asr-si ror-si))
            (t1 (b-nand op2- op3))
            (t2 (b-and op0 op1))
            (x  (b-or3 t2 t1 zero)))
         (list x si))))))

(defthmd shift-or-buf-cntl$value-zero
  (implies (shift-or-buf-cntl& netlist)
           (equal (car (se 'shift-or-buf-cntl
                           (list c an t op0 op1 op2 op3)
                           sts netlist))
                  t))
  :hints (("Goal" :in-theory (enable shift-or-buf-cntl$value
                                      f$shift-or-buf-cntl
                                      f-gates))))

(defun f$shift-or-buf (c a an zero op0 op1 op2 op3)
  (declare (xargs :guard (true-listp a)))
  (let ((pass (car (f$shift-or-buf-cntl c an zero op0 op1 op2 op3)))
        (si   (cadr (f$shift-or-buf-cntl c an zero op0 op1 op2 op3))))
    (fv-if pass a (fv-shift-right a si))))

;; (defthm true-listp-f$shift-or-buf
;;   (true-listp (f$shift-or-buf c a an zero op0 op1 op2 op3))
;;   :rule-classes :type-prescription)

(defthm len-f$shift-or-buf
  (equal (len (f$shift-or-buf c a an zero op0 op1 op2 op3))
         (len a)))

(defun shift-or-buf (c a an zero op0 op1 op2 op3)
  (declare (xargs :guard (true-listp a)))
  (let ((pass (car (shift-or-buf-cntl c an zero op0 op1 op2 op3)))
        (si   (cadr (shift-or-buf-cntl c an zero op0 op1 op2 op3))))
    (v-if pass a (v-shift-right a si))))

(defthm len-shift-or-buf
  (equal (len (shift-or-buf c a an zero op1 op2 op3 op4))
         (len a)))

(defthm bvp-shift-or-buf
  (bvp (shift-or-buf c a an zero op1 op2 op3 op4))
  :rule-classes (:rewrite :type-prescription))

(defthm f$shift-or-buf=shift-or-buf
  (implies (and (booleanp c)
                (booleanp an)
                (booleanp zero)
                (booleanp op1)
                (booleanp op2)
                (booleanp op3)
                (booleanp op4)
                (bvp a))
           (equal (f$shift-or-buf c a an zero op1 op2 op3 op4)
                  (shift-or-buf c a an zero op1 op2 op3 op4)))
  :hints (("Goal" :in-theory (enable shift-or-buf-cntl))))

(in-theory (disable f$shift-or-buf))

;; Lemmas about the shift unit.

(defthm shift-or-buf-is-buf
  (implies (and (bvp a)
                (or (and op0 op1)
                    op2
                    (not op3)
                    zero))
           (equal (shift-or-buf c a an zero op0 op1 op2 op3)
                  a))
  :hints (("Goal" :in-theory (enable shift-or-buf-cntl))))

(defthm shift-or-buf-is-asr
  (implies (and (bvp a)
                (equal an (nth (1- (len a)) a))
                op0
                (not op1)
                (not op2)
                op3
                (not zero))
           (equal (shift-or-buf c a an zero op0 op1 op2 op3)
                  (v-asr a)))
  :hints (("Goal" :in-theory (enable bvp
                                     shift-or-buf-cntl))))

(defthm shift-or-buf-is-ror
  (implies (and (bvp a)
                (booleanp c)
                (not op0)
                (not op1)
                (not op2)
                op3
                (not zero))
           (equal (shift-or-buf c a an zero op0 op1 op2 op3)
                  (v-ror a c)))
  :hints (("Goal" :in-theory (enable shift-or-buf-cntl))))

(defthm shift-or-buf-is-lsr
  (implies (and (bvp a)
                (not op0)
                op1
                (not op2)
                op3
                (not zero))
           (equal (shift-or-buf c a an zero op0 op1 op2 op3)
                  (v-lsr a)))
  :hints (("Goal" :in-theory (enable shift-or-buf-cntl))))

(in-theory (disable shift-or-buf))

;; ======================================================================

;; TV-SHIFT-OR-BUF* -- Hardware implementation of SHIFT-OR-BUF, using TV-IF
;; for the selector.

(destructuring-lemma
 tv-shift-or-buf* (tree)
 (declare (xargs :guard t))
 ;; Bindings
 ((a-names (sis 'a 0 (tree-size tree)))
  (out-names (sis 'out 0 (tree-size tree))))
 ;; Name
 (si 'tv-shift-or-buf (tree-number tree))
 ;; Inputs
 (cons 'c (append a-names '(an zero op0 op1 op2 op3)))
 ;; Outputs
 out-names
 ;; States
 nil
 ;; Body
 (list
  '(cntl (ctl si) shift-or-buf-cntl (c an zero op0 op1 op2 op3))
  (list 'mux
        out-names
        (si 'tv-if (tree-number tree))
        (cons 'ctl (append a-names
                           (v-shift-right-names a-names 'si))))))

(defund tv-shift-or-buf& (netlist tree)
  (declare (xargs :guard (and (alistp netlist)
                              (tv-guard tree))))
  (and (equal (assoc (si 'tv-shift-or-buf (tree-number tree))
                     netlist)
              (tv-shift-or-buf* tree))
       (shift-or-buf-cntl& (delete-to-eq
                            (si 'tv-shift-or-buf (tree-number tree))
                            netlist))
       (tv-if& (delete-to-eq (si 'tv-shift-or-buf (tree-number tree))
                             netlist)
               tree)))

(defun tv-shift-or-buf$netlist (tree)
  (declare (xargs :guard (tv-guard tree)))
  (cons (tv-shift-or-buf* tree)
        (union$ (tv-if$netlist tree)
                *shift-or-buf-cntl*
                :test 'equal)))

(local
 (defthm tv-shift-or-buf$value-aux
   (implies
    (and (tv-if& (delete-to-eq (si 'tv-shift-or-buf (tree-number tree))
                               netlist)
                 tree)
         (consp a)
         (equal (+ 1 (len (cdr a)))
                (tree-size tree))
         (true-listp (cdr a))
         (consp (sis 'a 0 (tree-size tree))))
    (equal
     (assoc-eq-values
      (sis 'out 0 (tree-size tree))
      (pairlis$
       (sis 'out 0 (tree-size tree))
       (se (si 'tv-if (tree-number tree))
           (list* (f-or3 (f-and op0 op1)
                         (f-nand (f-not op2) op3)
                         zero)
                  (car a)
                  (append (cdr a)
                          (cdr a)
                          (list (f-or (f-and op0 an)
                                      (f-and (f-and (f-not op0) (f-not op1))
                                             c)))))
           nil
           (delete-to-eq (si 'tv-shift-or-buf (tree-number tree))
                         netlist))))
     (fv-if (f-or3 (f-and op0 op1)
                   (f-nand (f-not op2) op3)
                   zero)
            a
            (fv-shift-right a
                            (f-or (f-and op0 an)
                                  (f-and (f-and (f-not op0) (f-not op1))
                                         c))))))
   :hints (("Goal"
            :use (:instance tv-if$value
                            (c (f-or3 (f-and op0 op1)
                                      (f-nand (f-not op2) op3)
                                      zero))
                            (b (append (cdr a)
                                       (list (f-or (f-and op0 an)
                                                   (f-and
                                                    (f-and (f-not op0)
                                                           (f-not op1))
                                                    c)))))
                            (sts nil)
                            (netlist (delete-to-eq
                                      (si 'tv-shift-or-buf
                                          (tree-number tree))
                                      netlist)))
            :in-theory (e/d (fv-if-rewrite
                              v-threefix-append
                              v-threefix
                              fv-shift-right)
                             (tv-disabled-rules
                              append-v-threefix))))))

(not-primp-lemma tv-shift-or-buf)

(defthmd tv-shift-or-buf$value
  (implies (and (tv-shift-or-buf& netlist tree)
                (equal (len a) (tree-size tree))
                (true-listp a))
           (equal (se (si 'tv-shift-or-buf (tree-number tree))
                      (cons c (append a (list an zero op0 op1 op2 op3)))
                      sts netlist)
                  (f$shift-or-buf c a an zero op0 op1 op2 op3)))
  :hints (("Goal"
           :in-theory (e/d (se-rules
                             tv-shift-or-buf&
                             tv-shift-or-buf*$destructure
                             not-primp-tv-shift-or-buf
                             tv-if$value
                             shift-or-buf-cntl$value
                             f$shift-or-buf
                             f$shift-or-buf-cntl)
                            (tv-disabled-rules)))))

(defthmd tv-shift-or-buf$value-zero
  (implies (and (tv-shift-or-buf& netlist tree)
                (equal (len a) (tree-size tree))
                (bvp a))
           (equal (se (si 'tv-shift-or-buf (tree-number tree))
                      (cons c (append a (list an t op0 op1 op2 op3)))
                      sts netlist)
                  a))
  :hints (("Goal" :in-theory (enable tv-shift-or-buf$value
                                      f$shift-or-buf
                                      f$shift-or-buf-cntl
                                      f-gates
                                      fv-shift-right
                                      fv-if-rewrite))))
