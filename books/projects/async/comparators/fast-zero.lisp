;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau (derived from the FM9001 verification work of Brock
;; and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; January 2018

;; A zero detector optimized for quick detection of the last 2 bits of the
;; input vector.  It should save a few nanoseconds in the FM9001.

;; LSI Logic timing analysis of the final design showed that this "fast"
;; zero-detector was about the same as simple, fully-balanced zero-detectors
;; defined in "t-or-nor.lisp".

(in-package "ADE")

(include-book "t-or-nor")

;; ======================================================================

(defun f$fast-zero (v)
  (f-nor3 (tr-or-nor (take (- (len v) 2) v)
                     nil
                     (make-tree (- (len v) 2)))
          (nth (- (len v) 2) v)
          (nth (1- (len v)) v)))

(defthm f$fast-zero-of-v-threefix-canceled
  (equal (f$fast-zero (v-threefix v))
         (f$fast-zero v)))

(defthm f$fast-zero=tr-or-nor
  (implies (>= (len v) 3)
           (equal (f$fast-zero v)
                  (tr-or-nor v t (cons (make-tree (- (len v) 2))
                                       (cons 0 0)))))
  :hints (("Goal" :in-theory (enable tr-or-nor f-nor3 f-nor
                                     car-nthcdr cdr-nthcdr))))

(defthm f$fast-zero=v-zp
  (implies (and (bvp v)
                (>= (len v) 3))
           (equal (f$fast-zero v)
                  (v-zp v)))
  :hints (("Goal" :in-theory (enable tree-size))))

(in-theory (disable f$fast-zero))

;; Hardware

(module-generator
 fast-zero* (n)
 (si 'fast-zero n)
 (sis 'a 0 n)
 '(z)
 nil
 (list
  (list 'front '(zfront) (si 't-or (tree-number (make-tree (1- (1- n)))))
        (take (- n 2) (sis 'a 0 n)))
  (list 'result '(z) 'b-nor3
        (list 'zfront (si 'a (- n 2)) (si 'a (1- n)))))
 :guard (and (natp n) (<= 2 n)))

(defund fast-zero& (netlist n)
  (declare (xargs :guard (and (alistp netlist)
                              (natp n)
                              (<= 2 n))))
  (and (equal (assoc (si 'fast-zero n) netlist)
              (fast-zero* n))
       (let ((netlist (delete-to-eq (si 'fast-zero n) netlist)))
         (t-or-nor& netlist (make-tree (- n 2)) nil))))

(defun fast-zero$netlist (n)
  (declare (xargs :guard (and (natp n)
                              (<= 2 n))))
  (cons (fast-zero* n)
        (t-or-nor$netlist (make-tree (- n 2)) nil)))

(defthm check-fast-zero$netlist-5
  (fast-zero& (fast-zero$netlist 5) 5))

(not-primp-lemma fast-zero)

(defthmd fast-zero$value
  (implies (and (fast-zero& netlist n)
                (equal (len v) n)
                (>= n 3))
           (equal (se (si 'fast-zero n) v sts netlist)
                  (list (f$fast-zero v))))
  :hints (("Goal"
           :do-not '(preprocess)
           :expand (se (si 'fast-zero n) v sts netlist)
           :in-theory (e/d (de-rules
                            fast-zero&
                            fast-zero*$destructure
                            not-primp-fast-zero
                            tr-or-nor
                            f-nor3
                            f-nor
                            car-nthcdr
                            cdr-nthcdr
                            t-or-nor$value)
                           (de-module-disabled-rules)))))

(in-theory (disable f$fast-zero=tr-or-nor))


