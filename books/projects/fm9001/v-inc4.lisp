;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; August 2016

;; V-INC4 -- A 4-bit incrementer.

(in-package "FM9001")

(include-book "de")
(include-book "macros")

;; ======================================================================

(fn-to-module
 v-inc4 (a0 a1 a2 a3)
 (declare (xargs :guard t))
 (b* ((a0n (b-not a0))
      (a1n (b-not a1))
      (a2n (b-not a2))
      (a3n (b-not a3))
      (c0 a0n)
      (c1 (b-nor a0n a1n))
      (c2 (b-nor3 a0n a1n a2n))
      (a1-out (b-xor a1n c0))
      (a2-out (b-equv a2n c1))
      (a3-out (b-equv a3n c2)))
   (list a0n a1-out a2-out a3-out)))

(defun f$v-inc4$v (a)
  (declare (xargs :guard (true-listp a)))
  (let ((a0 (car a))
        (a1 (cadr a))
        (a2 (caddr a))
        (a3 (cadddr a)))
    (let ((a0n (f-not a0))
          (a1n (f-not a1))
          (a2n (f-not a2))
          (a3n (f-not a3)))
      (let ((c0 a0n)
            (c1 (f-nor a0n a1n))
            (c2 (f-nor3 a0n a1n a2n)))
        (list a0n
              (f-xor a1n c0)
              (f-equv a2n c1)
              (f-equv a3n c2))))))

;; (defthm true-listp-f$v-inc4$v
;;   (true-listp (f$v-inc4$v a))
;;   :rule-classes :type-prescription)

(defthm len-f$v-inc4$v
  (equal (len (f$v-inc4$v a)) 4))

(defthm v-inc4$value-as-v-inc
  (implies (and (v-inc4& netlist)
                (true-listp a)
                (equal (len a) 4))
           (equal (se 'v-inc4 a sts netlist)
                  (f$v-inc4$v a)))
  :hints (("Goal" :in-theory (enable v-inc4$value f$v-inc4))))

(defthm f$v-inc4$v=v-inc
  (implies (and (bvp a)
                (equal (len a) 4))
           (equal (f$v-inc4$v a)
                  (v-inc a)))
  :hints (("Goal" :in-theory (enable bvp v-inc v-adder))))

(in-theory (disable f$v-inc4$v))

