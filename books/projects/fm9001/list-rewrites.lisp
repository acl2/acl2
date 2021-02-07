;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

(in-package "FM9001")

(local (include-book "utils"))

;; ======================================================================

(defthmd list-rewrite-1
   (implies (and (true-listp x)
                 (equal (len x) 1))
            (equal (list (car x)) x)))

(defthmd list-rewrite-4
  (implies (and (true-listp a)
                (equal (len a) 4))
           (equal (list (car a) (cadr a) (caddr a) (cadddr a))
                  a)))

;; LIST-AS-COLLECTED-NTH

(defun list-as-collected-nth (l len n)
  (declare (xargs :guard (and (true-listp l)
                              (natp len)
                              (natp n))))
  (if (zp len)
      nil
    (cons (nth n l)
          (list-as-collected-nth l (1- len) (1+ n)))))

(defthm open-list-as-collected-nth
  (and
   (implies
    (zp len)
    (equal (list-as-collected-nth l len n)
           nil))
   (implies (not (zp len))
            (equal (list-as-collected-nth l len n)
                   (cons (nth n l)
                         (list-as-collected-nth l (1- len) (1+ n)))))))

(in-theory (disable list-as-collected-nth))

(defthmd equal-len-4-as-collected-nth
  (implies (and (equal (len l) 4)
                (true-listp l))
           (equal (list-as-collected-nth l 4 0)
                  l))
  :hints (("Goal" :in-theory (enable open-len open-nth))))

(defthmd equal-len-32-as-collected-nth
  (implies (and (equal (len l) 32)
                (true-listp l))
           (equal (list-as-collected-nth l 32 0)
                  l))
  :hints (("Goal" :in-theory (enable open-len open-nth))))
