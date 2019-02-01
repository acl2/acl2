;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau (derived from the FM9001 work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; The ACL2 source code for the FM9001 work is available at
;; https://github.com/acl2/acl2/tree/master/books/projects/fm9001.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; January 2019

(in-package "ADE")

(local (include-book "utils"))

;; ======================================================================

(defthmd list-rewrite-1
   (implies (and (equal (len x) 1)
                 (true-listp x))
            (equal (list (car x)) x)))

(defthmd list-rewrite-2
  (implies (and (equal (len x) 2)
                (true-listp x))
           (equal (list (car x) (cadr x))
                  x)))

(defthmd list-rewrite-4
  (implies (and (equal (len x) 4)
                (true-listp x))
           (equal (list (car x) (cadr x) (caddr x) (cadddr x))
                  x)))

(defthmd list-rewrite-5
  (implies (and (equal (len x) 5)
                (true-listp x))
           (equal (list (nth 0 x)
                        (nth 1 x)
                        (nth 2 x)
                        (nth 3 x)
                        (nth 4 x))
                  x))
  :hints (("Goal" :in-theory (enable open-nth))))

(defthmd list-rewrite-10
  (implies (and (equal (len x) 10)
                (true-listp x))
           (equal (list (nth 0 x)
                        (nth 1 x)
                        (nth 2 x)
                        (nth 3 x)
                        (nth 4 x)
                        (nth 5 x)
                        (nth 6 x)
                        (nth 7 x)
                        (nth 8 x)
                        (nth 9 x))
                  x))
  :hints (("Goal" :in-theory (enable open-nth))))

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
