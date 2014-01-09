#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

;; For when you want the convenience of "nth" without the annoying
;; guard overhead.

(defun ith (n list)
  (declare (type t n list))
  (if (consp list)
      (if (zp (nfix n))
	  (car list)
	(ith (1- n) (cdr list)))
    nil))

(defthm open-ith-not-zp
  (implies
   (not (zp n))
   (equal (ith n list)
	  (ith (1- n) (cdr list)))))

(defthm open-ith-consp
  (implies
   (consp list)
   (equal (ith n list)
	  (if (zp n) (car list)
	    (ith (1- n) (cdr list))))))

(defthm ith-non-increasing
  (<= (acl2-count (ith n list)) (acl2-count list))
  :rule-classes (:linear))

;; If you need other rules about ith, you might want to switch over to nth

(defthmd ith-to-nth
  (equal (ith n list)
	 (nth n list)))

