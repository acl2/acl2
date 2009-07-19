#|
; Certification instructions:
(certify-book "perm")
JSM June, 2000
|#

(in-package "ACL2")

(defun del (x y)
  (if (consp y)
      (if (equal x (car y))
	  (cdr y)
	(cons (car y) (del x (cdr y))))
    y))

(defun mem (e x)
  (if (consp x)
      (or (equal e (car x))
          (mem e (cdr x)))
      nil))

(defun perm (x y)
  (if (consp x)
      (and (mem (car x) y)
           (perm (cdr x) (del (car x) y)))
      (not (consp y))))

; The following could be proved right now.
; (local
;  (defthm perm-reflexive
;    (perm x x)))

(local
 (defthm perm-cons
   (implies (mem a x)
            (equal (perm x (cons a y))
                   (perm (del a x) y)))
   :hints (("Goal" :induct (perm x y)))))

(local
 (defthm perm-symmetric
   (implies (perm x y) (perm y x))))

(local
 (defthm mem-del
   (implies (mem a (del b x)) (mem a x))))

(local
 (defthm perm-mem
   (implies (and (perm x y)
                 (mem a x))
            (mem a y))))

(local
 (defthm comm-del
   (equal (del a (del b x)) (del b (del a x)))))

(local
 (defthm perm-del
   (implies (perm x y)
            (perm (del a x) (del a y)))))

; We now prove this because we give a hint.

(local
 (defthm perm-transitive
   (implies (and (perm x y) (perm y z)) (perm x z))
   :hints (("Goal" :induct (and (perm x y) (perm x z))))))

(defequiv perm)

(defcong perm perm (cons x y) 2)

(defcong perm perm (append x y) 1)

(defcong perm perm (append x y) 2)

