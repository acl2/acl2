(in-package "ACL2")

(defun rm (e x)
  (if (consp x)
      (if (equal e (car x))
          (cdr x)
          (cons (car x) (rm e (cdr x))))
      nil))

; Matt K. mod: First parameter changed from e to a for compatibility with
; meta/term-defuns.lisp.
(defun memb (a x)
  ;; Alessandro Coglio: added guard for compatibility with meta/term-defuns.lisp
  (declare (xargs :guard t))
  (if (consp x)
      (or (equal a (car x))
          (memb a (cdr x)))
      nil))

(defun perm (x y)
  (if (consp x)
      (and (memb (car x) y)
           (perm (cdr x) (rm (car x) y)))
      (not (consp y))))

; The following could be proved right now.
; (local
;  (defthm perm-reflexive
;    (perm x x)))

(local
 (defthm perm-cons
   (implies (memb a x)
            (equal (perm x (cons a y))
                   (perm (rm a x) y)))
   :hints (("Goal" :induct (perm x y)))))

(local
 (defthm perm-symmetric
   (implies (perm x y) (perm y x))))

(local
 (defthm memb-rm
   (implies (memb a (rm b x)) (memb a x))))

(local
 (defthm perm-memb
   (implies (and (perm x y)
                 (memb a x))
            (memb a y))))

(local
 (defthm comm-rm
   (equal (rm a (rm b x)) (rm b (rm a x)))))

(local
 (defthm perm-rm
   (implies (perm x y)
            (perm (rm a x) (rm a y)))))

; We now prove this because we give a hint.

(local
 (defthm perm-transitive
   (implies (and (perm x y) (perm y z)) (perm x z))
   :hints (("Goal" :induct (and (perm x y) (perm x z))))))

(defequiv perm)
