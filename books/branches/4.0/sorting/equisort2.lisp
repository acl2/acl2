; (certify-book "equisort2")

; Suppose sortfn1 and sortfn2 are two arbitrary unary functions that return
; ordered results that preserve the how-many property for every object e.  Then
; they are equal.

; I constrain sortfn1 and sortfn2 and then prove this.  Thus, when one
; functionally instantiates sortfn1-is-sortfn2 below, replacing the two generic
; names by specific sorting functions, nice proof obligations are produced:
; each sorting function must return an ordered list that preserves the how-many
; property.

(in-package "ACL2")

(include-book "perm")
(include-book "ordered-perms")
(include-book "convert-perm-to-how-many")

(encapsulate ((sorthyp (x) t)
              (sortfn1 (x) t)
              (sortfn2 (x) t))
             (local (defun sorthyp (x) (true-listp x)))
             (local (defun sortfn1-insert (e x)
                      (if (endp x)
                          (cons e x)
                        (if (lexorder e (car x))
                            (cons e x)
                          (cons (car x)
                                (sortfn1-insert e (cdr x)))))))

             (local (defun sortfn1 (x)
                      (if (endp x)
                          nil
                        (sortfn1-insert (car x)
                                        (sortfn1 (cdr x))))))

             (local (defun sortfn2 (x) (sortfn1 x)))

             (defthm orderedp-sortfn1
               (orderedp (sortfn1 x)))

             (defthm true-listp-sortfn1
               (implies (sorthyp x)
                        (true-listp (sortfn1 x))))

             (defthm orderedp-sortfn2
               (orderedp (sortfn2 x)))

             (defthm true-listp-sortfn2
               (implies (sorthyp x)
                        (true-listp (sortfn2 x))))

             (defthm how-many-sortfn1
               (equal (how-many e (sortfn1 x))
                      (how-many e x)))

             (defthm how-many-sortfn2
               (equal (how-many e (sortfn2 x))
                      (how-many e x))))

(defthm sortfn1-is-sortfn2
  (implies (sorthyp x)
           (equal (sortfn1 x) (sortfn2 x)))
  :rule-classes nil
  :hints (("Goal" :use (:instance ordered-perms
                                  (a (sortfn1 x))
                                  (b (sortfn2 x))))))


