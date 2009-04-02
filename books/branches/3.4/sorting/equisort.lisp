; (certify-book "equisort")

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

(encapsulate ((sortfn1 (x) t)
              (sortfn2 (x) t))
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
               (implies (true-listp x)
                        (true-listp (sortfn1 x))))

             (defthm orderedp-sortfn2
               (orderedp (sortfn2 x)))

             (defthm true-listp-sortfn2
               (implies (true-listp x)
                        (true-listp (sortfn2 x))))

             (defthm how-many-sortfn1
               (equal (how-many e (sortfn1 x))
                      (how-many e x)))

             (defthm how-many-sortfn2
               (equal (how-many e (sortfn2 x))
                      (how-many e x))))

(defthm weak-sortfn1-is-sortfn2
  (implies (true-listp x)
           (equal (sortfn1 x) (sortfn2 x)))
  :hints (("Goal" :use (:instance ordered-perms
                                  (a (sortfn1 x))
                                  (b (sortfn2 x))))))

(encapsulate ((ssortfn1 (x) t)
              (ssortfn2 (x) t))
             (local (defun ssortfn1-insert (e x)
                      (if (endp x)
                          (cons e x)
                        (if (lexorder e (car x))
                            (cons e x)
                          (cons (car x)
                                (ssortfn1-insert e (cdr x)))))))

             (local (defun ssortfn1 (x)
                      (if (endp x)
                          nil
                        (ssortfn1-insert (car x)
                                        (ssortfn1 (cdr x))))))

             (local (defun ssortfn2 (x) (ssortfn1 x)))

             (defthm orderedp-ssortfn1
               (orderedp (ssortfn1 x)))

             (defthm true-listp-ssortfn1
               (true-listp (ssortfn1 x)))

             (defthm orderedp-ssortfn2
               (orderedp (ssortfn2 x)))

             (defthm true-listp-ssortfn2
               (true-listp (ssortfn2 x)))

             (defthm how-many-ssortfn1
               (equal (how-many e (ssortfn1 x))
                      (how-many e x)))

             (defthm how-many-ssortfn2
               (equal (how-many e (ssortfn2 x))
                      (how-many e x))))

(defthm strong-ssortfn1-is-ssortfn2
  (equal (ssortfn1 x) (ssortfn2 x))
  :hints (("Goal" :use (:instance ordered-perms
                                  (a (ssortfn1 x))
                                  (b (ssortfn2 x))))))
