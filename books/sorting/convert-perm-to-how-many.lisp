; (certify-book "convert-perm-to-how-many")

; See Exercise 11.50 in CAR.
; /projects/acl2/v3-1/acl2-sources/books/textbook/chap11/how-many-soln2.lisp

(in-package "ACL2")

(include-book "perm")

(include-book "how-many")

; We aim to prove that (perm x y) is the same as checking that for all e,
; (how-many e x) is (how-many e y).  We can do that by defining the function
; (perm-counter-example x y) -- the counterexample generator -- that finds an e that occurs a
; different number of times in x than in y.

; Thus, the following definition is modeled after the definition of perm.

(defun perm-counter-example (x y)
  (cond ((atom x)
         (car y))
        ((not (memb (car x) y))
         (car x))
        (t (perm-counter-example (cdr x) (rm (car x) y)))))


; The right-hand side of the equal term in the last hypothesis suggests the
; following rewrite rule.  (We return to this issue later.)

(defthm how-many-rm
  (implies (not (equal a b))
           (equal (how-many a (rm b x))
                  (how-many a x))))

(defthm not-memb-implies-rm-is-no-op
  (implies (and (not (memb a x))
                (true-listp x))
           (equal (rm a x) x)))

(defthm true-listp-rm
  (implies (true-listp x)
           (true-listp (rm a x)))
  :rule-classes :type-prescription)

(defthm not-memb-implies-how-many-is-0
  (implies (not (memb a x))
           (equal (how-many a x)
                  0)))

(defthm how-many-rm-general
  (equal (how-many a (rm b x))
         (if (and (equal a b) (memb a x))
             (1- (how-many a x))
           (how-many a x))))

(defthm perm-counter-example-is-counterexample-for-true-lists
  (implies (and (true-listp x)
                (true-listp y))
           (equal (perm x y)
                  (equal (how-many (perm-counter-example x y) x)
                         (how-many (perm-counter-example x y) y))))
  :rule-classes nil)

(defun tlfix (x)
  (if (endp x)
      nil
    (cons (car x) (tlfix (cdr x)))))

(defthm perm-tlfix
  (perm (tlfix x) x))

(defthm perm-counter-example-tlfix-1
  (equal (perm-counter-example (tlfix x) y)
         (perm-counter-example x y)))

(defthm rm-tlfix
  (equal (rm a (tlfix x))
         (tlfix (rm a x))))

(defthm memb-tlfix
  (equal (memb a (tlfix x))
         (memb a x)))

(defthm perm-counter-example-tlfix-2
  (equal (perm-counter-example x (tlfix y))
         (perm-counter-example x y)))

(defthm how-many-tlfix
  (equal (how-many a (tlfix x))
         (how-many a x)))

(defthm convert-perm-to-how-many
  (equal (perm x y)
         (equal (how-many (perm-counter-example x y) x)
                (how-many (perm-counter-example x y) y)))
  :hints (("Goal" :use
           ((:instance perm-counter-example-is-counterexample-for-true-lists
                       (x (tlfix x))
                       (y (tlfix y)))))))
