; This is the demo given in Lecture 1.

; The full path below is the one I use on my laptop.  But the same material
; is at http://www.cs.utexas.edu/users/moore/publications/talks/marktoberdorf-08/scripts

; v33 is ACL2 Version 3.3

; cd to the marktoberdorf-08/scripts/ directory and then fire up ACL2

(set-gag-mode nil) ; to get full proof output, as in the original demo

(set-guard-checking nil)

(quote (end of setup))

(cons 2 nil)
(cons 1 (cons 2 nil))

(if t 1 2)
(if nil 1 2)

(nth 2 '(a b c d e))
(update-nth 2 'h '(a b c d e))

(defun app (x y)
         (if (endp x)
             y
           (cons (car x)
                 (app (cdr x) y))))

(app '(1 2 3) '(4 5 6))

(defthm app-is-associative
        (equal (app (app a b) c)
               (app a (app b c))))

(quote (End of Demo 1))

(defun insert (e x)
         (if (endp x)
             (cons e x)
           (if (lexorder e (car x))
               (cons e x)
             (cons (car x)
                   (insert e (cdr x))))))

(insert 3 '(1 2 4 5))
(insert 'bravo '(alpha charlie dog))

(defun isort (x)
         (if (endp x)
             x
           (insert (car x)
                   (isort (cdr x)))))

(isort '(5 1 3 2 4))
(isort '(charlie alpha dog bravo))

(defun orderedp (x)
         (if (endp x)
             t
           (if (endp (cdr x))
               t
             (and (lexorder (car x) (car (cdr x)))
                  (orderedp (cdr x))))))

(orderedp '(1 2 3 3 4 5))
(orderedp '(1 2 3 4 3 5))

(defthm orderedp-isort
         (orderedp (isort x)))

(defthm isort-isort
  (equal (isort (isort x)) (isort x)))

(pe 'orderedp-isort)

(defthm key-lemma
  (implies (orderedp a)
           (equal (isort a) a)))

(defthm isort-isort
  (equal (isort (isort x)) (isort x)))

(include-book "perm")

(pe 'perm)
(perm '(1 2 3) '(3 1 2))
(perm '(1 2 3) '(1 3 4))

(defthm perm-isort
         (perm (isort x) x))

(quote (end of demo 2))

; Below is a script that proves that twins is correct.  I do not plan on
; showing or discussing twins.

(defun member! (e x)
  (and (member e x)
       (not (member e (cdr (member e x))))))

(defun rm* (e x)
  (if (consp x)
      (if (equal e (car x))
          (rm* e (cdr x))
          (cons (car x)
                (rm* e (cdr x))))
      nil))

(defun twins (x)
  (declare (xargs :measure (len x)))
  (if (consp x)
      (if (member! (car x) (cdr x))
          (cons (car x)
                (twins
                 (rm* (car x) (cdr x))))
          (twins
           (rm* (car x) (cdr x))))
      nil))

; The problem does not require the proof of correctness of twins.
; But I work it out here because I will eventually give it as a
; problem.
 
(defun how-many (e x)
  (if (consp x)
      (if (equal e (car x))
          (+ 1 (how-many e (cdr x)))
          (how-many e (cdr x)))
      0))

; This fails but the checkpoint is relevant.
(defthm twins-correct
  (iff (member e (twins x))
       (equal (how-many e x) 2)))

(defthm member-how-many
  (iff (member e x)
       (< 0 (how-many e x))))

; This fails but the checkpoint is relevant.
(defthm twins-correct
  (iff (member e (twins x))
       (equal (how-many e x) 2)))

(defthm how-many-rm*
  (equal (how-many e (rm* d x))
         (if (equal e d)
             0
           (how-many e x))))

; This fails but the checkpoint is relevant.
(defthm twins-correct
  (iff (member e (twins x))
       (equal (how-many e x) 2)))

(defthm how-many-cdr-member
  (implies (member e x)
           (equal (how-many e (cdr (member e x)))
                  (- (how-many e x) 1))))

; Succeeds
(defthm twins-correct
  (iff (member e (twins x))
       (equal (how-many e x) 2)))

(quote (the end))
