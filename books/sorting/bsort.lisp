; (certify-book "bsort")

(in-package "ACL2")

(include-book "ordered-perms")
(include-book "convert-perm-to-how-many")

(defun bnext (x)
  (declare (xargs :measure (len x)))
  (cond ((endp x) x)
        ((endp (cdr x)) x)
        ((lexorder (car x) (cadr x))
         (cons (car x) (bnext (cdr x))))
        (t (cons (cadr x)
                 (bnext (cons (car x) (cddr x)))))))

(defun how-many-smaller (e x)
  (cond ((endp x) 0)
        ((equal e (car x)) (how-many-smaller e (cdr x)))
        ((lexorder (car x) e) (+ 1 (how-many-smaller e (cdr x))))
        (t (how-many-smaller e (cdr x)))))

(defun bnext-size (x)
  (cond ((endp x) 0)
        (t (+ (how-many-smaller (car x) (cdr x))
              (bnext-size (cdr x))))))

(defthm how-many-smaller-bnext
  (equal (how-many-smaller e (bnext x))
         (how-many-smaller e x)))

#|
(defun samep (x y)
  (if (endp x)
      (endp y)
    (if (endp y)
        nil
      (and (equal (car x) (car y))
           (samep (cdr x) (cdr y))))))

(defequiv samep)

(defcong samep equal (how-many-smaller e x) 2)|#

(defthm how-many-bad-pairs-bnext
  (implies (not (equal x (bnext x)))
           (< (bnext-size (bnext x))
              (bnext-size x)))
  :rule-classes :linear)

(defun bsort (x)
  (declare (xargs :measure (bnext-size x)))
  (if (equal (bnext x) x)
      x
    (bsort (bnext x))))

(defthm orderedp-when-bnext-constant
  (implies (equal (bnext x) x)
           (orderedp x)))

(defthm orderedp-bsort
  (orderedp (bsort x)))

(defthm true-listp-bnext
  (implies (true-listp x)
           (true-listp (bnext x))))

(defthm true-listp-bsort
  (implies (true-listp x)
           (true-listp (bsort x))))

(defthm how-many-bnext
  (equal (how-many e (bnext x))
         (how-many e x)))

(defthm how-many-bsort
  (equal (how-many e (bsort x))
         (how-many e x)))

