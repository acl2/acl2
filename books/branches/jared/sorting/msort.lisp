; (certify-book "msort")

(in-package "ACL2")

(include-book "perm")
(include-book "ordered-perms")
(include-book "convert-perm-to-how-many")

(defun merge2 (x y)
  (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
  (if (endp x)
      y
    (if (endp y)
        x
      (if (lexorder (car x) (car y))
          (cons (car x)
                (merge2 (cdr x) y))
        (cons (car y)
              (merge2 x (cdr y)))))))

(defthm acl2-count-evens-strong
  (implies (and (consp x)
                (consp (cdr x)))
           (< (acl2-count (evens x)) (acl2-count x)))
  :rule-classes :linear)

(defthm acl2-count-evens-weak
  (<= (acl2-count (evens x)) (acl2-count x))
  :hints (("Goal" :induct (evens x)))
  :rule-classes :linear)

(defun msort (x)
  (if (endp x)
      nil
    (if (endp (cdr x))
        (list (car x))
      (merge2 (msort (evens x))
              (msort (odds x))))))

(defthm orderedp-msort
  (orderedp (msort x)))

(defthm true-listp-msort
  (true-listp (msort x)))

(defthm how-many-merge2
  (equal (how-many e (merge2 x y))
         (+ (how-many e x) (how-many e y))))

(defthm how-many-evens-and-odds
  (implies (consp x)
           (equal (+ (how-many e (evens x))
                     (how-many e (evens (cdr x))))
                  (how-many e x))))

(defthm how-many-msort
  (equal (how-many e (msort x))
         (how-many e x)))

; (defthm perm-msort
;   (perm (msort x) x))

