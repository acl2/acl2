(in-package "FAST-SETS")

(include-book "sets")

(defung add (x Y)
"Adds x to the set Y"
  (declare (xargs :guard (true-listp Y)))
  ((implies (true-listp Y) (true-listp (add x Y)))
   :rule-classes :type-prescription)
  (if (in x Y)
      Y
    (cons x Y)))

(defung intersect-aux (X Y Z)
  (declare (xargs :guard (and (true-listp X) (true-listp Y) (true-listp Z))))
  ((implies (true-listp Z) (true-listp (intersect-aux X Y Z)))
   :rule-classes :type-prescription)
  (cond ((endp X) Z)
        ((in (car X) Y)
         (intersect-aux (cdr X) Y (cons (car X) Z)))
        (t (intersect-aux (cdr X) Y Z))))

(defun intersect (X Y)
  (declare (xargs :guard (and (true-listp X) (true-listp Y))))
  (intersect-aux X Y nil))

(defthm append-==-set-union
  (== (append X Y)
      (sets::set-union X Y)))

(local
 (defthm intersect-aux-set-intersect
   (== (intersect-aux X Y Z)
       (append (sets::intersect X Y) Z))))

; Exercise 9
(defthm fast-intersect-is-set-intersect
  (== (intersect X Y)
      (sets::intersect X Y)))

(defung minus-t (X Y Z)
  (declare (xargs :guard (and (true-listp X) (true-listp Y) (true-listp Z))))
  ((implies (true-listp Z) (true-listp (minus-t X Y Z)))
   :rule-classes :type-prescription)
  (cond ((endp X) Z)
        ((in (car X) Y)
         (minus-t (cdr X) Y Z))
        (t (minus-t (cdr X) Y (cons (car X) Z)))))

; Exercise 10, part 1
(defun minus (X Y)
  (declare (xargs :guard (and (true-listp X) (true-listp Y))))
  (minus-t X Y nil))

(local (defthm minus-t-minus
         (== (minus-t X Y Z)
             (append (sets::minus X Y) Z))))

; Exercise 10, part 2
(defthm fast-minus-is-minus
  (== (minus X Y)
      (sets::minus X Y)))

(defun set-complement (X U)
  "complement set X (ie. U\X)"
  (declare (xargs :guard (and (true-listp X) (true-listp U))))
  (minus U X))

(defung set-union (X Y)
  (declare (xargs :guard (and (true-listp X) (true-listp Y))))
  ((implies (true-listp Y) (true-listp (set-union X Y)))
   :rule-classes :type-prescription)
  (cond ((endp X) Y)
        ((in (car X) Y)
         (set-union (cdr X) Y))
        (t (set-union (cdr X) (cons (car X) Y)))))

(local
 (defun ind-sb (Y Z x)
   (cond ((atom X) Z)
         ((in (car X) Y)
          (ind-sb Y Z (cdr X)))
         (t (ind-sb (cons (car X) Y)
                    (cons (car X) Z) (cdr X))))))

(local
 (defthm ==-over-set-union
   (implies (== Y Z)
            (== (set-union X Y)
                (set-union X Z)))
   :hints (("Goal" :induct (ind-sb y z x)))
   :rule-classes :congruence))

(local
 (defthm fast-set-union-over-cons
   (== (set-union X (cons a Y))
       (cons a (set-union X Y)))))

(local
 (defthm set-union-sets-set-union
   (implies (in a Y)
            (== (cons a (set-union X Y))
                (sets::set-union X Y)))))

; Exercise 8
(defthm fast-set-union-is-set-union
  (== (set-union X Y)
      (sets::set-union X Y)))

(defun remove-dups (X)
; removes duplicates in x.
  (declare (xargs :guard (true-listp X)))
  (set-union X nil))

(defun cardinality (X)
  (declare (xargs :guard (true-listp X)))
  (len (remove-dups X)))

(local
 (defthm remove-dups-is-remove-dups
   (== (remove-dups X)
       (sets::remove-dups X))))

(defthm no-dups-set-union
  (implies (no-dups X)
           (no-dups (set-union Y X))))

(defthm remove-dups-is-remove-dups2
  (perm (remove-dups X)
        (sets::rem-dups X))
  :hints (("Goal"
           :use ((:instance sets::no-dups-perm
                            (x (remove-dups x) )
                            (y (sets::rem-dups x)))))))

; Exercise 11
(defthm fast-cardinality-is-cardinality
  (equal (cardinality X)
         (sets::cardinality X)))

(in-theory (disable intersect minus set-union cardinality remove-dups))
