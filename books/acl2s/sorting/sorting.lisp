#|

 Author: Pete Manolios
 
 This is a book with merge sort and insertion sort, along with version
 that do not include duplicates. 

 I use definec and all functions have their contracts checked, so
 guards are verified.

 The book does not currently include correctness proofs and was
 primarily developed for defdata.

|#

(in-package "ACL2S")
(include-book "acl2s/custom" :dir :system :ttags :all)
(include-book "sorting/msort" :dir :system)

(definec merge2 (x :integer-list y :integer-list) :integer-list
  (cond ((endp x) y)
        ((endp y) x)
        ((< (car x) (car y))
         (cons (car x)
               (merge2 (cdr x) y)))
        (t (cons (car y)
                 (merge2 x (cdr y))))))

(sig evens ((listof :a)) => (listof :a))
(sig odds ((listof :a)) => (listof :a))

(definec msort (x :integer-list) :integer-list
  (cond ((endp x) x)
        ((endp (cdr x)) x)
        (t (merge2 (msort (evens x))
                   (msort (odds x))))))

(definec merge2-no-dups (x :integer-list y :integer-list) :integer-list
  (cond ((endp x) y)
        ((endp y) x)
        ((< (car x) (car y))
         (cons (car x)
               (merge2-no-dups (cdr x) y)))
        ((= (car x) (car y))
         (cons (car x)
               (merge2-no-dups (cdr x) (cdr y))))
        (t (cons (car y)
                 (merge2-no-dups x (cdr y))))))

(definec msort-no-dups (x :integer-list) :integer-list
  (cond ((endp x) x)
        ((endp (cdr x)) x)
        (t (merge2-no-dups (msort-no-dups (evens x))
                           (msort-no-dups (odds x))))))

(defthm merge2-len
  (implies (and (integer-listp x)
                (integer-listp y))
           (equal (len (merge2 x y))
                  (+ (len x) (len y)))))

(defthm expand-evens
  (implies (true-listp l)
           (equal (evens (cons a l))
                  (cons a (evens (cdr l))))))

(defthm evens-len
  (implies (true-listp x)
           (equal (+ (len (evens x)) (len (evens (cdr x))))
                  (len x)))
  :rule-classes ((:rewrite) (:forward-chaining :trigger-terms ((evens x)))))

(defthm msort-len
  (implies (integer-listp x)
           (= (len (msort x)) (len x))))

(defthm merge2-no-dups-len
  (implies (and (integer-listp x)
                (integer-listp y))
           (<= (len (merge2-no-dups x y)) (+ (len x) (len y))))
  :rule-classes ((:linear) (:rewrite)))

(defthm msort-no-dups-len
  (implies (integer-listp x)
           (<= (len (msort-no-dups x)) (len x)))
  :rule-classes ((:linear) (:rewrite)))

; (msort-no-dups '(1 2 3 3 2 1 1 1 1 2 2 2 3 3 3))

(definec insert (e :int l :integer-list) :integer-list
  (cond ((endp l) (list e))
        ((<= e (car l)) (cons e l))
        (t (cons (car l) (insert e (cdr l))))))
                          
(definec insert-no-dups (e :int l :integer-list) :integer-list
  (cond ((endp l) (list e))
        ((< e (car l)) (cons e l))
        ((= e (car l)) l)
        (t (cons (car l) (insert-no-dups e (cdr l))))))

(definec isort (x :integer-list) :integer-list
  (if (endp x)
      nil
    (insert (car x) (isort (cdr x)))))

(definec isort-no-dups (x :integer-list) :integer-list
  (if (endp x)
      nil
    (insert-no-dups (car x) (isort-no-dups (cdr x)))))

(defthm insert-len
  (implies (and (integerp e)
                (integer-listp l))
           (= (len (insert e l)) (1+ (len l)))))

(defthm isort-len
  (implies (integer-listp x)
           (= (len (isort x)) (len x))))

(defthm insert-no-dups-len
  (implies (and (integerp e)
                (integer-listp l))
           (<= (len (insert-no-dups e l)) (1+ (len l))))
  :rule-classes ((:linear) (:rewrite)))

(defthm isort-no-dups-len
  (implies (integer-listp x)
           (<= (len (isort-no-dups x)) (len x)))
  :rule-classes ((:linear) (:rewrite)))

(definec rem-dups-sorted (x :integer-list) :integer-list
  (cond ((endp x) x)
        ((endp (rest x)) x)
        ((equal (car x) (cadr x))
         (rem-dups-sorted (cdr x)))
        (t (cons (car x) (rem-dups-sorted (cdr x))))))

(definec fill-in-list (l :integer-list last :int cnt :nat) :integer-list
  (declare (xargs :consider-only-ccms ((+ (len l) cnt))))
  ; ccms not needed, but used to speed up book certification by ~8 seconds
  (cond ((= cnt 0) l)
        ((endp l) (cons (1+ last) (fill-in-list l (1+ last) (1- cnt))))
        ((< (1+ last) (car l))
         (cons (1+ last) (fill-in-list l (1+ last) (1- cnt))))
        (t (cons (car l) (fill-in-list (cdr l) (car l) cnt)))))

;(fill-in-list '(1 4) 1 1)

(definec make-unique-ordered (l :integer-list min :int) :integer-list
  (let* ((len (len l))
         (sort (msort-no-dups l))
         (lens (len sort)))
    (fill-in-list sort (1- min) (- len lens))))

;(make-unique-ordered '(5 5 3 5) 1)

(definec make-nondec (l :integer-list) :integer-list
  (msort l))

;(make-nondec '(5 5 3 5))

(definec make-unique-decreasing (l :integer-list min :int) :integer-list
  (rev (make-unique-ordered l min)))

;(make-unique-decreasing '(5 5 3 5) 1)

(definec make-noninc (l :integer-list) :integer-list
  (rev (msort l)))

;(make-noninc '(5 5 5 3))

#| 
Some testing 

(defun makelst (n)
  (if (zp n)
      nil
    (cons n (makelst (1- n)))))

(time$ (progn$ (msort (makelst 40000)) nil))         ;  0.04 secs
(time$ (progn$ (msort-no-dups (makelst 40000)) nil)) ;  0.04 secs
(time$ (progn$ (acl2::msort (makelst 40000)) nil))   ;  0.06 secs
(time$ (progn$ (isort (makelst 40000)) nil))         ; 26.28 secs
|#
