(in-package "ACL2")

; Many of the exercises in Chapter 6 cannot be done with the
; mechanized ACL2 theorem prover because the proofs require either use
; of the primitive rules of inference, discussion of the issues, or
; use of set-theoretic ordinals.  Therefore, the file solutions.txt
; presents all of the solutions precisely but not in a machine checked
; format.

; Some of the exercises do admit solution with ACL2, even though you
; -- the reader -- are not actually expected to do them this way.
; Upon your first reading of Chapter 6 you will probably not have the
; skills at driving the ACL2 theorem prover necessary to do these
; proofs.  But you might eventually return to these exercises with the
; theorem prover behind you and appreciate these solutions.

; ---------------------------------------------------------------------------
; Exercise 6.3

(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

(defthm w-larger-than-nats
  (implies (natp x)
	   (e0-ord-< x '(1 . 0))))

(defthm w-smaller-than-non-nats
  (implies (and (e0-ordinalp x)
		(not (natp x))
		(not (equal x '(1 . 0))))
	   (e0-ord-< '(1 . 0) x)))

; ---------------------------------------------------------------------------
; Exercise 6.4

;(e0-ordinalp '(2 1 . 27))
;(e0-ordinalp '(2 1 1 . 27))
;(e0-ordinalp '(2 1 0 . 27))
;(e0-ordinalp '(1 2 2 . 27))

; ---------------------------------------------------------------------------
; Exercise 6.6

(defthm e0-cons-pos
  (implies (and (natp i1)
		(natp i2))
	   (iff (e0-ordinalp (cons i1 i2))
		(< 0 i1))))

(defthm e0-cons
  (implies (and (natp i1)
		(natp i2))
	   (e0-ordinalp (cons (1+ i1) i2))))

(defthm e0-<-nats
  (implies (and (natp i1)
		(natp i2)
		(natp j1)
		(natp j2))
	   (iff (e0-ord-< (cons (1+ i1) i2)
			  (cons (1+ j1) j2))
		(or (< i1 j1)
		    (and (equal i1 j1)
			 (< i2 j2))))))

; ---------------------------------------------------------------------------
; Exercise 6.7
; (dec i) is the ith element of the sequence
; <(1 2 . 0), (1 1 2 . 0), (1 1 1 2 . 0), ...>
; This sequence is described in solutions.txt.

(defun dec (n)
  (if (zp n)
      '(1 2 . 0)
    (cons 1 (dec (1- n)))))

(encapsulate
 nil
 (local (include-book "arithmetic/top-with-meta" :dir :system))
 (defthm dec-decreases
   (implies (natp n)
	    (e0-ord-< (dec (1+ n)) (dec n)))))


; ---------------------------------------------------------------------------
; Exercise 6.8

(defun natsp (x)
  (if (endp x)
      t
    (and (integerp (car x))
         (<= 0 (car x))
         (natsp (cdr x)))))

(defthm assoc-of-append
  (equal (append (append a b) c)
         (append a (append b c))))

(defthm true-listp-append-rewrite
  (implies (true-listp a)
           (equal (true-listp (append a b))
                  (true-listp b))))

(defthm append-right-id
  (implies (true-listp a)
           (equal (append a nil) a)))

(defun prefix (x)
  (cond
   ((endp x) nil)
   ((endp (cdr x)) nil)
   (t (cons (car x) (prefix (cdr x))))))

(defthm len-non-0
  (implies (consp x)
           (< 0 (len x)))
  :rule-classes :linear)

(defthm true-listp-last
  (equal (true-listp (last x))
         (true-listp x))
  :rule-classes (:rewrite :generalize))

(defthm len-last
  (equal (len (last x))
         (if (consp x) 1 0))
  :rule-classes (:rewrite :generalize))

(defthm prefix-last-elim
  (implies (consp x)
           (equal (append (prefix x) (last x)) x))
  :rule-classes (:rewrite :elim))

(defthm natp-car-last
  (implies (natsp x)
           (and (equal (integerp (car (last x)))
                       (consp x))
                (<= 0 (car (last x)))))
  :rule-classes
  ((:rewrite)
   (:type-prescription
    :corollary
    (implies (and (natsp x)
                  (case-split (consp x)))
             (and (integerp (car (last x)))
                  (<= 0 (car (last x))))))))

(defthm acl2-count-prefix
  (implies (consp x)
           (< (acl2-count (prefix x))
              (acl2-count x)))
  :rule-classes :linear)

(defun lex (tuple)
  (if (endp tuple)
      0
    (if (endp (cdr tuple))
	(1+ (car tuple))
      (cons (lex (prefix tuple))
            (car (last tuple))))))

(defthm equal-lex-0
  (implies (natsp tuple)
           (equal (equal (lex tuple) 0)
                  (endp tuple))))

(defthm len-append
  (equal (len (append a b))
         (+ (len a) (len b))))

(defthm natsp-prefix
  (implies (natsp x)
           (natsp (prefix x))))

(defthm natsp-append
  (equal (natsp (append a b))
         (and (natsp a)
              (natsp b))))

(defthm len-prefix
  (equal (len (prefix x))
         (if (consp x)
             (- (len x) 1)
           0)))

(defthm e0-ordinalp-lex
  (implies (natsp tuple)
           (e0-ordinalp (lex tuple))))

; This is ``x <_n y,'' where (len x) = (len y) = n.

(defun lex-< (x y)
  (cond ((endp x) nil)
        ((< (car x) (car y)) t)
        (t (and (equal (car x) (car y))
                (lex-< (cdr x) (cdr y))))))

(defthm equal-append
  (implies (true-listp a)
           (equal (equal (append a b)
                         (append a c))
                  (equal b c))))

(defun lex-equal-hint (x y)
  (cond
   ((or (endp x)
        (endp y)
        (endp (cdr x))
        (endp (cdr y)))
    (list x y))
   (t (lex-equal-hint (prefix x) (prefix y)))))

(defthm lex-equal
  (implies (and (natsp x)
                (true-listp x)
                (natsp y)
                (true-listp y)
                (equal (len x) (len y)))
           (equal (equal (lex x) (lex y))
                  (equal x y)))
  :hints (("Goal"
                  :induct (lex-equal-hint x y))))

(defthm lex-<-alternative-def
  (implies (and (true-listp x)
                (true-listp y)
                (equal (len x) (len y)))
           (equal (lex-< x y)
                  (if (endp x)
                      nil
                    (or (lex-< (prefix x) (prefix y))
                        (and (equal (prefix x) (prefix y))
                             (< (car (last x)) (car (last y))))))))
  :rule-classes ((:definition :controller-alist ((lex-< t nil)))))

(defthm equal-0-len
  (equal (equal 0 (len x))
         (endp x)))

; We could have loaded an arithmetic book to avoid the following.

(defthm equal-1-+-1
  (equal (equal 1 (+ 1 x))
         (equal 0 (fix x))))

(defthm lex-is-order-preserving
  (implies (and (natsp x)
                (natsp y)
                (true-listp x)
                (true-listp y)
                (equal (len x) (len y)))
           (iff (lex-< x y)
                (e0-ord-< (lex x)
                          (lex y))))
  :hints (("Goal" :induct (lex-equal-hint x y))))

; ---------------------------------------------------------------------------
; Exercise 6.11

(defun upto (i max)
  (declare (xargs :measure (nfix (- (1+ max) i))))
  (if (and (integerp i)
           (integerp max)
           (<= i max))
      (+ 1 (upto (+ 1 i) max))
    0))

(defthm upto-example
  (equal (upto 7 12) 6)
  :rule-classes nil)

; ---------------------------------------------------------------------------
; Exercise 6.12

(defun g (i j)
  (declare (xargs :measure (nfix (+ i j))))
  (if (zp i)
      j
    (if (zp j)
        i
      (if (< i j)
          (g i (- j i))
        (g (- i j) j)))))

(defthm g-examples
  (and (equal (g 18 45) 9)
       (equal (g 7 9) 1))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; Exercise 6.13

(defun mlen (x y)
  (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
  (if (or (consp x) (consp y))
      (+ 1 (mlen (cdr x) (cdr y)))
    0))

(defthm mlen-example
  (equal (mlen '(a b c) '(a b c d e)) 5)
  :rule-classes nil)

; ---------------------------------------------------------------------------
; Exercise 6.14

(defun flen (x)
  (declare (xargs :measure (if (null x) 0 (1+ (acl2-count x)))))
  (if (equal x nil)
      0
    (+ 1 (flen (cdr x)))))

(defthm flen-examples
  (and (equal (flen '(a b c)) 3)
       (equal (flen '(a b c . 7)) 4))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; Exercise 6.15

(defun ack (x y)
   (declare (xargs :measure (cons (1+ (nfix y)) (nfix x))))
   (if (zp x)
       1
     (if (zp y)
         (if (equal x 1) 2 (+ x 2))
       (ack (ack (1- x) y) (1- y)))))


; ---------------------------------------------------------------------------
; Exercise 6.16

; We will enumerate the various ``functions'' f1, f2, ..., and admit
; functions satisfying the corresponding constraints or prove theorems
; showing that no such function could exist.

; 1. (defun f (x) (f x))

(encapsulate ((f1 (x) t))
             (local (defun f1 (x) x))
             (defthm f1-constraint
               (equal (f1 x) (f1 x))
               :rule-classes nil))


; 2. (defun f (x) (not (f x)))

; If f2 were admitted, then we could instantiate the following theorem to
; derive the negation of its definitional equation.

(defthm f2-unsound
  (not (equal f2x (not f2x)))
  :rule-classes nil)

; 3. (defun f (x) (if (f x) t t))

(encapsulate ((f3 (x) t))
             (local (defun f3 (x) (declare (ignore x)) t))
             (defthm f3-constraint
               (equal (f3 x) (if (f3 x) t t))
               :rule-classes nil))

(defthm f3-is-unique
  (equal (f3 x) t)
  :hints (("Goal" :use f3-constraint)))


; 4. (defun f (x) (if (f x) t nil))

(encapsulate ((f4 (x) t))
             (local (defun f4 (x) (declare (ignore x)) t))
             (defthm f4-constraint
               (equal (f4 x) (if (f4 x) t nil))
               :rule-classes nil))

; Here are three functions.  In the next theorem we prove that all
; three satisfy the f4 equation but that all three are different
; functions, i.e., are unequal at some point in their domains.

(defun f4-a (x) (declare (ignore x)) t)
(defun f4-b (x) (declare (ignore x)) nil)
(defun f4-c (x) (if (equal x 1) t nil))

(defthm f4-not-unique
  (and (equal (f4-a x) (if (f4-a x) t nil))
       (equal (f4-b x) (if (f4-b x) t nil))
       (equal (f4-c x) (if (f4-c x) t nil))
       (not (equal (f4-a 1) (f4-b 1)))
       (not (equal (f4-a 2) (f4-c 2)))
       (not (equal (f4-b 1) (f4-c 1)))))

; 5. (defun f (x) (if (f x) nil t))

; This is the same as (f x) = (not (f x)).

; 6. (defun f (x) (if (zp x) 0 (f (- x 1))))

(defun f6 (x) (if (zp x) 0 (f6 (- x 1))))

; 7. (defun f (x) (if (zp x) 0 (f (f (- x 1)))))

(encapsulate ((f7 (x) t))
             (local (defun f7 (x) (declare (ignore x)) 0))
             (defthm f7-constraint
               (equal (f7 x)
                      (if (zp x)
                          0
                        (f7 (f7 (- x 1)))))
               :rule-classes ((:definition :controller-alist ((f7 t))))))

(defthm f7-is-unique
  (equal (f7 x) 0)
  :hints (("Goal" :induct (f6 x))))

; 8. (defun f (x) (if (zp x) 0 (+ 1 (f (f (- x 1))))))

(encapsulate ((f8 (x) t))
             (local (defun f8 (x) (nfix x)))
             (defthm f8-constraint
               (equal (f8 x)
                      (if (zp x)
                          0
                        (+ 1 (f8 (f8 (- x 1))))))
               :rule-classes ((:definition :controller-alist ((f8 t))))))

(defthm f8-is-unique
  (equal (f8 x) (nfix x))
  :hints (("Goal" :induct (f6 x))))

; 9. (defun f (x) (if (zp x) 0 (+ 2 (f (f (- x 1))))))

(defthm f9-unsound
  (not (equal f9x (+ 2 f9x)))
  :rule-classes nil)

; 10 (defun f (x) (if (integerp x) (* x (f (+ x 1)) (f (- x 1))) 0))

(encapsulate ((f10 (x) t))
             (local (defun f10 (x) (declare (ignore x)) 0))
             (defthm f10-constraint
               (equal (f10 x)
                      (if (integerp x)
                          (* x
                             (f10 (+ x 1))
                             (f10 (- x 1)))
                        0))
               :rule-classes ((:definition :controller-alist ((f10 t))))))

(defun f10-induction (x)
  (declare (xargs :measure (acl2-count x))) ; = (abs x) for integral x.
  (if (integerp x)
      (if (< x 0)
          (f10-induction (+ x 1))
        (if (< 0 x)
            (f10-induction (- x 1))
          x))
    x))

(defthm times-zero
  (equal (* 0 x) 0))

(defthm f10-is-unique
  (equal (f10 x) 0)
  :hints (("Goal" :induct (f10-induction x))))
