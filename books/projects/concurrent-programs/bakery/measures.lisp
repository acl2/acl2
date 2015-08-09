(in-package "ACL2")

#|

     measures.lisp
     ~~~~~~~~~~~~~

we define and prove in this book several theorems about the measures defined by
fixed-length lists of natural numbers. the ordering on these measures is the
function msr< and is the lexicographic ordering on lists of naturals. we prove
that the ordering on these meaures is "embedded" in the e0-ord-< ordering on
the e0-ordinals, which is axiomatized to be well-founded and thus our ordering
is well-founded.

|#

;; (defun natp (x)
;;   (and (integerp x)
;;        (>= x 0)))

;; (defthm natp-compound-recognizer
;;   (iff (natp x)
;;        (and (integerp x)
;;             (>= x 0)))
;;   :rule-classes :compound-recognizer)

;; (in-theory (disable natp))

(include-book "ordinals/e0-ordinal" :dir :system)

(defmacro len= (x y)
  `(equal (len ,x) (len ,y)))

(defun msrp (x)
  (and (consp x)
       (natp (first x))))

(defun msr< (x y)
  (and (msrp x)
       (msrp y)
       (or (and (< (first x) (first y))
                (len= (rest x) (rest y)))
           (and (equal (first x) (first y))
                (msr< (rest x) (rest y))))))

(defun msr=0 (x)
  (or (endp x)
      (let ((ctr (first x)))
        (not (and (integerp ctr)
                  (> ctr 0))))))

(defun msr1- (x)
  (let ((rest (rest x)))
    (if (msr=0 rest)
        (cons (1- (first x)) rest)
      (cons (first x) (msr1- rest)))))

(defun pump-ord (n x)
  (if (zp n) (1+ x)
    (cons (pump-ord (1- n) x) 0)))

(defun msr->ord (x)
  (if (not (msrp x)) 0
    (cons (pump-ord (len x) (first x))
          (msr->ord (rest x)))))

(defun binary-induct (x y)
  (if (or (zp x) (zp y))
      (+ x y)
    (binary-induct (1- x) (1- y))))

(defthm consp-pump-ord-reduction
  (equal (consp (pump-ord n x))
         (and (integerp n)
              (> n 0))))

(defthm pump-ord-type-prescription
  (implies (and (integerp x)
                (>= x 0))
           (or (consp (pump-ord n x))
               (and (integerp (pump-ord n x))
                    (> (pump-ord n x) 0))))
  :rule-classes :type-prescription)

(defthm e0-ord-<-pump-ord-m<n
  (implies (and (integerp n)
                (integerp m)
                (> n m)
                (>= m 0)
                (integerp x)
                (integerp y))
           (e0-ord-< (pump-ord m x)
                     (pump-ord n y)))
  :hints (("Goal" :induct (binary-induct m n))))

(defthm e0-ord-<-asymmetry
  (implies (e0-ord-< x y)
           (not (e0-ord-< y x))))

(defthm pump-ord-is-an-e0-ordinalp
  (implies (and (integerp x)
                (>= x 0))
           (e0-ordinalp (pump-ord n x))))

(defthm car-msr->ord-conditional
  (implies (consp (msr->ord x))
           (equal (car (msr->ord x))
                  (pump-ord (len x) (car x)))))

(defthm pump-ord-maps-e0-ord-<-to-<1
  (implies (and (integerp x)
                (integerp y))
           (iff (e0-ord-< (pump-ord n x)
                          (pump-ord n y))
                (< x y))))

(defthm pump-ord-maps-e0-ord-<-to-<2
  (implies (and (integerp n)
                (integerp m)
                (integerp x)
                (>= m 0)
                (>= n 0))
           (iff (e0-ord-< (pump-ord n x)
                          (pump-ord m x))
                (< n m)))
  :hints (("Goal" :induct (binary-induct m n))))

(defthm msr<-implies-equal-lengths
  (implies (msr< x y)
           (equal (len x) (len y))))

#|

We will commonly use the predicate msr< as our well-founded measure in
the spec language SL. msr< is used to compare two equilength lists of
natural numbers via the lexicographic ordering. The next two theorems
demonstrate that msr< is well-founded by showing how to embed msr<
within e0-ord-< on the e0-ordinals via the mapping msr->ord. The last
theorem demonstrates that msr1- decrements measures which are non-0.

|#

(defthm msr->ord-returns-e0-ordinals
  (e0-ordinalp (msr->ord x))
  ;; [Jared] disabling this after building it into ACL2
  :hints(("Goal" :in-theory (disable fold-consts-in-+))))

(defthm msr<-is-well-founded-via-msr->ord
  (implies (msr< x y)
           (e0-ord-< (msr->ord x)
                     (msr->ord y))))

(defthm msr-1-decreases-non0-measures
  (implies (not (msr=0 x))
           (msr< (msr1- x) x)))


;;;; we additionally include some theorems for reducing msr<, cons,
;;;; append, len and some theorems demonstrating the ordering
;;;; properties of msr<

(defthm msr<-is-irreflexive
  (not (msr< x x)))

(defthm msr<-is-asymmetric
  (implies (msr< x y)
           (not (msr< y x))))

(defthm msr<-is-transitive
  (implies (and (msr< x y)
                (msr< y z))
           (msr< x z)))

(defthm msr<-cons-reduction
  (implies (and (len= x y)
                (natp a)
                (natp b))
           (equal (msr< (cons a x)
                        (cons b y))
                  (or (< a b)
                      (and (equal a b)
                           (msr< x y))))))

; Modified slightly 12/4/2012 by Matt K. to be redundant with new ACL2
; definition.
(defun nat-listp (l)
  (declare (xargs :guard t))
  (cond ((atom l)
         (eq l nil))
        (t (and (natp (car l))
                (nat-listp (cdr l))))))

(defthm nat-listp-is-true-listp
  (implies (nat-listp x)
           (true-listp x)))

(defthm len-append-reduction
  (equal (len (append x y))
         (+ (len x) (len y))))

(defthm msr<-append-reduction
  (implies (and (force (len= x1 y1))
                (force (len= x2 y2))
                (force (nat-listp x1))
                (force (nat-listp y1)))
           (equal (msr< (append x1 x2)
                        (append y1 y2))
                  (or (msr< x1 y1)
                      (and (equal x1 y1)
                           (msr< x2 y2))))))

