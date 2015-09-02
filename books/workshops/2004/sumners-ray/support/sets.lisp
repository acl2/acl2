;; sets.lisp

(in-package "ACL2")

(set-match-free-default :all)

#|

We define the common boolean operations (and a few other common useful notions)
on sets canonicalized as ordered lists using Pete's total ordering of all ACL2
objects. Further, the functions have been defined with a normalization of all
ACL2 objects as appropriate sets (we define a 1-1 function which maps any ACL2
object to a corresponding well-formed set) and using this normal (and its
inverse), we can prove properties about normalized set operations which use
equal-ity instead of set-equality and require no backtracking to relieve
well-formed set hypotheses.

EXPORTED logic functions:

   (in e x)      -- set membership predicate, is element e a member of set x
   (subset x y)  -- subset predicate, is set x a subset of set y
   (isect x y)   -- the set intersection of set x and set y
   (unite x y)   -- the set union of set x and set y
   (sdiff x y)   -- the set of elements in set x but not in set y
   (card x)      -- returns the number of objects in the set x
   (s1 e)        -- the singleton set consisting only of the element e
   (scar x)      -- the least (by <<) element in the set x, nil if x is empty
   ()            -- NIL is unique representative value for empty set,
                    so use NULL or NOT to test a set for emptiness
   (c1 x)        -- test which returns true if x is a singleton set

EXPORTED theorems provided at the end of this file.

I have removed all of the subgoal hints except for those introduced by the
macro defthm-ternary-sets. These subgoal hints are reasonable since they are
introduced in the context of a provided induction scheme and they help speed
the proofs through considerably by avoiding the problem in ACL2 of
free-variable matching in the application of <<-transitive.

|#

(include-book "total-order")

;; i needed to add the following forward-chaining rule to make better use
;; of <<-trichotomy from the included order book.

(local
(defthm <<-trichotomy-forward-chain1
  (implies (and (not (<< x y))
                (not (equal x y)))
           (<< y x))
  :rule-classes :forward-chaining))

(defun setp (x)
  (or (null x)
      (and (consp x)
           (setp (rest x))
           (or (null (rest x))
               (<< (first x) (second x))))))

(defun ifsp (x) ;; ill-formed setp
  (or (not (setp x))
      (and (consp x)
           (null (cdr x))
           (ifsp (car x)))))

(defun norm->set (x)
  (if (ifsp x) (list x) x))

(defun set->norm (x)
  (if (ifsp x) (first x) x))

(defun in-aux (e x)
  (and (not (endp x))
       (or (equal e (first x))
           (and (<< (first x) e)
                (in-aux e (rest x))))))

(defun in (e x)
  (in-aux e (norm->set x)))

(defun subset-aux (x y)
  (or (endp x)
      (and (not (endp y))
           (cond ((equal (first x) (first y))
                  (subset-aux (rest x) (rest y)))
                 ((<< (first y) (first x))
                  (subset-aux x (rest y)))
                 (t nil)))))

(defun subset (x y)
  (subset-aux (norm->set x) (norm->set y)))

(defun isect-aux (x y)
  (declare (xargs :measure (+ (acl2-count x)
                              (acl2-count y))))
  (cond ((endp x) ())
        ((endp y) ())
        ((equal (first x) (first y))
         (cons (first x)
               (isect-aux (rest x) (rest y))))
        ((<< (first x) (first y))
         (isect-aux (rest x) y))
        (t
         (isect-aux x (rest y)))))

(defun isect (x y)
  (set->norm (isect-aux (norm->set x) (norm->set y))))

(defun unite-aux (x y)
  (declare (xargs :measure (+ (acl2-count x)
                              (acl2-count y))))
  (cond ((endp x) y)
        ((endp y) x)
        ((equal (first x) (first y))
         (cons (first x)
               (unite-aux (rest x) (rest y))))
        ((<< (first x) (first y))
         (cons (first x)
               (unite-aux (rest x) y)))
        (t
         (cons (first y)
               (unite-aux x (rest y))))))

(defun unite (x y)
  (set->norm (unite-aux (norm->set x) (norm->set y))))

(defun sdiff-aux (x y)
  (declare (xargs :measure (+ (acl2-count x)
                              (acl2-count y))))
  (cond ((endp x) ())
        ((endp y) x)
        ((equal (first x) (first y))
         (sdiff-aux (rest x) (rest y)))
        ((<< (first x) (first y))
         (cons (first x)
               (sdiff-aux (rest x) y)))
        (t
         (sdiff-aux x (rest y)))))

(defun sdiff (x y)
  (set->norm (sdiff-aux (norm->set x) (norm->set y))))

(defun s1 (e)
  (set->norm (list e)))

(defun card (x)
  (len (norm->set x)))

(defun scar (x)
  (if (ifsp x) x (first x)))

(defmacro empty-set ()
  `())

(defun c1 (x)
  (let ((x (norm->set x))) (and (consp x) (not (cdr x)))))



;;; some useful auxiliary macros which could be removed if
;;; needed (e.g. if the names conflict with existing fns)

(defmacro sadd (e x)
  `(unite (s1 ,e) ,x))

(defmacro sdrop (e x)
  `(sdiff ,x (s1 ,e)))

(defmacro scdr (x)
  `(sdrop (scar ,x) ,x))

(defmacro satom (x)
  `(not ,x))

(defmacro common (x y)
  `(not (satom (isect ,x ,y))))


;;;; properties of setp ;;;;

(local
(defthm setp-implies-true-listp
  (implies (setp x)
           (true-listp x))
  :rule-classes (:forward-chaining
                 :rewrite)))


;;;; properties of norm->set and set->norm ;;;;

(local
(defthm norm->set-set->norm-of-setp
  (implies (setp x)
           (equal (norm->set (set->norm x))
                  x))))

(local
(defthm norm->set-of-wf-setp
  (implies (not (ifsp x))
           (equal (norm->set x) x))))

(local
(defthm norm->set-of-if-setp
  (implies (ifsp x)
           (equal (norm->set x) (list x)))))

(local
(defthm norm->set-returns-setp
  (setp (norm->set x))))

(local
(defthm norm->set-preserves-equality
  (iff (equal (norm->set x) (norm->set y))
       (equal x y))))

(local
(defthm set->norm-norm->set-inverse
  (equal (set->norm (norm->set x)) x)))

(local
(defthm set->norm-nil-iff-passed-nil
  (implies (setp x)
           (iff (set->norm x) x))))

(local
(defthm norm->set-of-x-is-consp-or-not-x
  (iff (consp (norm->set x)) x)
  :rule-classes nil))

(local
(defthm norm->set-is-true-listp
  (true-listp (norm->set x))
  :rule-classes :type-prescription))

(in-theory (disable set->norm norm->set))


;;;; bounded properties ;;;;

(local
(defthm unite-aux-bounded-<<
  (implies (and (<< a (first x))
                (<< a (first y)))
           (<< a (first (unite-aux x y))))))

(local
(defthm isect-aux-bounded-<<
  (implies (and (or (<< a (first x))
                    (<< a (first y)))
                (isect-aux x y))
           (<< a (first (isect-aux x y))))))

(local
(defthm sdiff-aux-bounded-<<
  (implies (and (setp x)
                (<< a (first x))
                (sdiff-aux x y))
           (<< a (first (sdiff-aux x y))))))


;;;; type-correctness properties ;;;;

(local
(defthm unite-aux-preserves-setp
  (implies (and (setp x) (setp y))
           (setp (unite-aux x y)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((unite-aux x y)))
                 :rewrite)))

(local
(defthm isect-aux-preserves-setp
  (implies (and (setp x) (setp y))
           (setp (isect-aux x y)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((isect-aux x y)))
                 :rewrite)))

(local
(defthm sdiff-aux-preserves-setp
  (implies (setp x)
           (setp (sdiff-aux x y)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((sdiff-aux x y)))
                 :rewrite)))


;;;; properties of membership-aux ;;;;

(local
(defthm in-aux-isect-aux-reduce
  (equal (in-aux e (isect-aux x y))
         (and (in-aux e x) (in-aux e y)))))

(local
(defthm in-aux-unite-aux-reduce
  (equal (in-aux e (unite-aux x y))
         (or (in-aux e x) (in-aux e y)))))

(local
(defthm in-aux-implies-bounded
  (implies (and (setp x)
                (<< a (first x)))
           (not (in-aux a x)))))

(local
(defthm in-aux-sdiff-aux-reduce
  (implies (setp x)
           (equal (in-aux e (sdiff-aux x y))
                  (and (in-aux e x) (not (in-aux e y)))))))

(local
(defthm in-aux-subset-aux-transits
  (implies (and (in-aux e x)
                (subset-aux x y))
           (in-aux e y))))


;;;; ternary variable induction scheme and strategy ;;;;

;; the following function defines an induction scheme used in theorems
;; involving three free variables (like associativity proofs).

(local
(defun ternary-induct (x y z)
  (declare (xargs :measure (+ (acl2-count x)
                              (acl2-count y)
                              (acl2-count z))))
  (if (or (endp x)
          (endp y)
          (endp z))
 ; The following was changed to avoid SBCL warning, "Asserted type NUMBER
 ; conflicts with derived type (VALUES LIST &OPTIONAL)."
      (list x y z)
    (cond ((<< (first x) (first y))
           (cond ((<< (first x) (first z))
                  (ternary-induct (rest x) y z))
                 ((equal (first x) (first z))
                  (ternary-induct (rest x) y (rest z)))
                 ((and (<< (first z) (first x))
                       (<< (first z) (first y)))
                  (ternary-induct x y (rest z)))))
          ((equal (first x) (first y))
           (cond ((<< (first x) (first z))
                  (ternary-induct (rest x) (rest y) z))
                 ((equal (first x) (first z))
                  (ternary-induct (rest x) (rest y) (rest z)))
                 ((<< (first z) (first x))
                  (ternary-induct x y (rest z)))))
          ((<< (first y) (first x))
           (cond ((<< (first y) (first z))
                  (ternary-induct x (rest y) z))
                 ((equal (first y) (first z))
                  (ternary-induct x (rest y) (rest z)))
                 ((and (<< (first z) (first y))
                       (<< (first z) (first x)))
                  (ternary-induct x y (rest z)))))))))

;; the following macro defines an effective strategy for inducting based on the
;; scheme ternary-induct.

(defmacro defthm-ternary-sets (name body)
  `(defthm ,name ,body
     :hints (("Goal"
              :induct (ternary-induct x y z)
              :in-theory (disable <<-transitive))
             ("Subgoal *1/13"
              :in-theory (enable <<-transitive))
             ("Subgoal *1/5"
              :in-theory (enable <<-transitive)))))


;;;; properties of subset-aux ;;;;

(local
(defthm unite-aux-x<y-expansion
  (implies (and (consp x)
                (consp y)
                (<< (car x) (car y)))
           (equal (unite-aux x y)
                  (cons (car x)
                        (unite-aux (cdr x) y))))))

(local
(defthm subset-aux-x<y-reduces-nil
  (implies (and (consp x)
                (consp y)
                (<< (car x) (car y)))
           (equal (subset-aux x y)
                  nil))))

(local
(defthm atom-unite-aux-implies-atom-params
  (implies (not (consp (unite-aux x y)))
           (and (not (consp x))
                (not (consp y))))))

(local
(defthm-ternary-sets subset-aux-unite-aux-reduction
  (equal (subset-aux (unite-aux x y) z)
         (and (subset-aux x z)
              (subset-aux y z)))))

(local
(in-theory (disable unite-aux-x<y-expansion)))

(local
(defthm subset-aux-is-reflexive
  (subset-aux x x)))

(local
(defthm subset-aux-unite-aux-property
  (implies (setp x)
           (subset-aux x (unite-aux x y)))))

(local
(defthm <<-irreflexive-rewrite
  (implies (<< x y)
           (not (equal x y)))))

(local
(defthm-ternary-sets subset-aux-isect-aux-reduction
  (equal (subset-aux x (isect-aux y z))
         (and (subset-aux x y)
              (subset-aux x z)))))

(local
(defthm subset-aux-isect-aux-property
  (implies (setp x)
           (subset-aux (isect-aux x y) x))))

(local
(defthm subset-aux-sdiff-aux-property
  (implies (setp x)
           (subset-aux (sdiff-aux x y) x))))

(local
(defthm-ternary-sets subset-aux-is-transitive
  (implies (and (subset-aux x y)
                (subset-aux y z))
           (subset-aux x z))))

(local
(defthm subset-aux-is-total-on-sets
  (implies (and (setp x) (setp y)
                (subset-aux x y))
           (equal (subset-aux y x)
                  (equal x y)))))

(local
(defthm subset-length-property
  (implies (and (setp x)
                (setp y)
                (subset-aux x y))
           (<= (len x) (len y)))))

(local
(defthm len<-reduce-when-subset
  (implies (and (setp x)
                (setp y)
                (subset-aux x y))
           (equal (< (len x) (len y))
                  (not (equal x y))))))


;;;; properties of unite-aux ;;;;

(local
(defthm unite-aux-implied-by-and
  (implies (and (setp x)
                (setp y)
                x y)
           (unite-aux x y))))

(local
(defthm unite-aux-reflexes
  (implies (setp x)
           (equal (unite-aux x x) x))))

(local
(defthm unite-aux-commutes
  (implies (and (setp x) (setp y))
           (equal (unite-aux x y)
                  (unite-aux y x)))))

(local
(defthm unite-aux-x<y-expansion-flip
  (implies (and (consp x)
                (consp y)
                (<< (car x) (car y)))
           (equal (unite-aux y x)
                  (cons (car x)
                        (unite-aux y (cdr x)))))))

(local
(in-theory (enable unite-aux-x<y-expansion)))

(local
(defthm-ternary-sets unite-aux-associates
  (implies (and (setp x) (setp y) (setp z))
           (equal (unite-aux (unite-aux x y) z)
                  (unite-aux x (unite-aux y z))))))

(local
(in-theory (disable unite-aux-x<y-expansion-flip
                    unite-aux-x<y-expansion)))

(local
(defthm unite-aux-subset-aux-property
  (equal (equal (unite-aux x y) y)
         (subset-aux x y))))

(local
(defthm length-of-unite-aux-property
  (implies (and (setp x) (setp y))
           (equal (len (unite-aux x y))
                  (+ (len x)
                     (len (sdiff-aux y x)))))))

(local
(defthm set-norm-equality-transfer
  (implies (setp x)
           (equal (equal (set->norm x) y)
                  (equal x (norm->set y))))))


;;;; properties of isect-aux ;;;;

(local
(defthm isect-aux-reflexes
  (implies (setp x)
           (equal (isect-aux x x) x))))

(local
(defthm isect-aux-commutes
  (implies (and (setp x) (setp y))
           (equal (isect-aux x y) (isect-aux y x)))))

(local
(defthm isect-aux-x<y-expansion
  (implies (and (consp x)
                (consp y)
                (<< (car x) (car y)))
           (equal (isect-aux y x)
                  (isect-aux y (cdr x))))))

(local
(defthm-ternary-sets isect-aux-associates
  (implies (and (setp x) (setp y) (setp z))
           (equal (isect-aux (isect-aux x y) z)
                  (isect-aux x (isect-aux y z))))))

(local
(in-theory (disable isect-aux-commutes
                    unite-aux-commutes)))

(local
(defthm isect-aux-bounded-then-not-equal
  (implies (and (consp z)
                (or (<< (car z) (car x))
                    (<< (car z) (car y))))
           (not (equal (isect-aux x y) z)))))

(local
(defthm isect-aux-subset-aux-property
  (implies (and (setp x) (setp y))
           (equal (equal (isect-aux x y) x)
                  (subset-aux x y)))))

(local
(defthm <<-irreflexive-rewrite-flip
  (implies (<< x y)
           (not (equal y x)))))

(local
(defthm-ternary-sets isect-aux-unite-aux-distributes
  (implies (and (setp x) (setp y) (setp z))
           (equal (isect-aux (unite-aux x y) z)
                  (unite-aux (isect-aux x z)
                             (isect-aux y z))))))

(local
(defthm-ternary-sets isect-aux-sdiff-aux-distributes
  (implies (and (setp x) (setp y) (setp z))
           (equal (isect-aux (sdiff-aux x y) z)
                  (sdiff-aux (isect-aux x z) y)))))


;;;; properties of sdiff-aux ;;;;

(local
(defthm sdiff-aux-subset-aux-property
  (implies (and (setp x) (setp y))
           (iff (sdiff-aux x y)
                (not (subset-aux x y))))))

(local
(defthm length-of-sdiff-aux-property
  (implies (and (setp x) (setp y))
           (equal (len (sdiff-aux x y))
                  (- (len x)
                     (len (isect-aux x y)))))))

(local
(defthm-ternary-sets sdiff-aux-unite-aux-distributes
  (implies (and (setp x) (setp y) (setp z))
           (equal (sdiff-aux (unite-aux x y) z)
                  (unite-aux (sdiff-aux x z)
                             (sdiff-aux y z))))))

(local
(defthm-ternary-sets sdiff-aux-unite-aux-reduction
  (implies (and (setp x) (setp y) (setp z))
           (equal (sdiff-aux x (unite-aux y z))
                  (sdiff-aux (sdiff-aux x y) z)))))

(local
(defthm sdiff-aux-reduce-no-isect-aux
  (implies (and (setp x) (setp y) (not (isect-aux x y)))
           (equal (sdiff-aux x y) x))))


;;;; properties of s1-aux -- i.e. list ;;;;

(local
(defthm subset-aux-reduces-to-membership
  (implies (setp x)
           (equal (subset-aux (list e) x)
                  (in-aux e x)))))

(local
(defthm subset-aux-of-singleton
  (implies (and (setp x) x
                (subset-aux x (list e)))
           (equal (equal x (list e)) t))))

(local
(defthm isect-aux-of-singleton
  (implies (setp x)
           (equal (isect-aux (list e) x)
                  (if (in-aux e x) (list e) ())))))

(local
(defthm sdiff-aux-of-singleton
  (implies (setp x)
           (equal (sdiff-aux (list e) x)
                  (if (in-aux e x) () (list e))))))


;;;; EXPORTED THEOREMS ;;;;
;; Note, the order of the these theorems below is relevant for the
;; order in which ACL2 applies them (later ones first). This is why
;; the associativity and commutativity theorems are first since
;; restructuring unite and isect can have the detrimental effect of
;; disabling the application of other rules.

(local
(in-theory (enable unite-aux-commutes
                   isect-aux-commutes)))


;;;; EXPORTED associative and commutative properties ;;;;

(defthm unite-implied-by-and
  (implies (and x y)
           (unite x y)))

(defthm unite-reflexes
  (equal (unite x x) x))

(defthm unite-commutes
  (equal (unite x y)
         (unite y x)))

(defthm unite-associates
  (equal (unite (unite x y) z)
         (unite x (unite y z))))

(defthm unite-associate-2
  (equal (unite x (unite y z))
         (unite y (unite x z)))
  :hints (("Goal"
           :in-theory (disable unite-commutes)
           :use ((:instance unite-commutes
                            (x x) (y (unite y z)))
                 (:instance unite-commutes
                            (x x) (y z))))))

(defthm isect-reflexes
  (equal (isect x x) x))

(defthm isect-commutes
  (equal (isect x y)
         (isect y x)))

(defthm isect-associates
  (equal (isect (isect x y) z)
         (isect x (isect y z))))

(defthm isect-associate-2
  (equal (isect x (isect y z))
         (isect y (isect x z)))
  :hints (("Goal"
           :in-theory (disable isect-commutes)
           :use ((:instance isect-commutes
                            (x x) (y (isect y z)))
                 (:instance isect-commutes
                            (x x) (y z))))))

;;;; EXPORTED properties of membership ;;;;

(defthm in-isect-reduce
  (equal (in e (isect x y))
         (and (in e x) (in e y))))

(defthm in-unite-reduce
  (equal (in e (unite x y))
         (or (in e x) (in e y))))

(defthm in-sdiff-reduce
  (equal (in e (sdiff x y))
         (and (in e x) (not (in e y)))))

(defthm in-subset-transits
  (implies (and (in e x)
                (subset x y))
           (in e y)))


;;;; EXPORTED properties of susbet ;;;;

(defthm subset-unite-reduction
  (equal (subset (unite x y) z)
         (and (subset x z)
              (subset y z))))

(defthm subset-unite-property
  (subset x (unite x y)))

(defthm subset-isect-reduction
  (equal (subset x (isect y z))
         (and (subset x y)
              (subset x z))))

(defthm subset-isect-property
  (subset (isect x y) x))

(defthm subset-sdiff-property
  (subset (sdiff x y) x))

(defthm subset-is-reflexive
  (subset x x))

(defthm subset-is-transitive
  (implies (and (subset x y)
                (subset y z))
           (subset x z)))

(defthm subset-is-total-order
  (implies (subset x y)
           (equal (subset y x)
                  (equal x y))))

(defthm subset-card-property
  (implies (subset x y)
           (<= (card x) (card y))))

(defthm card<-reduce-when-subset
  (implies (subset x y)
           (equal (< (card x) (card y))
                  (not (equal x y)))))


;;;; EXPORTED reductions of unite ;;;;

(defthm unite-subset-property
  (equal (equal (unite x y) y)
         (subset x y)))

(defthm unite-subset-property-2
  (equal (equal (unite y x) y)
         (subset x y)))

(defthm unite-card-property
  (equal (card (unite x y))
         (+ (card x)
            (card (sdiff y x)))))


;;;; EXPORTED reductions of isect ;;;;

(defthm isect-subset-property
  (equal (equal (isect x y) x)
         (subset x y)))

(defthm isect-unite-distributes-1
  (equal (isect (unite x y) z)
         (unite (isect x z)
                (isect y z))))

(defthm isect-unite-distributes-2
  (equal (isect z (unite x y))
         (unite (isect x z)
                (isect y z)))
  :hints (("Goal" :in-theory (disable isect-aux-commutes)
           :use (:instance isect-aux-commutes
                           (x (norm->set z))
                           (y (unite-aux (norm->set x)
                                         (norm->set y)))))))

(defthm isect-sdiff-distributes-1
  (equal (isect (sdiff x y) z)
         (sdiff (isect x z) y)))

(defthm isect-sdiff-distributes-2
  (equal (isect z (sdiff x y))
         (sdiff (isect x z) y))
  :hints (("Goal" :in-theory (disable isect-aux-commutes)
           :use (:instance isect-aux-commutes
                           (x (norm->set z))
                           (y (sdiff-aux (norm->set x)
                                         (norm->set y)))))))


;;;; EXPORTED reductions of sdiff ;;;;

(defthm sdiff-subset-property
  (iff (sdiff x y)
       (not (subset x y))))

(defthm sdiff-card-property
  (equal (card (sdiff x y))
         (- (card x)
            (card (isect x y)))))

(defthm sdiff-unite-distributes
  (equal (sdiff (unite x y) z)
         (unite (sdiff x z)
                (sdiff y z))))

(defthm sdiff-unite-reduction
  (equal (sdiff x (unite y z))
         (sdiff (sdiff x y) z)))

(defthm sdiff-reduce-no-isect
  (implies (not (isect x y))
           (equal (sdiff x y) x)))


;;;; EXPORTED reductions of s1 ;;;;

(defthm s1-membership-property
  (equal (in a (s1 b))
         (equal a b)))

(defthm s1-subset-property-1
  (equal (subset (s1 e) x)
         (in e x)))

(defthm s1-subset-property-2
  (implies (and (subset x (s1 e)) x)
           (equal x (s1 e)))
  :hints (("Goal" :use
           (:instance norm->set-of-x-is-consp-or-not-x)))
  :rule-classes :forward-chaining)

(defthm s1-isect-property-1
  (equal (isect (s1 e) x)
         (if (in e x) (s1 e) ())))

(defthm s1-isect-property-2
  (equal (isect x (s1 e))
         (if (in e x) (s1 e) ()))
  :hints (("Goal" :in-theory (disable isect-aux-commutes)
           :use (:instance isect-aux-commutes
                           (x (norm->set x))
                           (y (list e))))))

(defthm s1-sdiff-property
  (equal (sdiff (s1 e) x)
         (if (in e x) () (s1 e))))

(defthm s1-card-property
  (equal (card (s1 e)) 1))

(defthm s1-iff-t (iff (s1 e) t))

(defthm s1-equal-nil
  (equal (equal (s1 e) nil) nil))

(defthm subset-s1-redux
  (equal (subset a (s1 e))
         (if a (equal a (s1 e)) t)))



;;;; EXPORTED properties of empty-set ;;;;

(defthm membership-empty-set
  (not (in e (empty-set))))

(defthm empty-set-is-subset
  (subset (empty-set) x))

(defthm empty-set-is-only-superset-self
  (equal (subset x (empty-set))
         (not x)))

(defthm unite-empty-set-property-1
  (equal (unite x (empty-set)) x))

(defthm unite-empty-set-property-2
  (equal (unite (empty-set) x) x))

(defthm isect-empty-set-property-1
  (equal (isect (empty-set) x) (empty-set)))

(defthm isect-empty-set-property-2
  (equal (isect x (empty-set)) (empty-set)))

(defthm sdiff-of-empty-set-1
  (equal (sdiff (empty-set) x) (empty-set)))

(defthm sdiff-of-empty-set-2
  (equal (sdiff x (empty-set)) x))

(defthm s1-is-not-empty-set
  (s1 e)
  :hints (("Goal" :in-theory (enable set->norm)))
  :rule-classes :type-prescription)

(defthm card-of-empty-set
  (iff (not x)
       (equal (card x) 0))
  :hints (("Goal" :in-theory (enable norm->set)))
  :rule-classes :type-prescription)


;;;; EXPORTED properties of scar ;;;;

(defthm scar-membership-property
  (iff (in (scar x) x) x))

(defthm scar-is-least-member
  (implies (and (in e x)
                (not (equal e (scar x))))
           (<< (scar x) e)))

(defthm scar-returns-nil-for-empty-set
  (equal (scar (empty-set)) nil))

(defthm scar-of-s1
  (equal (scar (s1 e)) e)
  :hints (("Goal" :in-theory (enable set->norm))))

(defthm scar-of-unite
  (implies (and x y)
           (equal (scar (unite x y))
                  (if (<< (scar x) (scar y)) (scar x) (scar y))))
  :hints (("Goal" :in-theory (enable norm->set set->norm))))

(defthm scar-of-sdiff
  (implies (<< (scar x) (scar y))
           (equal (scar (sdiff x y)) (scar x)))
  :hints (("Goal" :in-theory (enable norm->set set->norm))))


;;;; EXPORTED properties of c1 ;;;;

(defthm c1-of-s1
  (equal (c1 (s1 e)) t))

(defthm c1-of-nil
  (equal (c1 ()) nil))

(defthm c1-of-unite
  (equal (c1 (unite x y))
         (if (c1 x) (implies y (equal x y)) (and (not x) (c1 y))))
  :hints (("Goal" :in-theory (enable norm->set set->norm)
           :expand ((unite-aux (list x) y) (unite-aux x y)))))

(defthm isect-aux-sdiff-aux-prop1
  (implies (and (setp x) x
                (not (isect-aux x y)))
           (sdiff-aux x y)))

(defthm isect-aux-sdiff-aux-prop2
  (implies (and (consp x)
                (setp x)
                (not (isect-aux x y))
                (not (cdr (sdiff-aux x y))))
           (not (cdr x))))

(defthm c1-of-sdiff
  (implies (not (isect x y))
           (equal (c1 (sdiff x y)) (c1 x)))
  :hints (("Goal" :in-theory (enable norm->set set->norm)
           :expand ((:free (x) (sdiff-aux (list x) y))
                    (:free (x z) (sdiff-aux (list x z) y))
                    (:free (x a b) (sdiff-aux (list* x a b) y))))))

(defthm c1-not-sdiff
  (implies (and (isect x y) (c1 x))
           (not (sdiff x y)))
  :hints (("Goal" :in-theory (enable norm->set set->norm)
           :expand (:free (x) (sdiff-aux (list x) y)))))


;; we now disable the top-level functions to keep their
;; definitions from being expanded

(in-theory (disable in subset isect unite sdiff card s1 scar c1))

;; the following macro will enable/disable the executable-counterparts

(defmacro ec-sets (x)
  `(in-theory (,(if x 'enable 'disable)
               (in) (subset) (isect) (unite)
               (sdiff) (card) (s1) (scar) (c1))))

;; we will begin with the executable-counterparts disabled

(ec-sets nil)

;; the following macro is a convenient way to define constants, it is similar
;; to the 'list macro

(defmacro make-set (&rest elems)
  (if (endp elems) '(emptyset)
    `(sadd ,(first elems) (make-set ,@(rest elems)))))



;; we conclude with a few corollaries

(defthm unite-iff-or
  (iff (unite x y) (or x y))
  :hints (("Goal" :cases ((not x) (not y)))))

(defthm unite-x-absorption
  (equal (unite x (unite x y)) (unite x y)))

(defthm c1-of-sadd
  (equal (c1 (sadd e x)) (if (c1 x) (equal x (s1 e)) (not x))))

(defthm equal-s1-redux
  (equal (equal (s1 a) (s1 b)) (equal a b))
  :hints (("Goal" :in-theory (enable s1))))

(defthm wrap-up-s1-equal-to-c1
  (equal (equal (s1 (scar s)) s) (c1 s))
  :hints (("Goal" :in-theory (enable s1 scar c1))))

(defthm c1-in-redux-scar
  (implies (c1 s) (equal (in e s) (equal e (scar s))))
  :hints (("Goal" :in-theory (enable in c1 scar))))

(local
(defthm setp-cons-redux
  (equal (setp (cons x y))
         (and (setp y) (implies y (<< x (car y)))))))

(defthm equal-sadd-s1-redux
  (equal (equal (sadd e x) (s1 a))
         (and (equal e a) (implies x (equal x (s1 e)))))
  :hints (("Goal" :in-theory (enable s1 unite norm->set set->norm)
           :expand ((unite-aux (list e) x)))))




#|



> I propose the following additions to the sets book:
>
> (defthm sdiff-x-x
>   (equal (sdiff x x)
> 	 (empty-set)))

The following rule subsumes yours and I think would be
a better addition:

(defthm sdiff-superset
  (implies (subset x y)
           (equal (sdiff x y)
                  (empty-set))))

> ;(add similar lemmas about other functions than unite
> (e.g., isect)?
> (defthm unite-reflexes-2
>   (equal (unite x (unite x y))
> 	 (unite x y)))
>
> ;and can you prove this one for me?
> (defthm sdiff-sdiff
>   (equal (sdiff (sdiff x y) y)
> 	 (sdiff x y))
> )

absorption rules for unite, isect, and sdiff (on the right)
would be good. I have no idea why I had not considered adding
these before. I will probably generalize them to have subset
hypothesis.

> BTW, what's the status of the sets book?  Will it be
> released with ACL2?

It is in one of the workshops, although I am uncertain if it
is updated. I will probably get Matt to add it to the misc
directory (especially with some of the recent additions to
the records book which make use of the sets book).

> I also need:
>
> (defthm unite-sdiff-hack
>   (equal (unite x (sdiff y x))
> 	 (unite x y)))

Hmmm. I am uncertain if this is a proper reduction. Intuitively,
while the lhs is a bigger term, it is smaller in terms of
cardinality. I will need to think about this case, but offhand,
I don't see this as an obviously good addition to the sets book.

> (BTW, I'm assuming its okay to ask you to prove these
> since they'd make good additions to the sets book,
> which you are developing.  If you'd rather not be
> bothered with this, let me know.)

Please feel free to make suggestions (just don't expect that I
will always be quick in handling the suggestions). I like using
the sets book and would like to see others use it as well. (I am
generally an advocate of having books with rewrite rules which
are "context-free" -- well as context-free as possible).

  -Rob


> i talked with Matt (the other "old-timer") and we
> are
> in tacit agreement that we should change
> "records.lisp"
> to "maps.lisp" (the new version with all of the
> various
> improvements and which includes the sets book). But,
> I want to wait ask about this at the next ACL2
> meeting
> to get an idea of how many people (if any) are using
> the
> records book.

Excellent.

My sense is that people aren't using the records/maps
book enough (and that, in general, people don't
appreciate the importance of the tricks done to make
the records book clean).  Did anyone ever give a talk
on records/maps at the ACL2 seminar?

I'm changing my copy of the "M5" JVM model to use
records, and I think this is clearly the way to go.
(There are some subtleties, but I now have a fairly
clean algebra for the heap.)  If J's folks keep
hearing about this from enough people, maybe they'll
use records for M6.  Hanbing seems to be in charge of
M6.

> > BTW, are there easy proofs for either of the
> following
> > (which I've left as axioms in order to get on with
> my
> > JVM proofs)?  I'm not terribly familiar with the
> sets
> > book, and I didn't find an easy proof for these.
> >
> > (defaxiom sdiff-sdiff
> >   (equal (ACL2::SDIFF (ACL2::SDIFF Z X) X)
> > 	 (ACL2::SDIFF Z X)))
> >
> > (defaxiom unite-hack
> >   (equal (acl2::unite x (acl2::sdiff z x))
> > 	 (acl2::unite x z)))
>
> I believe these are provable, but not easily proven
> in
> terms of the existing rules.
>
> I am planning on doing some work with the records (I
> mean
> "maps") and sets books this weekend. The updates
> should
> cover these theorems (and many others). I will send
> them
> to you on Monday.

That would be great!  Thanks.  I've been spending a
lot of time making changes to M5 and thinking about
sets, maps, and other implementation details, instead
of actually doing the proofs I'm supposed to be doing
(about java.util.linkedlist).  Even so, Dill seems
satisfied with my progress.  Once we get the JVM model
(and the sets and maps books) stabilized, I should be
much more productive and should be able to totally
impress him.

Thanks,
-Eric


__________________________________________________
Do you Yahoo!?
Yahoo! Tax Center - forms, calculators, tips, more
http://taxes.yahoo.com/




|#
