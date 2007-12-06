#| This is the .lisp file for the Abelian Group book.

   John Cowles, University of Wyoming, Summer 1993
     Last modified 29 July 1994.

   Modified A. Flatau  2-Nov-1994
     Added a :verify-guards t hint to PRED for Acl2 1.8.

   To use this book at the University of Wyoming:

   1. Set the Connected Book Directory to a directory containing this book.
      At one time, the argument to the following set-cbd named such a
      directory.  
           
           (set-cbd "/meru0/cowles/acl2-libs/ver1.6/")

   2. Execute the event:

      (include-book
       "acl2-agp")

    ========================================================
    The following were used for certification of this book
    at the University of Wyoming.

(set-cbd "/meru0/cowles/acl2-libs/ver1.6/")

(defpkg 
  "ACL2-ASG"
  (set-difference-equal
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)
   '(zero)))

(defpkg 
  "ACL2-AGP"
  (set-difference-equal
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)
   '(zero)))


(certify-book
  "acl2-agp"
  2
  nil)

   ============================================
   The following documentation is from the file
   /meru0/cowles/acl2-libs/ver1.6/libs.doc

(deflabel 
  abelian-groups
  :doc
  ":Doc-Section Libraries

   Axiomatization of an associative and commutative binary operation
               with an identity and an unary inverse operation.~/
         
   Axiomatization by J. Cowles, University of Wyoming, Summer 1993.
     Last modified 29 July 1994.

   See :DOC ~/

   Theory of Abelian Groups.

    ACL2-AGP::op is an associative and commutative binary operation on the
    set (of equivalence classes formed by the equivalence relation,
    ACL2-AGP::equiv, on the set) GP = { x | (ACL2-AGP::pred x) not equal
    nil }.

    ACL2-AGP::id is a constant in the set GP which acts as an unit for
    ACL2-AGP::op in GP.

    ACL2-AGP::inv is an unary operation on the set (of equivalence classes
    formed by the equivalence relation, ACL2-AGP::equiv, on the set) GP
    which acts as an ACL2-AGP::op-inverse for ACL2-AGP:: id.

    For example, let ACL2-AGP::pred = Booleanp,
                     ACL2-AGP::op   = exclusive-or, 
                     ACL2-AGP::id   = nil, and 
                     ACL2-AGP::inv  = identity function.

    Axioms of the theory of Abelian Groups.
      Do :PE on the following events to see the details.

      [Note. The actual names of these events are obtained by 
       adding the prefix ACL2-AGP:: to each name listed below.]

      Equiv-is-an-equivalence
      Equiv-1-implies-equiv-op
      Equiv-2-implies-equiv-op

      Closure-of-op-for-pred
      Closure-of-id-for-pred
      Closure-of-inv-for-pred

      Commutativity-of-op
      Associativity-of-op

      Left-unicity-of-id-for-op
      Right-inverse-of-inv-for-op

    Theorems of the theory of Abelian Groups.
      Do :PE on the following events to see the details.

      [Note. The actual names of these events are obtained by 
       adding the prefix ACL2-AGP:: to each name listed below.]

      Commutativity-2-of-op
      Right-unicity-of-id-for-op
      Left-inverse-of-inv-for-op
      Right-cancellation-for-op
      Left-cancellation-for-op
      Uniqueness-of-id-as-op-idempotent
      Uniqueness-of-op-inverses
      Uniqueness-of-op-inverses-1
      Involution-of-inv
      Distributivity-of-inv-over-op
      Id-is-its-own-invese
      Inv-cancellation-on-right
      Inv-cancellation-on-left~/

   :cite libraries-location")
|#

(in-package "ACL2-AGP")

(include-book "acl2-asg" :load-compiled-file nil)

(encapsulate
  ((equiv ( x y ) t)
   (pred ( x ) t)
   (op ( x y ) t)
   (id ( ) t)
   (inv ( x ) t))

  (local
    (defun
      equiv ( x y )
      (equal x y)))

  (local
    (defun
      pred ( x )
      (declare (xargs :verify-guards t))
      (or (equal x t)
          (equal x nil))))

  (local
    (defun
      op ( x y )
      (declare (xargs :guard (and (pred x)
                                  (pred y))))
      (and (or x y)
           (not (and x y)))))

  (local
    (defun 
      id ( )
      nil))

  (local
    (defun
      inv ( x )
      (declare (xargs :guard (pred x)))
      x))

  (defthm
    Equiv-is-an-equivalence
    (and (acl2::booleanp (equiv x y))
         (equiv x x)
         (implies (equiv x y) 
                  (equiv y x))
         (implies (and (equiv x y)
                       (equiv y z))
                  (equiv x z)))
    :rule-classes (:EQUIVALENCE
                   (:TYPE-PRESCRIPTION
                    :COROLLARY
                    (or (equal (equiv x y) t)
                        (equal (equiv x y) nil)))))

  (defthm
    Equiv-1-implies-equiv-op
    (implies (equiv x1 x2)
             (equiv (op x1 y)
                    (op x2 y)))
    :rule-classes :CONGRUENCE)

  (defthm
    Equiv-2-implies-equiv-op
    (implies (equiv y1 y2)
             (equiv (op x y1)
                    (op x y2)))
    :rule-classes :CONGRUENCE)

  (defthm 
    Closure-of-op-for-pred
    (implies (and (pred x)
                  (pred y))
             (pred (op x y))))

  (defthm
    Closure-of-id-for-pred
    (pred (id)))

  (defthm
    Closure-of-inv-for-pred
    (implies (pred x)
             (pred (inv x))))
  
  (defthm
    Commutativity-of-op
    (implies (and (pred x)
                  (pred y))
             (equiv (op x y)
                    (op y x))))

  (defthm 
    Associativity-of-op
    (implies (and (pred x)
                  (pred y)
                  (pred z))
             (equiv (op (op x y) z)
                    (op x (op y z)))))

  (defthm
    Left-unicity-of-id-for-op
    (implies (pred x)
             (equiv (op (id) x)
                    x)))

  (defthm
    Right-inverse-of-inv-for-op
    (implies (pred x)
             (equiv (op x (inv x))
                    (id)))))

(acl2-asg::add-commutativity-2 equiv
                               pred
                               op
                               commutativity-of-op
                               commutativity-2-of-op)

(defthm
  Right-unicity-of-id-for-op
  (implies (pred x)
           (equiv (op x (id))
                  x)))

(defthm
  Left-inverse-of-inv-for-op
  (implies (pred x)
           (equiv (op (inv x) x)
                  (id))))

(local
  (defthm
    Right-cancellation-for-op-iff
    (implies (and (pred x)
                  (pred y)
                  (pred z))
             (iff (equiv (op x z)
                         (op y z))
                  (equiv x y)))
    :rule-classes nil
    :hints (("Subgoal 1"
             :in-theory (disable Equiv-1-implies-equiv-op)
             :use (:instance 
                   Equiv-1-implies-equiv-op
                   (x1 (op x z))
                   (x2 (op y z))
                   (y  (inv z)))))))

(defthm
  Right-cancellation-for-op
  (implies (and (pred x)
                (pred y)
                (pred z))
           (equal (equiv (op x z)
                         (op y z))
                  (equiv x y)))
  :rule-classes nil
  :hints (("Goal"
           :use Right-cancellation-for-op-iff)))

(local
  (defthm
    Left-cancellation-for-op-iff
    (implies (and (pred x)
                  (pred y)
                  (pred z))
             (iff (equiv (op x y)
                         (op x z))                       
                  (equiv z y)))
    :rule-classes nil
    :hints (("Goal"
             :use ((:instance 
                    Right-cancellation-for-op
                    (x z)
                    (z x)))))))

(defthm
  Left-cancellation-for-op
  (implies (and (pred x)
                (pred y)
                (pred z))
           (equal (equiv (op x y)
                         (op x z))
                  (equiv y z)))
  ;rule-classes nil
  :hints (("Goal"
           :use Left-cancellation-for-op-iff)))

(defthm
  Uniqueness-of-id-as-op-idempotent
  (implies (and (pred x)
                (equiv (op x x)
                       x))
           (equiv x (id)))
  :rule-classes nil
  :hints (("Goal"
           :use (:instance
                 Right-cancellation-for-op
                 (y (id))
                 (z x)))))

(defthm
  Uniqueness-of-op-inverses
  (implies (and (pred x)
                (pred y)
                (equiv (op x y)
                       (id)))
           (equiv y (inv x)))
  :rule-classes nil 
  :hints (("Goal"
           :use (:instance
                 Right-cancellation-for-op
                 (x y)
                 (y (inv x))
                 (z x)))))

(defthm
  Involution-of-inv
  (implies (pred x)
           (equiv (inv (inv x))
                  x))
  :hints (("Goal"
           :use (:instance
                 Uniqueness-of-op-inverses
                 (x (inv x))
                 (y x)))))

(defthm
  Uniqueness-of-op-inverses-1
  (implies (and (pred x)
                (pred y)
                (equiv (op x (inv y))
                       (id)))
           (equiv x y))
  :rule-classes nil
  :hints (("Goal"
           :use (:instance
                 Uniqueness-of-op-inverses
                 (y x)
                 (x (inv y))))))

(defthm
  Distributivity-of-inv-over-op
  (implies (and (pred x)
                (pred y))
           (equiv (inv (op x y))
                  (op (inv x)
                      (inv y))))
  :hints (("Goal"
           :use (:instance
                 Uniqueness-of-op-inverses
                 (x (op x y))
                 (y (op (inv x)(inv y)))))))

(defthm
  id-is-its-own-invese
  (equiv (inv (id))
         (id))
  :hints (("Goal"
           :use (:instance
                 Uniqueness-of-op-inverses
                 (x (id))
                 (y (id))))))

(local
  (defthm
    obvious-inv-cancellation
    (implies (and (pred x)
                  (pred y))
             (equiv (op (op x (inv x)) y) y))
    :rule-classes nil))

(defthm
  inv-cancellation-on-right
  (implies (and (pred x)
                (pred y))
           (equiv (op x (op y (inv x)))
                  y))
  :hints (("Goal"
           :use obvious-inv-cancellation
           :in-theory (acl2::disable 
                       right-inverse-of-inv-for-op))))

(defthm
  inv-cancellation-on-left
  (implies (and (pred x)
                (pred y))
           (equiv (op x (op (inv x) y))
                  y)))
