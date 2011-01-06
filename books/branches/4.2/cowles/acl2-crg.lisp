#| This is the .lisp file for the Commutative Ring book.

   John Cowles, University of Wyoming, Summer 1993

   Modified A. Flatau  2-Nov-1994
     Added a :verify-guards t hint to PRED for Acl2 1.8.

   To use this book execute the event:

(include-book
 "acl2-crg")

    ========================================================
    The following is required for certification of this book.

(defpkg 
  "ACL2-CRG"
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

(certify-book "acl2-crg" 2)

   ============================================
   The following documentation is from the file
   /home/cowles/acl2-libs/ver1.3/libs.doc

(deflabel 
  commutative-rings
  :doc
  ":Doc-Section Libraries

   Axiomatization of two associative and commutative operations,
               one distributes over the other, while the other
               has an identity and an unary inverse operation.~/
         
   Axiomatization by J. Cowles, University of Wyoming, Summer 1993.

   See :DOC ~/

   Theory of Commutative Rings.

    ACL2-CRG::plus and ACL2-CRG::times are associative and commutative
    binary operations on the set (of equivalence classes formed by the
    equivalence relation, ACL2-CRG::equiv, on the set) RG = { x |
    (ACL2-CRG::pred x) not equal nil } with ACL2-CRG::times distributing
    over ACL2-CRG::plus.

    ACL2-CRG::zero is a constant in the set RG which acts as an unit for
    ACL2-CRG::plus.

    ACL2-CRG::minus is an unary operation on the set (of equivalence
    classes formed by the equivalence relation, ACL2-CRG::equiv, on the
    set) RG which acts as an ACL2-CRG::plus-inverse for ACL2-CRG::zero.

    For example, let ACL2-CRG::pred  = Booleanp,
                     ACL2-CRG::plus  = exclusive-or, 
                     ACL2-CRG::times = and,
                     ACL2-CRG::zero  = nil, and
                     ACL2-CRG::minus = identity function.

   Axioms of the theory of Commutative Rings.
     Do :PE on the following events to see the details.

     [Note. The actual names of these events are obtained by 
      adding the prefix ACL2-CRG:: to each name listed below.]

     Equiv-is-an-equivalence
     Equiv-1-implies-equiv-plus
     Equiv-2-implies-equiv-plus
     Equiv-2-implies-equiv-times
     Equiv-1-implies-equiv-minus

     Closure-of-plus-for-pred
     Closure-of-times-for-pred
     Closure-of-zero-for-pred
     Closure-of-minus-for-pred

     Commutativity-of-plus
     Commutativity-of-times

     Associativity-of-plus
     Associativity-of-times

     Left-distributivity-of-times-over-plus

     Left-unicity-of-zero-for-plus
     Right-inverse-for-plus

   Theorems of the theory of Commutative Rings.
     Do :PE on the following events to see the details.

     [Note. The actual names of these events are obtained by 
      adding the prefix ACL2-CRG:: to each name listed below.]

     Right-distributivity-of-times-over-plus

     Left-nullity-of-zero-for-times
     Right-nullity-of-zero-for-times

     Functional-commutativity-of-minus-times-right
     Functional-commutativity-of-minus-times-left

     [Note. <RG, ACL2-CRG::plus> and <RG, ACL2-CRG::times>
      are both semigroups, and 
      <RG, ACL2-CRG::plus, ACL2-CRG::minus, ACL2-CRG::zero>
      is an Abelian Group. Thus, additional theorems of the
      theory of Commutative Rings may be obtained as instances
      of the theorems of the theories of Abelian Semigroups and 
      Abelian Groups.]~/

   :cite libraries-location")
|#
(in-package "ACL2-CRG")

(include-book "acl2-agp" :load-compiled-file nil)

(encapsulate
  ((equiv ( x y ) t)
   (pred ( x ) t)
   (plus ( x y ) t)
   (times ( x y ) t)
   (zero ( ) t)
   (minus ( x ) t))

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
      plus ( x y )
      (declare (xargs :guard (and (pred x)
                                  (pred y))))
      (and (or x y)
           (not (and x y)))))

  (local
    (defun
      times ( x y )
      (declare (xargs :guard (and (pred x)
                                  (pred y))))
      (and x y)))

  (local
    (defun
      zero ( )
      nil))

  (local
    (defun
      minus ( x )
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
    Equiv-1-implies-equiv-plus
    (implies (equiv x1 x2)
             (equiv (plus x1 y)
                    (plus x2 y)))
    :rule-classes :CONGRUENCE)

  (defthm
    Equiv-2-implies-equiv-plus
    (implies (equiv y1 y2)
             (equiv (plus x y1)
                    (plus x y2)))
    :rule-classes :CONGRUENCE)

  (defthm
    Equiv-2-implies-equiv-times
    (implies (equiv y1 y2)
             (equiv (times x y1)
                    (times x y2)))
    :rule-classes :CONGRUENCE)

  (defthm
    Equiv-1-implies-equiv-minus
    (implies (equiv x1 x2)
             (equiv (minus x1)
                    (minus x2)))
    :rule-classes :CONGRUENCE)

  (defthm 
    Closure-of-plus-for-pred
    (implies (and (pred x)
                  (pred y))
             (pred (plus x y))))

  (defthm 
    Closure-of-times-for-pred
    (implies (and (pred x)
                  (pred y))
             (pred (times x y))))

  (defthm
    Closure-of-zero-for-pred
    (pred (zero)))

  (defthm
    Closure-of-minus-for-pred
    (implies (pred x)
             (pred (minus x))))

  (defthm
    Commutativity-of-plus
    (implies (and (pred x)
                  (pred y))
             (equiv (plus x y)
                    (plus y x))))

  (defthm
    Commutativity-of-times
    (implies (and (pred x)
                  (pred y))
             (equiv (times x y)
                    (times y x))))

  (defthm 
    Associativity-of-plus
    (implies (and (pred x)
                  (pred y)
                  (pred z))
             (equiv (plus (plus x y) z)
                    (plus x (plus y z)))))

  (defthm 
    Associativity-of-times
    (implies (and (pred x)
                  (pred y)
                  (pred z))
             (equiv (times (times x y) z)
                    (times x (times y z)))))

  (defthm 
    Left-distributivity-of-times-over-plus
    (implies (and (pred x)
                  (pred y)
                  (pred z))
             (equiv (times  x (plus y z))
                    (plus (times x y)
                          (times x z)))))

  (defthm
    Left-unicity-of-zero-for-plus
    (implies (pred x)
             (equiv (plus (zero) x)
                    x)))

  (defthm
    Right-inverse-for-plus
    (implies (pred x)
             (equiv (plus x (minus x))
                    (zero)))))

(defthm 
  Right-distributivity-of-times-over-plus
  (implies (and (pred x)
                (pred y)
                (pred z))
           (equiv (times (plus x y) z)
                  (plus (times x z)
                        (times y z)))))

(defthm
  Left-nullity-of-zero-for-times
  (implies (pred x)
           (equiv (times (zero) x)
                  (zero)))
  :hints (("Goal"
           :use ((:instance
                  (:functional-instance
                   acl2-agp::Uniqueness-of-id-as-op-idempotent
                   (acl2-agp::equiv equiv)
                   (acl2-agp::pred pred)
                   (acl2-agp::op plus)
                   (acl2-agp::id zero)
                   (acl2-agp::inv minus))
                  (acl2-agp::x (times (zero) x)))
                 (:instance
                  Left-distributivity-of-times-over-plus       
                  (y (zero))
                  (z (zero)))))))

(defthm
  Right-nullity-of-zero-for-times
  (implies (pred x)
           (equiv (times x (zero))
                  (zero))))

(defthm
  Functional-commutativity-of-minus-times-right
  (implies (and (pred x)
                (pred y))
           (equiv (times x
                         (minus y))
                  (minus (times x y))))
  :hints (("Goal"
           :use ((:instance
                  (:functional-instance
                   acl2-agp::Uniqueness-of-op-inverses
                   (acl2-agp::equiv equiv)
                   (acl2-agp::pred pred)
                   (acl2-agp::op plus)
                   (acl2-agp::id zero)
                   (acl2-agp::inv minus))
                  (acl2-agp::x (times x y))
                  (acl2-agp::y (times x (minus y))))
                 (:instance
                  Left-distributivity-of-times-over-plus
                  (z (minus y)))))))

(defthm
  Functional-commutativity-of-minus-times-left
  (implies (and (pred x)
                (pred y))
           (equiv (times (minus x)
                         y)
                  (minus (times x y)))))
