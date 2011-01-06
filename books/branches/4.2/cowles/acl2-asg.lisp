#| This is the .lisp file for the Abelian SemiGroup book.

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
       "acl2-asg")

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

(certify-book 
  "acl2-asg"
  1
  nil)

   ============================================
   The following documentation is from the file
   /meru0/cowles/acl2-libs/ver1.6/libs.doc

(deflabel 
  abelian-semigroups
  :doc
  ":Doc-Section Libraries

   Axiomatization of an associative and commutative binary operation.~/

   Axiomatization by J. Cowles, University of Wyoming, Summer 1993.

   See :DOC ~/

   Theory of Abelian SemiGroups.

    ACL2-ASG::op is an associative and commutative binary operation on the
    set (of equivalence classes formed by the equivalence relation,
    ACL2-ASG::equiv, on the set) { x | (ACL2-ASG::pred x) not equal nil }.

    Exclusive-or on the set of Boolean values with the equivalence
    relation, EQUAL, is an example.

   Note, it is recommended that a second version of commutativity, called
   Commutativity-2, be added as a :REWRITE rule for any operation which
   has both Associative and Commutative :REWRITE rules. The macro
   ACL2-ASG::Add-Commutativity-2 may be used to add such a rule. 
   See :DOC Add-Commutativity-2.

   Axioms of the theory of Abelian Semigroups.
      Do :PE on the following events to see the details.

      [Note. The actual names of these events are obtained by 
       adding the prefix ACL2-ASG:: to each name listed below.]

      Equiv-is-an-equivalence
      Equiv-2-implies-equiv-op
      Closure-of-op-for-pred
      Associativity-of-op
      Commutativity-of-op

   Theorem of the theory of Abelian Groups.
      Do :PE on the following events to see the details.

      [Note. The actual name of this event is obtained by 
       adding the prefix ACL2-ASG:: to the name listed below.]

      Commutativity-2-of-op~/

   :cite libraries-location")

(deflabel 
  add-commutativity-2
  :doc
  ":Doc-Section Libraries

   Macro for adding a second version of commutativity.~/

   Examples:

   (acl2-asg::add-commutativity-2 equal
                                  rationalp
                                  *
                                  commutativity-of-*
                                  commutativity-2-of-*)

   (acl2-asg::add-commutativity-2 acl2-bag::bag-equal
                                  true-listp
                                  acl2-bag::bag-union
                                  acl2-bag::commutativity-of-bag-union
                                  commutativity-2-of-bag-union)

   Macro by J. Cowles, University of Wyoming, Summer 1993.
     This documentation last modified 19 Jan. 1994.

   See :DOC ~/

   General Form:

   (acl2-asg::add-commutativity-2 equiv-name
                                  pred-name
                                  op-name
                                  commutativity-thm-name
                                  commutativity-2-thm-name)

   where all the arguments are names.  Equiv-name is the name of an
   equivalence relation, equiv; pred-name is the name of a unary
   function, pred; op-name is the name of a binary function, op;
   commutativity-thm-name is the name of theorem which added a :REWRITE
   rule to the data base saying that the operation op is commutative on
   the set (of equivalence classes formed by the equivalence relation,
   equiv, on the set) SG = { x | (pred x) not equal nil }.  There must
   be rules in the data base for the closure of SG under op and the
   associativity with respect to equiv of op on SG.  The macro adds a
   rewrite rule for a second version of the commutativity with respect to
   equiv of op on SG.  This is done by proving a theorem named
   commutativity-2-thm-name.

   Here is the form of the rule added by the macro:

    (DEFTHM
      commutativity-2-thm-name
      (IMPLIES (AND (PRED X)
                    (PRED Y)
                    (PRED Z))
               (EQUIV (OP X (OP Y Z))
                      (OP Y (OP X Z))))) .

   Here is what is meant by \"closure of SG under op\":

    (IMPLIES (AND (PRED X)
                  (PRED Y))
             (PRED (OP X Y))) .

   Here is what is meant by \"associativity with respect to equiv of
   op on SG\":

    (IMPLIES (AND (PRED X)
                  (PRED Y)
                  (PRED Z))
             (EQUIV (OP (OP X Y) Z)
                    (OP X (OP Y Z)))) .

   Here is the form of the commutativity rule:

    (DEFTHM
      commutativity-thm-name    
      (IMPLIES (AND (PRED X)
                    (PRED Y))
               (EQUIV (OP X Y)
                      (OP Y X)))))

   :cite abelian-semigroups
   :cite libraries-location")
|#

(in-package "ACL2-ASG")

(encapsulate
  ((equiv ( x y ) t)
   (pred ( x ) t)
   (op ( x y ) t))

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

  (defthm
    Equiv-is-an-equivalence
    (and (acl2::booleanp (equiv x y))
         (equiv x x)
         (implies (equiv x y) 
                  (equiv y x))
         (implies (and (equiv x y)
                       (equiv y z))
                  (equiv x z)))
    :rule-classes :EQUIVALENCE)

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
    Associativity-of-op
    (implies (and (pred x)
                  (pred y)
                  (pred z))
             (equiv (op (op x y) z)
                    (op x (op y z)))))

  (defthm
    Commutativity-of-op
    (implies (and (pred x)
                  (pred y))
             (equiv (op x y)
                    (op y x)))))

 ; Provide 2nd version of Commutativity of op:

(local
 (defthm
   commutativity-2-of-op-lemma
   (implies (and (pred x)
                 (pred y)
                 (pred z))
            (equiv (op (op x y) z)
                   (op (op y x) z)))
   :rule-classes nil))

(defthm
  Commutativity-2-of-op
  (implies (and (pred x)
                (pred y)
                (pred z))
           (equiv (op x (op y z))
                  (op y (op x z))))
  :hints (("Goal"
           :in-theory (acl2::disable commutativity-of-op)
           :use commutativity-2-of-op-lemma)))

(defmacro
  add-commutativity-2 ( equiv-name
                        pred-name
                        op-name
                        commutativity-thm-name
                        commutativity-2-thm-name )

             "Assume equiv-name is the name of an equivalence relation, equiv;
                     pred-name  is the name of a unary function, pred;
                     op-name    is the name of a binary function, op;
                     commutativity-thm-name 
                                is the name of theorem which added a rewrite rule
                                to the data base saying that the operation op is 
                                commutative on the set (of equivalence classes 
                                formed by the equivalence relation, equiv, on the 
                                set) SG = { x | (pred x) /= nil };
                     there are rules in the data base for the closure of SG under 
                                op and the associativity with respect to equiv of 
                                op on SG.
              The macro adds a rewrite rule for a second version of the
                     commutativity with respect to equiv of op on SG. 
                     This is done by proving a theorem named 
                     commutativity-2-thm-name."

  (declare (xargs :guard (and (symbolp equiv-name)
                              (symbolp pred-name)
                              (symbolp op-name)
                              (symbolp commutativity-thm-name)
                              (symbolp commutativity-2-thm-name))))
  `(encapsulate
    nil
    (local
     (defthm
       Associativity-of-op-name
       ; Temporarily ensure that the associativity rewrite rule
       ; comes after the commutativity rewrite rule.
       (IMPLIES (AND (,pred-name X)
                     (,pred-name Y)
                     (,pred-name Z))
                (,equiv-name (,op-name (,op-name X Y) Z)
                             (,op-name X (,op-name Y Z))))
       :hints (("Goal"
                :in-theory (acl2::disable ,commutativity-thm-name)))))

    (defthm
      ,commutativity-2-thm-name
      (implies (and (,pred-name x)
                    (,pred-name y)
                    (,pred-name z))
               (,equiv-name (,op-name x (,op-name y z))
                            (,op-name y (,op-name x z))))
      :hints (("Goal"
               :use (:functional-instance
                     ACL2-ASG::Commutativity-2-of-op
                     (ACL2-ASG::equiv (lambda (x y)(,equiv-name x y)))
                     (ACL2-ASG::pred (lambda (x)(,pred-name x)))
                     (ACL2-ASG::op (lambda (x y)(,op-name x y)))))))))
