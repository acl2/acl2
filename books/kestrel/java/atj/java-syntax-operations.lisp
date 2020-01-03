; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "java-abstract-syntax")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-java-syntax-operations
  :parents (atj-implementation)
  :short "Operations on the Java abstract syntax used by ATJ."
  :long
  (xdoc::topstring
   (xdoc::p
    "These operartions, like the "
    (xdoc::seetopic "atj-java-abstract-syntax" "abstract syntax of Java")
    ", are more general than ATJ and will be eventually moved
     to a new library for manipulating Java code.
     For now, these are parts of ATJ, which is their only user so far."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines jexpr-vars
  :short "Variables in a Java expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return all the names in expression names.
     The list is without duplicates but in no particular order."))

  (define jexpr-vars ((expr jexprp))
    :returns (vars string-listp)
    (jexpr-case expr
                :literal nil
                :name (list expr.get)
                :newarray (jexpr-vars expr.size)
                :newarray-init (jexpr-list-vars expr.init)
                :array (union-equal (jexpr-vars expr.array)
                                    (jexpr-vars expr.index))
                :newclass (jexpr-list-vars expr.args)
                :field (jexpr-vars expr.target)
                :method (jexpr-list-vars expr.args)
                :smethod (jexpr-list-vars expr.args)
                :imethod (union-equal (jexpr-vars expr.target)
                                      (jexpr-list-vars expr.args))
                :postinc (jexpr-vars expr.arg)
                :postdec (jexpr-vars expr.arg)
                :cast (jexpr-vars expr.arg)
                :unary (jexpr-vars expr.arg)
                :binary (union-equal (jexpr-vars expr.left)
                                     (jexpr-vars expr.right))
                :instanceof (jexpr-vars expr.left)
                :cond (union-equal (jexpr-vars expr.test)
                                   (union-equal (jexpr-vars expr.then)
                                                (jexpr-vars expr.else)))
                :paren (jexpr-vars expr.get))
    :measure (jexpr-count expr))

  (define jexpr-list-vars ((exprs jexpr-listp))
    :returns (vars string-listp)
    (cond ((endp exprs) nil)
          (t (union-equal (jexpr-vars (car exprs))
                          (jexpr-list-vars (cdr exprs)))))
    :measure (jexpr-list-count exprs))

  :prepwork
  ((local (include-book "std/typed-lists/string-listp" :dir :system)))

  :verify-guards nil ; done below
  ///
  (local (include-book "std/lists/union" :dir :system))
  (verify-guards jexpr-vars))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines jstatems+jblocks-count-ifs
  :short "Number of @('if')s in a statement or block."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is useful as a measure for certain recursive functions.")
   (xdoc::p
    "We prove some theorems about the results of these counting functions.
     Additional similar theorems could be added as needed."))

  (define jstatem-count-ifs ((statem jstatemp))
    :returns (count natp)
    (jstatem-case statem
                  :locvar 0
                  :expr 0
                  :return 0
                  :throw 0
                  :break 0
                  :continue 0
                  :if (1+ (jblock-count-ifs statem.then))
                  :ifelse (1+ (+ (jblock-count-ifs statem.then)
                                 (jblock-count-ifs statem.else)))
                  :while (jblock-count-ifs statem.body)
                  :do (jblock-count-ifs statem.body)
                  :for (jblock-count-ifs statem.body))
    :measure (jstatem-count statem))

  (define jblock-count-ifs ((block jblockp))
    :returns (count natp)
    (cond ((endp block) 0)
          (t (+ (jstatem-count-ifs (car block))
                (jblock-count-ifs (cdr block)))))
    :measure (jblock-count block))

  ///

  (defrule jblock-count-ifs-of-cons
    (equal (jblock-count-ifs (cons statem block))
           (+ (jstatem-count-ifs statem)
              (jblock-count-ifs block))))

  (defrule jblock-count-ifs-of-append
    (equal (jblock-count-ifs (append block1 block2))
           (+ (jblock-count-ifs block1)
              (jblock-count-ifs block2)))
    :enable append)

  (defrule jstatem-count-ifs-of-return
    (equal (jstatem-count-ifs (jstatem-return expr?))
           0))

  (defrule jblock-count-ifs-of-jstatem-if->then-decreases
    (implies (jstatem-case statem :if)
             (< (jblock-count-ifs (jstatem-if->then statem))
                (jstatem-count-ifs statem)))
    :rule-classes :linear
    :expand ((jstatem-count-ifs statem)))

  (defrule jblock-count-ifs-of-jstatem-ifelse->then-decreases
    (implies (jstatem-case statem :ifelse)
             (< (jblock-count-ifs (jstatem-ifelse->then statem))
                (jstatem-count-ifs statem)))
    :rule-classes :linear
    :expand ((jstatem-count-ifs statem)))

  (defrule jblock-count-ifs-of-jstatem-ifelse->else-decreases
    (implies (jstatem-case statem :ifelse)
             (< (jblock-count-ifs (jstatem-ifelse->else statem))
                (jstatem-count-ifs statem)))
    :rule-classes :linear
    :expand ((jstatem-count-ifs statem)))

  (defrule jblock-count-ifs-of-take-not-increases
    (<= (jblock-count-ifs (take n block))
        (jblock-count-ifs block))
    :rule-classes :linear
    :enable take)

  (defrule jblock-count-ifs-of-nthcdr-not-increases
    (<= (jblock-count-ifs (nthcdr n block))
        (jblock-count-ifs block))
    :rule-classes :linear
    :enable nthcdr)

  (defrule jstatem-count-ifs-of-car-not-increases
    (<= (jstatem-count-ifs (car block))
        (jblock-count-ifs block))
    :rule-classes :linear)

  (defrule jblock-count-ifs-of-cdr-not-increases
    (<= (jblock-count-ifs (cdr block))
        (jblock-count-ifs block))
    :rule-classes :linear)

  (defrule jblock-count-ifs-positive-when-nth-ifelse
    (implies (jstatem-case (nth i block) :ifelse) ; free I
             (> (jblock-count-ifs block) 0))
    :rule-classes :linear
    :expand ((jblock-count-ifs block)
             (jstatem-count-ifs (car block)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mergesort-jfields ((fields jfield-listp))
  :returns (sorted-fields jfield-listp :hyp :guard)
  :verify-guards :after-returns
  :short "Sort a list of fields according to their names."
  (b* ((len-fields (len fields))
       ((when (<= len-fields 1)) fields)
       (len/2 (floor len-fields 2))
       (fields1 (mergesort-jfields (take len/2 fields)))
       (fields2 (mergesort-jfields (nthcdr len/2 fields))))
    (merge-jfields fields1 fields2))
  :measure (len fields)

  :prepwork

  ((local (include-book "arithmetic-5/top" :dir :system))
   (local (include-book "std/lists/take" :dir :system))
   (local (include-book "std/lists/nthcdr" :dir :system))

   (define merge-jfields ((fields1 jfield-listp) (fields2 jfield-listp))
     :returns (merged-fields jfield-listp :hyp :guard)
     (cond ((endp fields1) fields2)
           ((endp fields2) fields1)
           (t (if (string<= (jfield->name (car fields1))
                            (jfield->name (car fields2)))
                  (cons (car fields1)
                        (merge-jfields (cdr fields1) fields2))
                (cons (car fields2)
                      (merge-jfields fields1 (cdr fields2))))))
     :measure (+ (len fields1) (len fields2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mergesort-jmethods ((methods jmethod-listp))
  :returns (sorted-methods jmethod-listp :hyp :guard)
  :verify-guards :after-returns
  :short "Sort a list of methods according to their names."
  (b* ((len-methods (len methods))
       ((when (<= len-methods 1)) methods)
       (len/2 (floor len-methods 2))
       (methods1 (mergesort-jmethods (take len/2 methods)))
       (methods2 (mergesort-jmethods (nthcdr len/2 methods))))
    (merge-jmethods methods1 methods2))
  :measure (len methods)

  :prepwork

  ((local (include-book "arithmetic-5/top" :dir :system))
   (local (include-book "std/lists/take" :dir :system))
   (local (include-book "std/lists/nthcdr" :dir :system))

   (define merge-jmethods ((methods1 jmethod-listp) (methods2 jmethod-listp))
     :returns (merged-methods jmethod-listp :hyp :guard)
     (cond ((endp methods1) methods2)
           ((endp methods2) methods1)
           (t (if (string<= (jmethod->name (car methods1))
                            (jmethod->name (car methods2)))
                  (cons (car methods1)
                        (merge-jmethods (cdr methods1) methods2))
                (cons (car methods2)
                      (merge-jmethods methods1 (cdr methods2))))))
     :measure (+ (len methods1) (len methods2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define negate-boolean-jexpr ((expr jexprp))
  :returns (new-expr jexprp)
  :short "Negates a (boolean) Java expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "This accepts and transforms any Java expression.
     However, if the original expression is not boolean,
     the transformed expression is malformed (i.e. ill-typed).")
   (xdoc::p
    "If the expression is a boolean literal,
     we replace it with the other boolean literal.
     If the expression is a logical negation @('!...'),
     we remove the @('!').
     If the expression is an (in)equality or comparison,
     we negate the operator.
     In all other cases, we put @('!') before the expression,
     which is always correct and a default strategy.
     We may extend the special (i.e. non-default) handling,
     e.g. by distributing the negation over conjunctions and disjunctions,
     and over the `then' and `else' branches
     of the ternary condition operator @('? ... : ...')."))
  (b* ((default-result (jexpr-unary (junop-logcompl) expr)))
    (case (jexpr-kind expr)
      (:literal (b* ((literal (jexpr-literal->get expr)))
                  (if (jliteral-case literal :boolean)
                      (if (jliteral-boolean->value literal)
                          (jexpr-literal-false)
                        (jexpr-literal-true))
                    default-result)))
      (:unary (b* ((op (jexpr-unary->op expr))
                   (arg (jexpr-unary->arg expr)))
                (if (junop-case op :logcompl)
                    arg
                  default-result)))
      (:binary (b* ((op (jexpr-binary->op expr))
                    (left (jexpr-binary->left expr))
                    (right (jexpr-binary->right expr)))
                 (case (jbinop-kind op)
                   (:lt (jexpr-binary (jbinop-ge) left right))
                   (:gt (jexpr-binary (jbinop-le) left right))
                   (:le (jexpr-binary (jbinop-gt) left right))
                   (:ge (jexpr-binary (jbinop-lt) left right))
                   (:eq (jexpr-binary (jbinop-ne) left right))
                   (:ne (jexpr-binary (jbinop-eq) left right))
                   (otherwise default-result))))
      (otherwise default-result))))
