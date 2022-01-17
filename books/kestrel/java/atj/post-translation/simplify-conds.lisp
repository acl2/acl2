; Java Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "../java-syntax-operations")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-post-translation-simplify-conds
  :parents (atj-post-translation)
  :short "Post-translation step:
          simplify conditional expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The translation step may produce Java conditional expressions
     @('... ? ... : ...') whose condition is a Java boolean literal,
     i.e. either @('true') or @('false').
     In either case, the expression may be always replaced with
     the appropriate branch, making the code more readable and efficient.")
   (xdoc::p
    "This kind of Java conditional expressions arise, in particular,
     when the quoted constants @('t') and @('nil') in ACL2,
     which are translated to the Java's literals @('true') and @('false'),
     are used as symbols (not as booleans),
     thus generating Java code to convert them to
     @('Acl2Symbol.T') and @('Acl2Symbol.NIL').")
   (xdoc::p
    "This post-translation step carries out this simplification."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-simplify-conds-in-jexpr
  :short "Simplify conditional expressions
          whose condition is a boolean literal,
          in expressions."

  (define atj-simplify-conds-in-jexpr ((expr jexprp))
    :returns (new-expr jexprp)
    (jexpr-case
     expr
     :literal (jexpr-fix expr)
     :name (jexpr-fix expr)
     :newarray (jexpr-newarray expr.type
                               (atj-simplify-conds-in-jexpr expr.size))
     :newarray-init (jexpr-newarray-init expr.type
                                         (atj-simplify-conds-in-jexprs
                                          expr.init))
     :array (jexpr-array (atj-simplify-conds-in-jexpr expr.array)
                         (atj-simplify-conds-in-jexpr expr.index))
     :newclass (jexpr-newclass expr.type
                               (atj-simplify-conds-in-jexprs expr.args))
     :field (jexpr-field (atj-simplify-conds-in-jexpr expr.target)
                         expr.name)
     :method (jexpr-method expr.name
                           (atj-simplify-conds-in-jexprs expr.args))
     :smethod (jexpr-smethod expr.type
                             expr.name
                             (atj-simplify-conds-in-jexprs expr.args))
     :imethod (jexpr-imethod (atj-simplify-conds-in-jexpr expr.target)
                             expr.name
                             (atj-simplify-conds-in-jexprs expr.args))
     :postinc (jexpr-postinc (atj-simplify-conds-in-jexpr expr.arg))
     :postdec (jexpr-postdec (atj-simplify-conds-in-jexpr expr.arg))
     :cast (jexpr-cast expr.type
                       (atj-simplify-conds-in-jexpr expr.arg))
     :unary (jexpr-unary expr.op
                         (atj-simplify-conds-in-jexpr expr.arg))
     :binary (jexpr-binary expr.op
                           (atj-simplify-conds-in-jexpr expr.left)
                           (atj-simplify-conds-in-jexpr expr.right))
     :instanceof (jexpr-instanceof (atj-simplify-conds-in-jexpr expr.left)
                                   expr.right)
     :cond (b* ((new-test (atj-simplify-conds-in-jexpr expr.test))
                ((when (jexpr-equiv new-test
                                    (jexpr-literal-true)))
                 (atj-simplify-conds-in-jexpr expr.then))
                ((when (jexpr-equiv new-test
                                    (jexpr-literal-false)))
                 (atj-simplify-conds-in-jexpr expr.else)))
             (jexpr-cond new-test
                         (atj-simplify-conds-in-jexpr expr.then)
                         (atj-simplify-conds-in-jexpr expr.else)))
     :paren (jexpr-paren (atj-simplify-conds-in-jexpr expr.get)))
    :measure (jexpr-count expr))

  (define atj-simplify-conds-in-jexprs ((exprs jexpr-listp))
    :returns (new-exprs jexpr-listp)
    (cond ((endp exprs) nil)
          (t (cons (atj-simplify-conds-in-jexpr (car exprs))
                   (atj-simplify-conds-in-jexprs (cdr exprs)))))
    :measure (jexpr-list-count exprs))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-simplify-conds-in-jexprs)

  (fty::deffixequiv-mutual atj-simplify-conds-in-jexpr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-simplify-conds-in-jstatems+jblocks
  :short "Simplify conditional expressions
          whose condition is a boolean literal,
          in statements and blocks."

  (define atj-simplify-conds-in-jstatem ((statem jstatemp))
    :returns (new-statem jstatemp)
    (jstatem-case
     statem
     :locvar (jstatem-locvar statem.get)
     :expr (jstatem-expr (atj-simplify-conds-in-jexpr statem.get))
     :return (jstatem-return
              (and statem.expr?
                   (atj-simplify-conds-in-jexpr statem.expr?)))
     :throw (jstatem-throw (atj-simplify-conds-in-jexpr statem.expr))
     :break (jstatem-break)
     :continue (jstatem-continue)
     :if (jstatem-if (atj-simplify-conds-in-jexpr statem.test)
                     (atj-simplify-conds-in-jblock statem.then))
     :ifelse (jstatem-ifelse (atj-simplify-conds-in-jexpr statem.test)
                             (atj-simplify-conds-in-jblock statem.then)
                             (atj-simplify-conds-in-jblock statem.else))
     :while (jstatem-while (atj-simplify-conds-in-jexpr statem.test)
                           (atj-simplify-conds-in-jblock statem.body))
     :do (jstatem-do (atj-simplify-conds-in-jblock statem.body)
                     (atj-simplify-conds-in-jexpr statem.test))
     :for (jstatem-for (atj-simplify-conds-in-jexpr statem.init)
                       (atj-simplify-conds-in-jexpr statem.test)
                       (atj-simplify-conds-in-jexpr statem.update)
                       (atj-simplify-conds-in-jblock statem.body)))
    :measure (jstatem-count statem))

  (define atj-simplify-conds-in-jblock ((block jblockp))
    :returns (new-block jblockp)
    (cond ((endp block) nil)
          (t (cons (atj-simplify-conds-in-jstatem (car block))
                   (atj-simplify-conds-in-jblock (cdr block)))))
    :measure (jblock-count block))

  :verify-guards nil
  ///
  (verify-guards atj-simplify-conds-in-jstatem)

  (fty::deffixequiv-mutual atj-simplify-conds-in-jstatems+jblocks))
