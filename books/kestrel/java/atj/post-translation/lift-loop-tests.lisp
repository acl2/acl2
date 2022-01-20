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

(defxdoc+ atj-post-translation-lift-loop-tests
  :parents (atj-post-translation)
  :short "Post-translation step:
          lifting to loop tests."
  :long
  (xdoc::topstring
   (xdoc::p
    "The "
    (xdoc::seetopic "atj-post-translation-tailrec-elimination"
                    "tail recursion elimination step")
    " produces method bodies of the form @('while (true) { ... }').
     When the body of the @('while') is an @('if')
     one of whose branches is a @('return'),
     then it is possible to lift the @('if') tests to the loop test,
     moving the @('return') after the loop.")
   (xdoc::p
    "More precisely, if the method body has the form")
   (xdoc::codeblock
    "while (true) {"
    "    if (<test>) {"
    "        return <expr>;"
    "    } else {"
    "        ..."
    "    }"
    "}")
   (xdoc::p
    "it can be turned into")
   (xdoc::codeblock
    "while (!<test>) {"
    "    ..."
    "}"
    "return <expr>;")
   (xdoc::p
    "Simillarly, if the method body has the form")
   (xdoc::codeblock
    "while (true) {"
    "    if (<test>) {"
    "        ...."
    "    } else {"
    "        return <expr>;"
    "    }"
    "}")
   (xdoc::p
    "it can be turned into")
   (xdoc::codeblock
    "while (<test>) {"
    "    ..."
    "}"
    "return <expr>;")
   (xdoc::p
    "This post-translation step performs these transformations,
     which produce more idiomatic looping code.
     It should be possible to extend the scope of this post-translation step,
     e.g. to cases in which the @('return') is preceded by some statements."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-check-single-return-with-expr ((block jblockp))
  :returns (mv (yes/no booleanp)
               (expr jexprp))
  :short "Check if a Java block consists of
          a single @('return') with an expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the check is successful,
     we return the expression of the @('return').
     If the check is not successful, i.e. the first result is @('nil'),
     the second result is irrelevant."))
  (b* (((fun (fail)) (mv nil (jexpr-name "")))
       ((unless (= (len block) 1)) (fail))
       (statem (car block))
       ((unless (jstatem-case statem :return)) (fail))
       (expr? (jstatem-return->expr? statem))
       ((unless expr?) (fail)))
    (mv t expr?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-check-liftable-loop-test ((block jblockp))
  :returns (mv (yes/no booleanp)
               (test jexprp)
               (return jexprp)
               (body jblockp))
  :short "Check if a Java block is a @('while (true) ...') loop
          with an @('if') body whose test can be lifted to the loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "This checks if a block has one of the two forms described "
    (xdoc::seetopic "atj-post-translation-lift-loop-tests" "here")
    ". If it does, we return its components, i.e.
     the test expression, the return expression,
     and the block that will become the body of the new loop
     (i.e. the `then' or `else' branch that is not a @('return').
     The returned test expression is the one that will become
     the test of the new loop:
     thus, it is either the same as the @('if')
     or its logical negation,
     depending on which branch is the @('return').")
   (xdoc::p
    "If the first result of this function is @('nil'),
     the other results have irrelevant values."))
  (b* (((fun (fail)) (mv nil (jexpr-name "") (jexpr-name "") nil))
       ((unless (= (len block) 1)) (fail))
       (statem (car block))
       ((unless (jstatem-case statem :while)) (fail))
       (while-test (jstatem-while->test statem))
       (while-body (jstatem-while->body statem))
       ((unless (equal while-test (jexpr-literal-true))) (fail))
       ((unless (= (len while-body) 1)) (fail))
       (statem (car while-body))
       ((unless (jstatem-case statem :ifelse)) (fail))
       (test (jstatem-ifelse->test statem))
       (then (jstatem-ifelse->then statem))
       (else (jstatem-ifelse->else statem))
       ((mv then-return-p return) (atj-check-single-return-with-expr then))
       ((when then-return-p) (mv t (negate-boolean-jexpr test) return else))
       ((mv else-return-p return) (atj-check-single-return-with-expr else))
       ((when else-return-p) (mv t test return then)))
    (fail)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-lift-loop-test ((block jblockp))
  :returns (new-block jblockp :hyp :guard)
  :short "Lift an @('if') test to the enclosing loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the block is a loop of the form described "
    (xdoc::seetopic "atj-post-translation-lift-loop-tests" "here")
    ", we transform into the equivalent code also described "
    (xdoc::seetopic "atj-post-translation-lift-loop-tests" "here")
    ". We do it only once, not recursively,
     because ATJ's ACL2-to-Java translation
     currently does not generate nested loops."))
  (b* (((mv matchp test return body) (atj-check-liftable-loop-test block))
       ((unless matchp) block))
    (append (jblock-while test body)
            (jblock-return return))))
