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

(defxdoc+ atj-post-translation-fold-returns
  :parents (atj-post-translation)
  :short "Post-translation step:
          folding of @('return')s into @('if')s."
  :long
  (xdoc::topstring
   (xdoc::p
    "ATJ's ACL2-to-Java translation
     introduces a Java local variable for every @(tsee if) in ACL2:
     the variable is assigned in the `then' and `else' branches,
     and then used in subsequent Java code.
     When the subsequent Java code is simply a @('return'),
     the body of a Java method would look like this:")
   (xdoc::codeblock
    "..."
    "<type> <result> = null;"
    "if (...) {"
    "    ..."
    "    <result> = <then>;"
    "} else {"
    "    ..."
    "    <result> = <else>;"
    "}"
    "return <result>;")
   (xdoc::p
    "This post-translation step folds the @('return') into the @('if'),
     turning this code into the following form:")
   (xdoc::codeblock
    "..."
    "if (...) {"
    "    ..."
    "    return <then>;"
    "} else {"
    "    ..."
    "    return <else>;"
    "}")
   (xdoc::p
    "In fact, it does so recursively:
     if the new `then' and/or `else' branch has the same form as above
     (i.e. @('<then>') and/or @('<else>') is a result variable
     introduced for a nested @('if')),
     we keep folding @('return')s into @('if')s.")
   (xdoc::p
    "The function @(tsee atj-gen-shallow-fndef-method),
     which translates an ACL2 function to a Java method,
     always produces a method body that ends with a single @('return').
     This post-translation step may replace that single @('return')
     with a number of @('return')s, inside different conditional branches.
     This is more readable and idiomatic Java code."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-check-foldable-return ((block jblockp))
  :returns (mv (yes/no booleanp)
               (pre-block jblockp :hyp :guard)
               (test-expr jexprp)
               (then-block jblockp)
               (then-expr jexprp)
               (else-block jblockp)
               (else-expr jexprp))
  :short "Check if a Java block has an ending @('return')
          that is foldable into an immediately preceding @('if')."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check whether the block has the structure described "
    (xdoc::seetopic "atj-post-translation-fold-returns" "here")
    ". If it does, we return its components, i.e.
     the block that precedes the declaration of the result variable,
     the `then' block without the final assignment to the result variable,
     the expression assigned to the result variable in the `then' block,
     the `else' block without the final assignment to the result variable,
     and the expression assigned to the result variable in the `else' block.")
   (xdoc::p
    "If the first result of this function is @('nil'),
     the other results have irrelevant values.")
   (xdoc::p
    "We prove that, if the first result is @('t'),
     the @('then-block') and @('else-block') results
     have strictly fewer @('if')s than the input block.
     This is used to prove the termination of @(tsee atj-fold-returns),
     which processes those blocks recursively."))
  (b* (((fun (fail))
        (mv nil nil (jexpr-name "") nil (jexpr-name "") nil (jexpr-name "")))
       ((unless (>= (len block) 3)) (fail))
       (pre-block (butlast block 3))
       (rest-block (nthcdr (len pre-block) block))
       (3rd-to-last-statem (car rest-block))
       (2nd-to-last-statem (cadr rest-block))
       (last-statem (caddr rest-block))
       ((unless (jstatem-case last-statem :return)) (fail))
       (return-expr? (jstatem-return->expr? last-statem))
       ((when (null return-expr?)) (fail))
       (return-expr return-expr?)
       ((unless (jexpr-case return-expr :name)) (fail))
       (result-var (jexpr-name->get return-expr))
       ((unless (jstatem-case 2nd-to-last-statem :ifelse)) (fail))
       (test-expr (jstatem-ifelse->test 2nd-to-last-statem))
       (then+asg-block (jstatem-ifelse->then 2nd-to-last-statem))
       (else+asg-block (jstatem-ifelse->else 2nd-to-last-statem))
       ((unless (and (consp then+asg-block)
                     (consp else+asg-block))) (fail))
       (then-block (butlast then+asg-block 1))
       (else-block (butlast else+asg-block 1))
       (then-asg (car (last then+asg-block)))
       (else-asg (car (last else+asg-block)))
       ((unless (and (jstatem-case then-asg :expr)
                     (jstatem-case else-asg :expr))) (fail))
       (then-asg (jstatem-expr->get then-asg))
       (else-asg (jstatem-expr->get else-asg))
       ((unless (and (jexpr-case then-asg :binary)
                     (jexpr-case else-asg :binary)
                     (jbinop-case (jexpr-binary->op then-asg) :asg)
                     (jbinop-case (jexpr-binary->op else-asg) :asg)
                     (equal (jexpr-binary->left then-asg)
                            (jexpr-name result-var))
                     (equal (jexpr-binary->left else-asg)
                            (jexpr-name result-var)))) (fail))
       (then-expr (jexpr-binary->right then-asg))
       (else-expr (jexpr-binary->right else-asg))
       ((unless (jstatem-case 3rd-to-last-statem :locvar)) (fail))
       (locvar (jstatem-locvar->get 3rd-to-last-statem))
       ((unless (and (equal (jlocvar->name locvar)
                            result-var)
                     (equal (jlocvar->init? locvar)
                            nil))) (fail)))
    (mv t pre-block test-expr then-block then-expr else-block else-expr))

  ///

  (defruledl lemma
    (implies (mv-nth 0 (atj-check-foldable-return block))
             (jstatem-case (nth (- (len block) 2) block) :ifelse)))

  (defret atj-check-foldable-return-then-decreases
    :hyp (mv-nth 0 (atj-check-foldable-return block))
    (< (jblock-count-ifs then-block)
       (jblock-count-ifs block))
    :rule-classes :linear
    :hints(("Goal" :use (lemma
                         (:instance jblock-count-ifs-positive-when-nth-ifelse
                          (i (- (len block) 2)))))))

  (defret atj-check-foldable-return-else-decreases
    :hyp (mv-nth 0 (atj-check-foldable-return block))
    (< (jblock-count-ifs else-block)
       (jblock-count-ifs block))
    :rule-classes :linear
    :hints(("Goal" :use (lemma
                         (:instance jblock-count-ifs-positive-when-nth-ifelse
                          (i (- (len block) 2))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-fold-returns ((block jblockp))
  :returns (new-block jblockp :hyp :guard)
  :verify-guards :after-returns
  :short "Fold @('return')s into @('if')s in a Java block."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the block ends with the pattern described "
    (xdoc::seetopic "atj-post-translation-fold-returns" "here")
    ", we replace it with the equivalent code also described "
    (xdoc::seetopic "atj-post-translation-fold-returns" "here")
    ", recursively."))
  (b* (((mv matchp
            pre-block
            test-expr
            then-block
            then-expr
            else-block
            else-expr) (atj-check-foldable-return block))
       ((unless matchp) block)
       (then-return (jstatem-return then-expr))
       (else-return (jstatem-return else-expr))
       (new-then-block (append then-block (list then-return)))
       (new-else-block (append else-block (list else-return)))
       (new-then-block (atj-fold-returns new-then-block))
       (new-else-block (atj-fold-returns new-else-block))
       (if-block (list
                  (jstatem-ifelse test-expr new-then-block new-else-block)))
       (new-block (append pre-block if-block)))
    new-block)
  :measure (jblock-count-ifs block))
