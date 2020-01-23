; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-list-call")
(include-book "number-of-results-plus")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define term-possible-numbers-of-results ((term pseudo-termp) (wrld plist-worldp))
  :returns (possible-numbers-of-results pos-listp)
  :parents (std/system/term-queries)
  :short "Calculate the possible numbers of results of a translated term."
  :long
  (xdoc::topstring
   (xdoc::p
    "The number of results of an untranslated term,
     which is either 1 or more if @(tsee mv) is involved directly or indirectly,
     can be always determined by translating the term
     (see @(tsee check-user-term)).
     However, that information is largely lost in translated terms.
     In some cases, the number of results can be determined,
     but in other cases there may be two possilities,
     namely 1 or a number greater than 1.
     The reason is that calls of the macro @(tsee mv)
     become calls of @(tsee list) when terms are translated,
     and therefore we cannot distinguish a single list result
     from multiple results.")
   (xdoc::p
    "This utility returns the possible number of results of a translated term,
     as follows.")
   (xdoc::ul
    (xdoc::li
     "If the term is a variable or a quoted constants,
      it always returns one result.
      This would not be true for the @(tsee mv) variables
      that result from translating @(tsee mv-let)s
      (see @(tsee check-mv-let-call)),
      but this utility never reaches such variables (see below);
      it only reaches other variables,
      which are always bound to single results.")
    (xdoc::li
     "If the term is a (translated) call of @(tsee list),
      we have two possibilities in general, as mentioned above.
      Unless the call builds an empty or singleton list,
      in which case it cannot result from an @(tsee mv),
      which always takes at least two arguments,
      and thus the call must return a single list result.")
    (xdoc::li
     "If the term is a call of @(tsee return-last),
      we recursively process its last argument.
      Note that @(tsee return-last) is in @('*stobjs-out-invalid*'),
      because it returns the same number of results as its last argument.")
    (xdoc::li
     "If the term is a call of @(tsee if),
      we recursively process its second and third arguments,
      and intersect the possible numbers for the two branches.
      Note that @(tsee if) is in @('*stojbjs-out-invalid*'),
      because it returns the same number of results as its branches.
      Thus, for example,
      if one branch is a @(tsee list) call
      that may return either 1 or 3 results,
      while the other branch is a call of a named function
      that returns 3 results,
      the @(tsee if) call must return 3 results;
      one branch resolves the ambiguity of the other branch.
      However, a translated call @('(if ... (mv ...) (mv ...))')
      remains ambiguous, with two possible numbers of results.
      The case in which the two branches have no numbers of results in common
      should never happen in translated terms
      obtained by translating valid untranslated terms;
      however, this utility cannot make that assumption,
      and may well return @('nil').")
    (xdoc::li
     "A call of any other named function is unambiguous,
      based on the number of results of that function.")
    (xdoc::li
     "Finally, if the term is a call of a lambda expression,
      we recursively process its body.
      Its arguments and bound variables do not matter
      for determining the number of results of the lambda call.
      In particular, if the term is a translated @(tsee mv-let),
      the @('mv') variables is skipped over (see @(tsee check-mv-let-call)),
      as mentioned above."))
   (xdoc::p
    "Since this utility always returns 1 or 2 numbers explicitly,
     or intersects the numbers for subterms,
     the result always consists of 0, 1, or 2 numbers."))
  (b* (((when (variablep term)) (list 1))
       ((when (fquotep term)) (list 1))
       ((mv list-call-p elements) (check-list-call term))
       ((when list-call-p) (if (>= (len elements) 2)
                               (list 1 (len elements))
                             (list 1)))
       (fn (ffn-symb term))
       ((when (eq fn 'return-last))
        (term-possible-numbers-of-results (fargn term 3) wrld))
       ((when (eq fn 'if))
        (intersection$ (term-possible-numbers-of-results (fargn term 2) wrld)
                       (term-possible-numbers-of-results (fargn term 3) wrld)))
       ((when (symbolp fn)) (list (number-of-results+ fn wrld))))
    (term-possible-numbers-of-results (lambda-body fn) wrld))
  :verify-guards :after-returns

  :prepwork

  ((local
    (defthm pos-listp-of-intersection-equal
      (implies (pos-listp x)
               (pos-listp (intersection-equal x y)))))

   (local
    (defthm eqlable-listp-when-pos-listp
      (implies (pos-listp x)
               (eqlable-listp x)))))

  ///

  (local
   (defthm len-of-intersection-equal-upper-bound
     (<= (len (intersection-equal x y))
         (len x))
     :rule-classes :linear))

  (defret len-of-term-possible-numbers-of-results-upper-bound
    (<= (len possible-numbers-of-results) 2)
    :rule-classes :linear))
