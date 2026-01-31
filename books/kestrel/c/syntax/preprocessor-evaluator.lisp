; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "preprocessor-lexemes")

(local (include-book "std/lists/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ preprocessor-evaluator
  :parents (preprocessor)
  :short "Evaluator component of the preprocessor."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('#if') and @('#elif') directives contain constant expressions
     that must be evaluated [C17:6.10.1].
     In our preprocessor, this is done by the evaluator component,
     which is given the list of lexemes that follow a @('#if') and @('#elif'),
     after all macro replacement has taken place.
     Our evaluator parses those lexemes as an expression,
     at the same time evaluating it.
     Any comment and white space, including the final new line,
     are ignored (i.e. skipped over) in this evaluation process:
     only tokens are relevant.")
   (xdoc::p
    "By the time we reach the evaluator.
     the occurrences of the @('defined') operator
     have already been evaluated, as part of macro replacement.
     They have been replaced by @('0') or @('1').")
   (xdoc::p
    "Our evaluator does not yet support
     all the integer constant expressions described in [C17:6.6/6].
     We start with support for common expressions,
     which we plan to extend as needed."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define find-first-token ((lexemes plexeme-listp))
  :returns (mv (token? plexeme-optionp)
               (lexemes-rest plexeme-listp))
  :short "Find the first token in a list of lexemes, if any."
  :long
  (xdoc::topstring
   (xdoc::p
    "We skip over comments and white space until we find a token.
     If we find no token, we return @('nil')."))
  (b* (((when (endp lexemes)) (mv nil nil))
       (lexeme (car lexemes))
       ((when (plexeme-tokenp lexeme))
        (mv (plexeme-fix lexeme) (plexeme-list-fix (cdr lexemes)))))
    (find-first-token (cdr lexemes)))

  ///

  (defret plexeme-tokenp-of-find-first-token
    (implies token?
             (plexeme-tokenp token?))
    :hints (("Goal" :induct t)))

  (defret len-of-find-first-token-uncond
    (<= (len lexemes-rest)
        (len lexemes))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret len-of-fid-first-token-cond
    (implies token?
             (<= (len lexemes-rest)
                 (1- (len lexemes))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: continue
