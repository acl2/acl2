; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-user-term")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-user-lambda (x (wrld plist-worldp))
  :returns (mv (lambd/message  "A @(tsee pseudo-termp) or @(tsee msgp).")
               (stobjs-out "A @(tsee symbol-listp)."))
  :mode :program
  :parents (std/system/term-queries)
  :short (xdoc::topstring
          "Recognize "
          (xdoc::seetopic "term" "untranslated")
          " lambda expressions that are valid for evaluation.")
  :long
  (xdoc::topstring
   (xdoc::p
    "An untranslated @(see lambda) expression is
     a lambda expression as entered by the user.
     This function checks whether @('x')is
     a true list of exactly three elements,
     whose first element is the symbol @('lambda'),
     whose second element is
     a list of legal variable symbols without duplicates,
     and whose third element is
    an untranslated term that is valid for evaluation.")
   (xdoc::p
    "If the check succeeds, the translated lambda expression is returned,
     along with the @(tsee stobjs-out) list of the body of the lambda expression
     (see @(tsee check-user-term) for an explanation
     of the @(tsee stobjs-out) list of a term).
     Otherwise, a possibly structured error message is returned
     (printable with @('~@')),
     along with @('nil') as @(tsee stobjs-out) list.")
   (xdoc::p
    "The @(tsee check-user-lambda) function does not terminate
     if @(tsee check-user-term) does not terminate."))
  (b* (((unless (true-listp x))
        (mv (msg "~x0 is not a true list." x) nil))
       ((unless (= (len x) 3))
        (mv (msg "~x0 does not consist of exactly three elements." x) nil))
       ((unless (eq (first x) 'lambda))
        (mv (msg "~x0 does not start with LAMBDA." x) nil))
       ((unless (arglistp (second x)))
        (mv (msg "~x0 does not have valid formal parameters." x) nil))
       ((mv term/message stobjs-out) (check-user-term (third x) wrld))
       ((when (msgp term/message))
        (mv (msg "~x0 does not have a valid body.  ~@1" x term/message) nil)))
    (mv `(lambda ,(second x) ,term/message) stobjs-out)))
