; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-list-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (elements pseudo-term-listp :hyp :guard))
  :parents (std/system/term-queries)
  :short "Check if a term is a (translated) call of @(tsee list)."
  :long
  (xdoc::topstring
   (xdoc::p
    "In translated form, the term must have the form
     @('(cons ... (cons ... (cons ... (... \'nil)...)))'),
     i.e. be a nest of @(tsee cons)es that ends in a quoted @('nil').
     The nest may be empty, i.e. the term may be just a quoted @('nil').
     If the term has this form, we return the list of its element terms,
     i.e. all the @(tsee car)s of the nest, in the same order."))
  (b* (((when (variablep term)) (mv nil nil))
       ((when (fquotep term)) (if (equal term *nil*)
                                  (mv t nil)
                                (mv nil nil)))
       (fn (ffn-symb term))
       ((unless (eq fn 'cons)) (mv nil nil))
       (args (fargs term))
       ((unless (= (len args) 2))
        (raise "Internal error: found CONS with ~x0 arguments." (len args))
        (mv nil nil))
       (car (first args))
       (cdr (second args))
       ((mv yes/no-rest elements-rest) (check-list-call cdr))
       ((unless yes/no-rest) (mv nil nil)))
    (mv t (cons car elements-rest))))
