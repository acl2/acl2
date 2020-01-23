; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-mv-let-call ((vars symbol-listp)
                          (mv-term pseudo-termp)
                          (body-term pseudo-termp))
  :returns (term pseudo-termp :hyp :guard)
  :parents (std/system/term-transformations)
  :short "Build a translated call of @(tsee mv-let)."
  :long
  (xdoc::topstring
   (xdoc::p
    "In translated form, @('(mv-let (var1 ... varn) mv-term body-term)') is")
   (xdoc::codeblock
    "((lambda (mv)"
    "         ((lambda (var1 ... varn) body-term-trans)"
    "          (mv-nth '0 mv)"
    "          ..."
    "          (mv-nth 'n-1 mv)))"
    " mv-term-trans)")
   (xdoc::p
    "where @('mv-term-trans') and @('body-term-trans') are
     the translations of @('mv-term') and @('body-term').")
   (xdoc::p
    "This utility creates a translated term of the form above
     from its constituents.")
   (xdoc::p
    "This utility is essentially the inverse of @(tsee check-mv-let-call)."))
  `((lambda (mv)
      ((lambda ,vars ,body-term)
       ,@(make-mv-let-call-aux 0 (len vars))))
    ,mv-term)

  :prepwork

  ((define make-mv-let-call-aux ((index natp) (n natp))
     :returns (terms pseudo-term-listp)
     (if (or (not (mbt (natp index)))
             (not (mbt (natp n)))
             (>= index n))
         nil
       (cons `(mv-nth ',index mv)
             (make-mv-let-call-aux (1+ index) n)))
     :measure (nfix (- n index))
     ///

     (defret len-of-make-mv-let-call-aux
       (implies (and (natp index)
                     (natp n))
                (equal (len terms)
                       (nfix (- n index))))))))
