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

(define make-mv-let-call ((mv-var symbolp)
                          (vars symbol-listp)
                          (indices (or (nat-listp indices)
                                       (eq indices :all)))
                          (mv-term pseudo-termp)
                          (body-term pseudo-termp))
  :guard (or (equal indices :all)
             (equal (len indices) (len vars)))
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
    "For greater flexibility,
     we allow the @('mv') variable to be
     a symbol different from the symbol `@('mv')':
     as explained in @(tsee check-mv-let-call),
     a translated @(tsee mv-let) may have a different symbol from `@('mv')',
     and so this flexibility is useful, for example,
     to reconstruct an @(tsee mv-let) call,
     possibly with some modification,
     from another one whose @('mv') variable is another symbol.
     The parameter @('mv-var') of this utility is the symbol to use.")
   (xdoc::p
    "Also for greater flexibilty,
     we allow some @(tsee mv-nth) calls to be missing.
     As explained in @(tsee check-mv-let-call),
     while translated terms obtained directly from @(tsee mv-let) calls
     always have all the @(tsee mv-nth) calls,
     a term subjected to some transformations may not.
     To use this utility to reconstruct this kind of transformed term,
     the @('indices') parameter lets the caller specify
     which indices should be present.
     As a convenience, @(':all') stands for
     all contiguous indices from 0 to the number of bound variables minus 1.
     If a list of indices is supplied,
     it must consist of strictly increasing natural numbers,
     and its length must match the number of bound variables.
     The second condition is expressed by the guard,
     but the first condition is checked at run time,
     causing an error if not satisfied.")
   (xdoc::p
    "This utility is essentially the inverse of @(tsee check-mv-let-call)."))
  `((lambda (,mv-var)
      ((lambda ,vars ,body-term)
       ,@(if (eq indices :all)
             (make-mv-let-call-aux1 0 (len vars) mv-var)
           (make-mv-let-call-aux2 indices mv-var))))
    ,mv-term)

  :prepwork

  ((define make-mv-let-call-aux1 ((index natp) (n natp) (mv-var symbolp))
     :returns (terms pseudo-term-listp :hyp (symbolp mv-var))
     (if (or (not (mbt (natp index)))
             (not (mbt (natp n)))
             (>= index n))
         nil
       (cons `(mv-nth ',index ,mv-var)
             (make-mv-let-call-aux1 (1+ index) n mv-var)))
     :measure (nfix (- n index))
     ///
     (defret len-of-make-mv-let-call-aux1
       (implies (and (natp index)
                     (natp n))
                (equal (len terms)
                       (nfix (- n index))))))

   (local
    (defthm pseudo-term-listp-of-make-list-ac
      (implies (and (pseudo-termp val)
                    (pseudo-term-listp ac))
               (pseudo-term-listp (make-list-ac n val ac)))))

   (local
    (defthm len-of-make-list-ac
      (equal (len (make-list-ac n val ac))
             (+ (nfix n) (len ac)))))

   (define make-mv-let-call-aux2 ((indices nat-listp) (mv-var symbolp))
     :returns (terms pseudo-term-listp :hyp (symbolp mv-var))
     (cond ((endp indices) nil)
           ((endp (cdr indices)) (list `(mv-nth ',(car indices) ,mv-var)))
           (t (if (< (car indices)
                     (cadr indices))
                  (cons `(mv-nth ',(car indices) ,mv-var)
                        (make-mv-let-call-aux2 (cdr indices) mv-var))
                (prog2$ (raise "The list of indices ~x0 ~
                                is not strictly increasing."
                               indices)
                        (make-list (len indices) :initial-element nil)))))
     ///
     (defret len-of-mv-let-call-aux2
       (equal (len terms)
              (len indices))))))
