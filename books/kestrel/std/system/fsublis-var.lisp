; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defines" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines fsublis-var
  :parents (std/system/term-transformations)
  :short "Variant of @(tsee sublis-var) that performs no simplification."
  :long
  (xdoc::topstring
   (xdoc::p
    "The meaning of the starting @('f') in the name of this utility
     is analogous to @(tsee fcons-term) compared to @(tsee cons-term).")
   (xdoc::@def "fsublis-var")
   (xdoc::@def "fsublis-var-lst"))

  (define fsublis-var ((alist (and (symbol-alistp alist)
                                   (pseudo-term-listp (strip-cdrs alist))))
                       (term pseudo-termp))
    :returns (new-term "A @(tsee pseudo-termp).")
    (cond ((variablep term) (b* ((pair (assoc-eq term alist)))
                              (cond (pair (cdr pair))
                                    (t term))))
          ((fquotep term) term)
          (t (b* ((fn (ffn-symb term))
                  (args (fsublis-var-lst alist (fargs term))))
               (fcons-term fn args)))))

  (define fsublis-var-lst ((alist (and (symbol-alistp alist)
                                       (pseudo-term-listp (strip-cdrs alist))))
                           (terms pseudo-term-listp))
    :returns (new-terms "A @(tsee pseudo-term-listp).")
    (cond ((endp terms) nil)
          (t (cons (fsublis-var alist (car terms))
                   (fsublis-var-lst alist (cdr terms)))))))
