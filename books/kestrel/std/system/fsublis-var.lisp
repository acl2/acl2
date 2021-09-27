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
   (xdoc::@def "fsublis-var-lst")
   (xdoc::p
    "The file @('fsublis-var-more-theorems.lisp') contains theorems
     about these functions and @(tsee symbol-pseudoterm-alistp).
     They are similar to the return type theorems,
     but involve that stronger alist recognizer;
     they are disabled by default."))

  (define fsublis-var ((alist (and (symbol-alistp alist)
                                   (pseudo-term-listp (strip-cdrs alist))))
                       (term pseudo-termp))
    :returns (new-term pseudo-termp :hyp :guard)
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
    :returns (new-terms (and (pseudo-term-listp new-terms)
                             (equal (len new-terms)
                                    (len terms)))
                        :hyp :guard)
    (cond ((endp terms) nil)
          (t (cons (fsublis-var alist (car terms))
                   (fsublis-var-lst alist (cdr terms))))))

  :returns-hints ('(:expand (:free (x y) (pseudo-termp (cons x y)))))

  :prepwork
  ((local
    (defthm returns-lemma
      (implies (and (symbol-alistp alist)
                    (pseudo-term-listp (strip-cdrs alist)))
               (pseudo-termp (cdr (assoc-equal key alist))))))))
