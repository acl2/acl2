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

(include-book "kestrel/std/basic/symbol-package-name-lst" :dir :system)

(local (include-book "std/lists/union" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines all-pkg-names
  :parents (std/system/term-queries)
  :short "Collect all the package names of all the symbols in a term."
  :long
  (xdoc::topstring
   (xdoc::@def "all-pkg-names")
   (xdoc::@def "all-pkg-names-lst"))

  (define all-pkg-names ((term pseudo-termp))
    :returns (pkg-names string-listp)
    (cond ((variablep term) (list (symbol-package-name term)))
          ((fquotep term) (if (symbolp (cadr term))
                              (list (symbol-package-name (cadr term)))
                            nil))
          ((symbolp (ffn-symb term))
           (add-to-set-equal (symbol-package-name (ffn-symb term))
                             (all-pkg-names-lst (fargs term))))
          (t (union-equal (remove-duplicates-equal
                           (symbol-package-name-lst
                            (lambda-formals (ffn-symb term))))
                          (union-equal
                           (all-pkg-names (lambda-body (ffn-symb term)))
                           (all-pkg-names-lst (fargs term)))))))

  (define all-pkg-names-lst ((terms pseudo-term-listp))
    :returns (pkg-names string-listp)
    (cond ((endp terms) nil)
          (t (union-equal (all-pkg-names (car terms))
                          (all-pkg-names-lst (cdr terms))))))

  :verify-guards nil ; done below
  ///
  (verify-guards all-pkg-names))
