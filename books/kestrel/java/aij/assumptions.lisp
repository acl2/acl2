; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "kestrel/std/basic/symbol-package-name-lst" :dir :system)
(include-book "kestrel/std/system/known-packages-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc aij-assumptions
  :parents (aij)
  :short "Assumptions about ACL2 on which AIJ is based."
  :long
  (xdoc::topstring
   (xdoc::p
    "The implementation of AIJ is based on a number of assumptions about ACL2.
     Here we state assertions for some of these assumptions,
     thus checking these assumptions when this file is processed:
     a failure when processing this file may point to a need to revise AIJ.
     These assumptions may be unlikely to change,
     but there is no harm in checking them.")
   (xdoc::p
    "In the future, (some of) these assertions
     might be extracted automatically from the AIJ Java code.")
   (xdoc::p
    "We check the following assumptions for now:")
   (xdoc::ul
    (xdoc::li
     "The ACL2 symbols for which AIJ has final static fields
      have the pacakge names used to construct them in the Java code.
      AIJ constructs these symbols
      via the private constructor, not via the public builder,
      because the construction happens before defining packages:
      thus, the package name must be the one where the symbol is,
      not one that imports the symbol.")
    (xdoc::li
     "The first three packages returned by @(tsee known-packages)
      are @('\"KEYWORD\"'), @('\"COMMON-LISP\"'), and @('\"ACL2\"'),
      in this order.")
    (xdoc::li
     "The @('\"KEYWORD\"') and @('\"COMMON-LISP\"') packages
      import no symbols.
      The @('\"ACL2\"') package imports only symbols
      in the @('\"COMMON-LISP\"') package.")
    (xdoc::li
     "The ACL2 constant @('*pkg-witness-name*')
      has the value @('\"ACL2-PKG-WITNESS\"')."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (equal (symbol-package-name t) "COMMON-LISP"))
(assert-event (equal (symbol-package-name nil) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'list) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'if) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'characterp) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'stringp) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'symbolp) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'integerp) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'rationalp) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'consp) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'char-code) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'code-char) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'coerce) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'symbol-name) "COMMON-LISP"))
(assert-event (equal (symbol-package-name '<) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'realpart) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'imagpart) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'numerator) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'denominator) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'complex) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'cons) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'car) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'cdr) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'equal) "COMMON-LISP"))
(assert-event (equal (symbol-package-name 'or) "COMMON-LISP"))

(assert-event (equal (symbol-package-name 'complex-rationalp) "ACL2"))
(assert-event (equal (symbol-package-name 'acl2-numberp) "ACL2"))
(assert-event (equal (symbol-package-name 'intern-in-package-of-symbol) "ACL2"))
(assert-event (equal (symbol-package-name 'symbol-package-name) "ACL2"))
(assert-event (equal (symbol-package-name 'pkg-imports) "ACL2"))
(assert-event (equal (symbol-package-name 'pkg-witness) "ACL2"))
(assert-event (equal (symbol-package-name 'unary--) "ACL2"))
(assert-event (equal (symbol-package-name 'unary-/) "ACL2"))
(assert-event (equal (symbol-package-name 'binary-+) "ACL2"))
(assert-event (equal (symbol-package-name 'binary-*) "ACL2"))
(assert-event (equal (symbol-package-name 'bad-atom<=) "ACL2"))
(assert-event (equal (symbol-package-name 'nonnegative-integer-quotient) "ACL2"))
(assert-event (equal (symbol-package-name 'string-append) "ACL2"))
(assert-event (equal (symbol-package-name 'len) "ACL2"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (equal (take 3 (known-packages+ state))
                     '("KEYWORD" "COMMON-LISP" "ACL2")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (equal (pkg-imports "KEYWORD") nil))

(assert-event (equal (pkg-imports "COMMON-LISP") nil))

(assert-event (let ((imports (pkg-imports "ACL2")))
                (equal (symbol-package-name-lst imports)
                       (make-list (len imports)
                                  :initial-element "COMMON-LISP"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (equal *pkg-witness-name* "ACL2-PKG-WITNESS"))
