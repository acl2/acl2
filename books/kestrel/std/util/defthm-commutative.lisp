; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/std/util/defmacro-plus" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ defthm-commutative (name op &key hints)
  (declare (xargs :guard (and (symbolp name)
                              (symbolp op))))
  :parents (std::std/util-extensions std/util)
  :short "Introduce a commutativity theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "General form:")
   (xdoc::codeblock
    "(defthm-commutative name op :hints ...)")
   (xdoc::ul
    (xdoc::li
     "@('name') must be a symbol that names the new theorem.")
    (xdoc::li
     "@('op') must be a symbol that names an existing binary operation,
      whose (unconditional) commutativity the new theorem asserts.")
    (xdoc::li
     "@(':hints'), if present, must consist of hints
      of the kind use in @(tsee defthm).
      These hints are used to prove the commutative theorem."))
   (xdoc::p
    "More customization options may be added in the future.")
   (xdoc::p
    "The new theorem's variables are `@('x')' and `@('y')',
     in the same package as @('op'),
     unless @('op') is the @('\"COMMON-LISP\"') package,
     in which case the variables are in the @('\"ACL2\"') package."))
  (let* ((var-pkg (fix-pkg (symbol-package-name op)))
         (x (intern$ "X" var-pkg))
         (y (intern$ "Y" var-pkg)))
    `(defthm ,name
       (equal (,op ,x ,y) (,op ,y ,x))
       :hints ,hints)))
