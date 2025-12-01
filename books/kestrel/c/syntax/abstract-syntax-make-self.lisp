; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "kestrel/fty/defmake-self" :dir :system)

(include-book "code-ensembles")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defmake-self code-ensemble
  :parents (abstract-syntax)
  :short (xdoc::topstring
          (xdoc::seetopic "fty::defmake-self" "Make-self functions")
          " for "
          (xdoc::seetopic "code-ensemble" "code ensembles")
          " and all the AST types."))
