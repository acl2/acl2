; ACL2 Programming Language Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2PL")

; Matt K. mod: Avoid repeated ACL2(p) failures with waterfall-parallelism (no
; apparent reason, just incomplete)
(set-waterfall-parallelism nil)

(include-book "values")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ packages
  :parents (acl2-programming-language)
  :short "A formalization of ACL2 packages."
  :long
  (xdoc::topstring
   (xdoc::p
    "Packages are defined via @(tsee defpkg) in ACL2.
     Its arguments are
     the name of the package,
     a term that evaluates to the import list of the package,
     and an optional documentation string.")
   (xdoc::p
    "In our formalization, we ignore the documentation string,
     and we consider the evaluated import list
     (as opposed to the term that evaluates to it).
     Thus, we introduce a notion of package as consisting of
     a package name and a list of symbol values.")
   (xdoc::p
    "Here we allow any string as package name,
     despite the restrictions given in @(tsee defpkg).
     Those restrictions can be captured elsewhere."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod package
  :short "Fixtype of packages."
  ((name string)
   (imports symbol-value-listp))
  :layout :list
  :pred packagep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist package-list
  :short "Fixtype of lists of packages."
  :elt-type package
  :true-listp t
  :elementp-of-nil nil
  :pred package-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-package
  package
  :short "Fixtype of packages and @('nil')."
  :pred maybe-packagep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define package-lookup ((name stringp) (packages package-listp))
  :returns (package? maybe-packagep)
  :short "Look up a package in a list, by name."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return the first package in the list with the given name, if any.
     If there is none, we return @('nil').")
   (xdoc::p
    "When a list of packages represents
     all the package definitions in an ACL2 environment,
     the list will have unique package names;
     this will be formalized elsewhere.
     Under this condition,
     returning the first package found
     is as good as returning any package with that name in the list,
     since there can be at most one."))
  (b* (((when (endp packages)) nil)
       (package (car packages))
       ((when (equal name (package->name package)))
        (package-fix package)))
    (package-lookup name (cdr packages)))
  ///
  (fty::deffixequiv package-lookup
    :args ((packages package-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define import-lookup ((name stringp) (imports symbol-value-listp))
  :returns (symbol? maybe-symbol-valuep)
  :short "Find a symbol with a given name in a package import list."
  :long
  (xdoc::topstring
   (xdoc::p
    "When denoting a symbol
     via a package name @('P') and a (symbol) name @('N'),
     the denoted symbol does not always have that package name
     (in the sense of the one returned by @(tsee symbol-package-name)).
     The reason is that if @('P') imports, from another package @('Q'),
     a symbol with name @('N'), that is the denoted symbol,
     i.e. its @(tsee symbol-package-name) is @('Q') and not @('P').
     For instance @('acl2::cons') denotes @('common-lisp::cons'),
     whose @(tsee symbol-package-name) is @('\"COMMON-LISP\"').")
   (xdoc::p
    "This function looks up a symbol, by name,
     in a list of symbol that is meant to be a package import list.
     We return the first symbol found, if any.
     If none is found, we return @('nil').")
   (xdoc::p
    "An import list in a package definition of an ACL2 environment
     will have symbols with unique names;
     will have unique package names;
     this will be formalized elsewhere.
     Under this condition,
     returning the first symbol found
     is as good as returning any symbol with that name in the list,
     since there can be at most one."))
  (b* (((when (endp imports)) nil)
       (import (car imports))
       ((when (equal name (symbol-value->name import)))
        (symbol-value-fix import)))
    (import-lookup name (cdr imports)))
  ///
  (fty::deffixequiv import-lookup
    :args ((imports symbol-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-package ((name stringp))
  :returns (package packagep)
  :short "Lift a package from the current ACL2 environment to the meta level."
  :long
  (xdoc::topstring
   (xdoc::p
    "This must be used only on package names that are currently known.
     Otherwise, @(tsee pkg-imports) will cause an error.")
   (xdoc::p
    "We retrieve the imports of the package (a list of symbols),
     we lift them to the meta level,
     and we construct a package with the given name and lifted imports."))
  (b* ((imports (pkg-imports name)))
    (make-package :name name
                  :imports (lift-symbol-list imports))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection lift-package-list (x)
  :guard (string-listp x)
  :returns (packages package-listp)
  :short "Lift a list of packages (specified by name)
          from the current ACL2 environment to the meta level,
          in the same order."
  (lift-package x))
