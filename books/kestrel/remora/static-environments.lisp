; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-derived-fixtypes")
(include-book "abstract-syntax-constructors")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ static-environments
  :parents (static-semantics)
  :short "Static environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "A static environment consists of
     the contextual information needed to
     enforce the static semantics of some AST.
     Our static environments correspond to the combination of
     the sort environment @($\\Theta$),
     the kind environment @($\\Delta$), and
     the type environment @($\\Gamma$)
     in [arxiv], [thesis], and [esop].")
   (xdoc::p
    "This is currently not used in the type checker.
     It is intended for use in the upcoming declarative typing rules.
     We may also use it in the type checker."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod senv
  :short "Fixtype of static environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "A static environment consists of:")
   (xdoc::ul
    (xdoc::li
     "The set of ispace variables in scope.
      This corresponds to @($\\Theta$),
      but since our ispace variables include their own sort,
      a set suffices, as opposed to a map from variables to sorts.")
    (xdoc::li
     "A map from the type variables in scope to their kinds.
      This corresponds to @($\\Delta$).")
    (xdoc::li
     "A map from the term variables in scope to their types.
      This corresponds to @($\\Gamma$).")))
  ((ispace-vars ispace-var-set)
   (type-vars string-kind-map)
   (term-vars string-type-map))
  :pred senvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-op-types ()
  :returns (term-vars string-type-mapp)
  :short "Association of primitive operations to their types."
  :long
  (xdoc::topstring
   (xdoc::p
    "In Remora, the primitive operations (i.e. built-in functions)
     are syntactically variables of suitable function type;
     these variables are implicitly in scope,
     and thus part of the initial static environment."))
  (b* ((add/sub/mul/div-type (t-> ((tarray :int (shape))
                                   (tarray :int (shape)))
                                  (tarray :int (shape))))
       (append-type
        (tforall ("t" :atom)
                 (tpi ("$n" "$m" "@s")
                      (t-> ((tarray "t" (shape++ (shape "$m") "@s"))
                            (tarray "t" (shape++ (shape "$n") "@s")))
                           (tarray "t" (shape++ (shape (dim+ "$m" "$n"))
                                                "@s"))))))
       (reduce-type
        (tforall ("t" :atom)
                 (tpi ("@s" "$d")
                      (t-> ((tarray (t-> ((tarray "t" "@s")
                                          (tarray "t" "@s"))
                                         (tarray "t" "@s"))
                                    (shape))
                            (tarray "t" (shape++ (shape (dim+ 1 "$d")) "@s")))
                           (tarray "t" "@s")))))
       (iota-type
        (tpi ("$d")
             (t-> ((tarray :int (shape "$d")))
                  (tarray (tsigma ("@s") (tarray :int "@s")) (shape))))))
    (omap::from-alist
     (list (cons "add" add/sub/mul/div-type)
           (cons "sub" add/sub/mul/div-type)
           (cons "mul" add/sub/mul/div-type)
           (cons "div" add/sub/mul/div-type)
           (cons "append" append-type)
           (cons "reduce" reduce-type)
           (cons "iota" iota-type)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-senv ()
  :short "Initial static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the initial, i.e. top-level, static environment.
     It only contains the primitive operations in scope."))
  (make-senv :ispace-vars nil
             :type-vars nil
             :term-vars (prim-op-types)))
