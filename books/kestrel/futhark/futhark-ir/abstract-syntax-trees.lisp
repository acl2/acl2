; Futhark IR abstract syntax trees
;
; Copyright (C) 2026 Kestrel Institute (https://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FUTHARK")

(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "kestrel/fty/defset" :dir :system)
(include-book "kestrel/fty/defresult" :dir :system)

(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-trees
  :parents (abstract-syntax)
  :short "Abstract syntax trees for a Futhark IR subset."
  :long
  (xdoc::topstring
   (xdoc::p
    "The Futhark IR grammar in this directory is deliberately small and geared
     toward the subset used by the Remora-to-Futhark path.  These datatypes use
     fixtypes so that parsed and constructed IR fragments have generated
     recognizers, fixing functions, equivalence relations, and structural
     induction schemes.")
   (xdoc::p
    "The datatypes are syntax-oriented rather than semantic: for example,
     primitive types, array sizes, and literal text are retained as strings
     when the current front end does not need to interpret them further.")
   (xdoc::p
    "Identifier names and string-literal contents that originate from
     non-ASCII source code use the same convention as the Remora ASTs:
     ACL2 strings contain the UTF-8 byte encoding of the corresponding
     Unicode code-point sequence."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption string-option
  string
  :pred string-optionp
  :parents (abstract-syntax-trees)
  :short "Optional source name for a Futhark IR program.")

(fty::deftypes types

  (fty::deftagsum fut-type
    (:prim ((name string)))
    (:array ((size string-option)
             (elem fut-type)))
    :pred fut-typep
    :parents (abstract-syntax-trees)
    :short "Futhark IR type names and array types.")

  (fty::deflist fut-type-list
    :elt-type fut-type
    :true-listp t
    :elementp-of-nil nil
    :pred fut-type-listp))

(fty::defprod param
  ((name string)
   (type fut-type))
  :pred paramp
  :parents (abstract-syntax-trees)
  :short "A named, typed Futhark IR parameter.")

(fty::deflist param-list
  :elt-type param
  :true-listp t
  :elementp-of-nil nil
  :pred param-listp
  :parents (abstract-syntax-trees)
  :short "A list of Futhark IR parameters.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes forms

  (fty::deftagsum expr
    (:var ((name string)))
    (:literal ((text string)))
    (:array ((elems expr-list)
             (type fut-type)))
    (:brace ((elems expr-list)))
    (:call ((fun string)
            (args expr-list)))
    (:apply ((fun string)
             (args expr-list)
             (result-types fut-type-list)))
    (:map ((args expr-list)))
    (:lambda ((params param-list)
              (result-types fut-type-list)
              (body body)))
    (:paren ((expr expr)))
    (:raw ((text string)))
    :pred exprp
    :measure (two-nats-measure (acl2-count x) 0)
    :parents (abstract-syntax-trees)
    :short "Futhark IR expressions.")

  (fty::deflist expr-list
    :elt-type expr
    :true-listp t
    :elementp-of-nil nil
    :pred expr-listp
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::deftagsum stmt
    (:let ((pattern param-list)
           (expr expr)))
    :pred stmtp
    :base-case-override :let
    :measure (two-nats-measure (acl2-count x) 1)
    :parents (abstract-syntax-trees)
    :short "Futhark IR statements.")

  (fty::deflist stmt-list
    :elt-type stmt
    :true-listp t
    :elementp-of-nil nil
    :pred stmt-listp
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::deftagsum body
    (:block ((stmts stmt-list)
             (results expr-list)))
    :pred bodyp
    :base-case-override :block
    :measure (two-nats-measure (acl2-count x) 2)
    :parents (abstract-syntax-trees)
    :short "Futhark IR bodies.")

  (fty::deftagsum decl
    (:fun ((name string)
           (params param-list)
           (result-types fut-type-list)
           (body body)))
    (:entry ((external-name string)
             (entry-result-types fut-type-list)
             (name string)
             (params param-list)
             (result-types fut-type-list)
             (body body)
             (doc string-option)))
    :pred declp
    :base-case-override :fun
    :measure (two-nats-measure (acl2-count x) 3)
    :parents (abstract-syntax-trees)
    :short "Top-level Futhark IR declarations, including optional entry-point
            documentation in the current textual format.")

  (fty::deflist decl-list
    :elt-type decl
    :true-listp t
    :elementp-of-nil nil
    :pred decl-listp
    :measure (two-nats-measure (acl2-count x) 0)))

(fty::defprod fut-program
  ((name-source string-option)
   (decls decl-list))
  :pred fut-programp
  :parents (abstract-syntax-trees)
  :short "A parsed Futhark IR program.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult fut-type-result
  :ok fut-type
  :pred fut-type-resultp
  :parents (abstract-syntax-trees)
  :short "Errors and Futhark IR types.")

(fty::defresult fut-type-list-result
  :ok fut-type-list
  :pred fut-type-list-resultp
  :parents (abstract-syntax-trees)
  :short "Errors and lists of Futhark IR types.")

(fty::defresult param-result
  :ok param
  :pred param-resultp
  :parents (abstract-syntax-trees)
  :short "Errors and Futhark IR parameters.")

(fty::defresult param-list-result
  :ok param-list
  :pred param-list-resultp
  :parents (abstract-syntax-trees)
  :short "Errors and lists of Futhark IR parameters.")

(fty::defresult expr-result
  :ok expr
  :pred expr-resultp
  :parents (abstract-syntax-trees)
  :short "Errors and Futhark IR expressions.")

(fty::defresult expr-list-result
  :ok expr-list
  :pred expr-list-resultp
  :parents (abstract-syntax-trees)
  :short "Errors and lists of Futhark IR expressions.")

(fty::defresult stmt-result
  :ok stmt
  :pred stmt-resultp
  :parents (abstract-syntax-trees)
  :short "Errors and Futhark IR statements.")

(fty::defresult stmt-list-result
  :ok stmt-list
  :pred stmt-list-resultp
  :parents (abstract-syntax-trees)
  :short "Errors and lists of Futhark IR statements.")

(fty::defresult body-result
  :ok body
  :pred body-resultp
  :parents (abstract-syntax-trees)
  :short "Errors and Futhark IR bodies.")

(fty::defresult decl-result
  :ok decl
  :pred decl-resultp
  :parents (abstract-syntax-trees)
  :short "Errors and Futhark IR declarations.")

(fty::defresult decl-list-result
  :ok decl-list
  :pred decl-list-resultp
  :parents (abstract-syntax-trees)
  :short "Errors and lists of Futhark IR declarations.")

(fty::defresult fut-program-result
  :ok fut-program
  :pred fut-program-resultp
  :parents (abstract-syntax-trees)
  :short "Errors and Futhark IR programs.")
