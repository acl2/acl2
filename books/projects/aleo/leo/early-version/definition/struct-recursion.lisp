; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "files")
(include-book "types")

(include-book "centaur/depgraph/top" :dir :system)

(local (include-book "std/alists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ struct-recursion
  :parents (static-semantics)
  :short "Struct type recursion checks in Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "Struct types may contain components with other struct types,
     but there cannot be any circularity:
     a struct type cannot include, directly or indirectly,
     components of the same struct type.
     If such a circularity existed,
     it would be impossible to construct values of the struct type,
     because values in Leo are finite objects.")
   (xdoc::p
    "Thus, the Leo static semantics includes the requirement that
     there is no recursion in struct types (in the sense above).
     Here we formalize this requirement,
     by constructing a dependency graph among type identifiers
     and ensuring that there are no circularities in the graph."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compdecl-type-identifiers ((decl compdeclp))
  :returns (ids identifier-setp)
  :short "Type identifiers in a struct component declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the same as the ones in the type of the component."))
  (type-identifiers (compdecl->type decl))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compdecl-list-type-identifiers ((decls compdecl-listp))
  :returns (ids identifier-setp)
  :short "Type identifiers in a list of struct component declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "We take the union of the ones in all the components."))
  (cond ((endp decls) nil)
        (t (set::union (compdecl-type-identifiers (car decls))
                       (compdecl-list-type-identifiers (cdr decls)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define structdecl-struct-graph ((decl structdeclp))
  :returns (graph alistp)
  :short "Struct graph induced by a struct definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return a dependency graph expressing that
     the circui type defined by the struct type declaration
     depends on the type identifiers in the components' types.
     This dependency relation is
     the direct containment relation of struct types.
     The format is that of an alist for the "
    (xdoc::seetopic "depgraph::depgraph" "dependency graph library")
    "."))
  (b* ((subs (compdecl-list-type-identifiers (structdecl->components decl))))
    (list (cons (structdecl->name decl) subs)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define topdecl-struct-graph ((decl topdeclp))
  :returns (graph alistp)
  :short "Struct graph induced by a top-level definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "A function declaration induces nothing for this graph.
     A struct declaration contributes a graph."))
  (topdecl-case decl
                :function nil
                :struct (structdecl-struct-graph decl.get)
                ;; TODO, or this might already be ok:
                :mapping nil
                )
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define topdecl-list-struct-graph ((decls topdecl-listp))
  :returns (graph alistp)
  :short "Struct graph induced by a list of top-level declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "We take the union of all the graphs for the declarations.
     Note that, for lists of top-level declarations
     in files that pass type-checking,
     the names of the structs introduced by the declarations are unique,
     and thus there is no shadowing in the graph alist."))
  (cond ((endp decls) nil)
        (t (append (topdecl-struct-graph (car decls))
                   (topdecl-list-struct-graph (cdr decls)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define file-struct-recursion-okp ((file filep))
  :returns (yes/no booleanp)
  :short "Check if a Leo file has no struct type recursion."
  :long
  (xdoc::topstring
   (xdoc::p
    "We build the dependency graph of the struct types in the file,
     by going through the declarations that form the file.
     Then we attempt to topologically sort the graph.
     If that succeeds, the graph has no circularities
     and therefore there is no struct type recursion.
     If that fails, there is a circularity."))
  (b* ((graph (topdecl-list-struct-graph (programdecl->items (file->program file))))
       ;; TODO: consider imports
       ((mv okp &) (depgraph::toposort graph)))
    okp)
  :hooks (:fix))
