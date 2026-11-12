; C Library
;
; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/strings/strprefixp" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/abstract-domains/many-valued-logics/3vl" :dir :system)

(include-book "kestrel/data/graph/add-edge-defs" :dir :system)
(include-book "kestrel/data/graph/add-node-defs" :dir :system)
(include-book "kestrel/data/graph/fty" :dir :system)
(include-book "kestrel/data/graph/graph-defs" :dir :system)
(include-book "kestrel/data/graph/nodes-defs" :dir :system)
(include-book "kestrel/data/graph/successors-defs" :dir :system)
(include-book "kestrel/data/graph/walk/reachable-defs" :dir :system)
(include-book "kestrel/data/treeset/cardinality-defs" :dir :system)
(include-book "kestrel/data/treeset/delete-defs" :dir :system)
(include-book "kestrel/data/treeset/diff-defs" :dir :system)
(include-book "kestrel/data/treeset/fty" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/treeset/min-max-defs" :dir :system)
(include-book "kestrel/data/treeset/set-defs" :dir :system)
(include-book "kestrel/data/treeset/union-defs" :dir :system)

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(include-book "../../syntax/abstract-syntax-operations")
(include-book "../../syntax/validation-annotations")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(acl2::controlled-configuration)

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/graph/add-edge" :dir :system))
(local (include-book "kestrel/data/graph/add-node" :dir :system))
(local (include-book "kestrel/data/graph/graph" :dir :system))
(local (include-book "kestrel/data/graph/nodes" :dir :system))
(local (include-book "kestrel/data/treeset/cardinality" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/diff" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))
(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ call-graphs
  :parents (utilities)
  :short "A utility to build the call graph of a C translation ensemble."
  :long
  (xdoc::topstring
    (xdoc::p
      "The call graph of a validated translation ensemble is a "
      (xdoc::seetopic "graph::graph" "graph")
      " whose nodes are the "
      (xdoc::seetopic "c$::uid" "unique identifiers")
      " of functions, plus @('nil'), which stands for code we cannot see. A
       function definition has an edge to each function it calls directly,
       and an edge to @('nil') if it calls something we cannot resolve, such
       as a function pointer, or contains an assembler statement. A function
       without a definition in the ensemble, such as a library function or a
       built-in, has an edge to @('nil'). Every edge has the label
       @('nil').")
    (xdoc::p
      "The call graph is sound in the following sense: if a function @('f')
       may call a function @('g'), then @('g') or @('nil') is a successor of
       @('f'). Conversely, an edge from @('f') to a function @('g') means
       that the definition of @('f') contains a call of @('g'). We make no
       attempt to eliminate calls which are never executed, such as calls in
       dead code or in the operand of @('sizeof').")
    (xdoc::p
      "Query the call graph with @(tsee cg-calls-3p), @(tsee cg-calls+-3p), and
       @(tsee cg-recursive-3p). These take the unique identifiers of functions;
       @('resolve-qualified-ident') obtains the unique identifier of a
       function from its name (see @(see qualified-ident)).")
    (xdoc::p
      "Attributes are currently ignored. In particular, the function named by
       a GCC @('cleanup') attribute is called implicitly, but no edge to it is
       recorded."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cg-callee-node ((fun exprp))
  :returns (node c$::uid-optionp)
  :short "The call graph node of the function called by a function call."
  :long
  (xdoc::topstring
    (xdoc::p
      "The argument is the expression in function position of the call.
       Parentheses, the address operator @('&'), and the indirection operator
       @('*') do not change which function is called, so we strip them. If
       what remains is a variable denoting a function, we return its unique
       identifier. Otherwise, we return @('nil').")
    (xdoc::p
      "A variable denotes a function if it has linkage, and it has either a
       function type, or the unknown built-in type and a name starting with
       @('__builtin_'). A function always has linkage, while an object
       declared in a block has none [C17:6.2.2]. The validator gives the
       unknown built-in type to built-ins with that prefix which it does not
       know (see @(tsee c$::prefixed-built-in-identp)), but it also uses that
       type for vector types, so we check the prefix too."))
  (expr-case
    fun
    :ident (b* (((c$::var-vinfo info) (c$::coerce-var-vinfo fun.info))
                (name (ident->unwrap fun.ident)))
             (and (case (type-kind info.type)
                    (:function t)
                    (:unknown-builtin (and (stringp name)
                                           (str::strprefixp "__builtin_"
                                                            name)))
                    (otherwise nil))
                  (not (c$::linkage-case info.linkage :none))
                  info.uid))
    :paren (cg-callee-node fun.inner)
    :unary (and (member-eq (unop-kind fun.op) '(:address :indir))
                (cg-callee-node fun.arg))
    :otherwise nil)
  :measure (expr-count fun))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate ()

  ;; Temporary workaround. In the fixing theorems of the fold, FTY's
  ;; <type>-fix-when-<kind> rules (e.g. struct-declon-fix-when-empty) rewrite
  ;; a fixed AST of a kind without fields to a ground constructor call, and
  ;; the fold functions are then evaluated on it, giving nil, while the other
  ;; side of the equation stays (treeset::empty). Remove this once
  ;; deffold-reduce disables the executable counterparts of the fold
  ;; functions in those proofs.

  (local (in-theory (enable (:e treeset::empty))))

  (fty::deffold-reduce callees
    :short "Definition of the functions which collect the call graph nodes
            called by ASTs."
    :long
    (xdoc::topstring
      (xdoc::p
        "The result is a set of call graph nodes: the unique identifiers of the
         functions called directly, plus @('nil') if the AST may call something
         we cannot resolve.")
      (xdoc::p
        "A function call contributes the node of its callee, as computed by
         @(tsee cg-callee-node), in addition to the nodes called by the callee
         expression and the arguments. An assembler statement may do anything,
         so it contributes @('nil').")
      (xdoc::p
        "We stop at function definitions. A function definition's callees
         include those in its declarator, because the size expressions of
         variably modified parameters are evaluated on entry to the function
         [C17:6.9.1/10]."))
    :types (c$::exprs/decls/stmts
            fundef)
    :result treeset::setp
    :default (treeset::empty)
    :combine treeset::union
    :override
    ((expr :funcall (treeset::insert (cg-callee-node expr.fun)
                                     (treeset::union
                                       (expr-callees expr.fun)
                                       (expr-list-callees expr.args))))
     (c$::stmt :asm (treeset::set nil)))
    :name abstract-syntax-callees))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cg-add-call-edges (caller (callees treeset::setp) (graph graph::graphp))
  :returns (graph$ graph::graphp)
  :short "Add an edge from a caller to each node in a set."
  (if (treeset::emptyp callees)
      (graph::fix graph)
    (cg-add-call-edges caller
                    (treeset::delete (treeset::min callees) callees)
                    (graph::add-edge caller (treeset::min callees) nil graph)))
  :measure (treeset::cardinality callees))

(define cg-add-unknown-edges ((nodes treeset::setp) (graph graph::graphp))
  :returns (graph$ graph::graphp)
  :short "Add an edge from each node in a set to @('nil')."
  (if (treeset::emptyp nodes)
      (graph::fix graph)
    (cg-add-unknown-edges (treeset::delete (treeset::min nodes) nodes)
                       (graph::add-edge (treeset::min nodes) nil nil graph)))
  :measure (treeset::cardinality nodes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fundef-call-graph ((fundef fundefp)
                           (graph graph::graphp)
                           (defined treeset::setp))
  :guard (fundef-annop fundef)
  :returns (mv (graph$ graph::graphp)
               (defined$ treeset::setp))
  :short "Add the edges of a function definition to the call graph."
  :long
  (xdoc::topstring-p
    "We also add the function to the set of defined functions.")
  (b* ((caller (type+uid-vinfo->uid (fundef->info fundef))))
    (mv (cg-add-call-edges caller
                        (fundef-callees fundef)
                        (graph::add-node caller graph))
        (treeset::insert caller defined)))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules))))

(define ext-declon-call-graph ((declon ext-declonp)
                               (graph graph::graphp)
                               (defined treeset::setp))
  :guard (ext-declon-annop declon)
  :returns (mv (graph$ graph::graphp)
               (defined$ treeset::setp))
  :short "Add the edges of an external declaration to the call graph."
  (ext-declon-case
    declon
    :fundef (fundef-call-graph declon.fundef graph defined)
    :otherwise (mv (graph::fix graph) (treeset::fix defined)))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules))))

(define trans-item-call-graph ((item trans-itemp)
                               (graph graph::graphp)
                               (defined treeset::setp))
  :guard (trans-item-annop item)
  :returns (mv (graph$ graph::graphp)
               (defined$ treeset::setp))
  :short "Add the edges of a translation unit item to the call graph."
  :long
  (xdoc::topstring-p
    "The validator does not support @('#include') directives or conditional
     directives, so they should not occur.")
  (trans-item-case
    item
    :declon (ext-declon-call-graph item.declon graph defined)
    :include (prog2$ (raise "Internal error: unexpected #include directive.")
                     (mv (graph::fix graph) (treeset::fix defined)))
    :cond (prog2$ (raise "Internal error: unexpected conditional directive.")
                  (mv (graph::fix graph) (treeset::fix defined)))
    :otherwise (mv (graph::fix graph) (treeset::fix defined)))
  :no-function nil
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules))))

(define trans-item-list-call-graph ((items trans-item-listp)
                                    (graph graph::graphp)
                                    (defined treeset::setp))
  :guard (trans-item-list-annop items)
  :returns (mv (graph$ graph::graphp)
               (defined$ treeset::setp))
  :short "Add the edges of a list of translation unit items to the call
          graph."
  (b* (((when (endp items))
        (mv (graph::fix graph) (treeset::fix defined)))
       ((mv graph defined)
        (trans-item-call-graph (first items) graph defined)))
    (trans-item-list-call-graph (rest items) graph defined))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules))))

(define filepath-trans-unit-map-call-graph ((map filepath-trans-unit-mapp)
                                            (graph graph::graphp)
                                            (defined treeset::setp))
  :guard (filepath-trans-unit-map-annop map)
  :returns (mv (graph$ graph::graphp)
               (defined$ treeset::setp))
  :short "Add the edges of a map of translation units to the call graph."
  (b* ((map (c$::filepath-trans-unit-map-fix map))
       ((when (omap::emptyp map))
        (mv (graph::fix graph) (treeset::fix defined)))
       ((mv graph defined)
        (trans-item-list-call-graph (trans-unit->items (omap::head-val map))
                                    graph
                                    defined)))
    (filepath-trans-unit-map-call-graph (omap::tail map) graph defined))
  :measure (acl2-count (c$::filepath-trans-unit-map-fix map))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules))))

(define trans-ensemble-call-graph ((ensemble trans-ensemblep))
  :guard (trans-ensemble-annop ensemble)
  :returns (call-graph graph::graphp)
  :short "Build the call graph of a translation ensemble."
  :long
  (xdoc::topstring-p
    "After adding the edges of all function definitions, we add an edge to
     @('nil') from every other node except @('nil') itself: these are the
     functions called without a definition in the ensemble.")
  (b* (((mv graph defined)
        (filepath-trans-unit-map-call-graph (trans-ensemble->units ensemble)
                                            (graph::empty)
                                            (treeset::empty))))
    (cg-add-unknown-edges (treeset::delete nil
                                        (treeset::diff (graph::nodes graph)
                                                       defined))
                       graph))
  :guard-hints (("Goal" :in-theory (enable* c$::abstract-syntax-annop-rules))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cg-calls-3p ((caller uidp) (callee uidp) (call-graph graph::graphp))
  :returns (3vl acl2::3p)
  :short "Check whether a function contains a call of another function."
  :long
  (xdoc::topstring
    (xdoc::p
      "The result is @('t') if the definition of @('caller') contains a call
       of @('callee'), and @('nil') if no code which @('caller') may run
       contains such a call. Otherwise, it is @(':unknown'): the call graph
       has no edge to @('callee'), but @('caller') may run code we cannot
       see, for instance because it has no definition in the ensemble.")
    (xdoc::p
      "Note that @('t') only means that a call appears in the code, not that
       it is ever executed."))
  (b* ((caller (uid-fix caller))
       (callee (uid-fix callee)))
    (cond ((not (graph::node-in caller call-graph)) :unknown)
          ((graph::adjacentp caller callee call-graph) t)
          ((graph::adjacentp caller nil call-graph) :unknown)
          (t nil))))

(define cg-calls+-3p ((caller uidp) (callee uidp) (call-graph graph::graphp))
  :returns (3vl acl2::3p)
  :short "Check whether a function contains a call of another function,
          directly or through a chain of calls."
  :long
  (xdoc::topstring
    (xdoc::p
      "This is the transitive version of @(tsee cg-calls-3p). The result is
       @('t') if the call graph has a path from @('caller') to @('callee'),
       and @('nil') if it reaches neither @('callee') nor @('nil'). Otherwise,
       it is @(':unknown').")
    (xdoc::p
      "Note that @('t') only means that a chain of calls appears in the
       code, not that it is ever executed."))
  (b* ((caller (uid-fix caller))
       (callee (uid-fix callee)))
    (cond ((not (graph::node-in caller call-graph)) :unknown)
          ((graph::reachable+p caller callee call-graph) t)
          ((graph::reachable+p caller nil call-graph) :unknown)
          (t nil))))

(define cg-recursive-3p ((fn uidp) (call-graph graph::graphp))
  :returns (3vl acl2::3p)
  :short "Check whether a function is recursive, directly or mutually."
  :long
  (xdoc::topstring-p
    "This is @(tsee cg-calls+-3p) from the function to itself. A result of
     @('nil') means that the function cannot call itself.")
  (cg-calls+-3p fn fn call-graph))
