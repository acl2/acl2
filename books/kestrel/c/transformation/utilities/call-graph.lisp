; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)

(include-book "../../syntax/abstract-syntax-operations")
(include-book "../../syntax/validator")

(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ call-graphs
  :parents (utilities)
  :short "Utilities to build a call graph from C translation units."
  :long
  (xdoc::topstring
    (xdoc::p
      "A call graph is a map from function names to the set of all functions
       which are called in the original function's body. For instance, consider
       the following C source file:")
    (xdoc::codeblock
      "void bar(void);"
      ""
      "void foo(int x) {"
      "  foo(x);"
      "  bar(x);"
      "}"
      ""
      "void bar(int x) {"
      "  foo(x);"
      "}"
      ""
      "int baz(int z) {"
      "  if (z) {"
      "    return z;"
      "  }"
      "  return baz(z - 1);"
      "}"
      ""
      "int main() {"
      "  int x = 5;"
      "  return foo(x);"
      "}")
    (xdoc::p
      "The call graph for this function would associate @('foo') to @('foo')
       and @('bar'), @('bar') to @('foo'), @('baz') to @('baz'), and @('main')
       to @('foo').")
    (xdoc::p
      "If a call graph edge connects a function to itself, this function is
       directly recursive. We may also construct the transitive closure of the
       call graph given some initial function @(tsee
       call-graph-transitive-closure)). This closure represents all functions
       which are reachable through some path of function calls. Notably, a
       mutually recursive function is in its own transitive closure. See @(tsee
       direct-recursivep) and @(tsee recursivep).")
    (xdoc::p
      "Identifiers in the call graph are qualified to distinguish internal
       functions of the same name across different translation units. See @(see
       qualified-ident).")
    (xdoc::p
      "Note that call graph construction currently only recognizes direct
       function calls. No sort of analysis is done to attempt to resolve calls
       of dereferenced function pointers. We may wish to add such analysis in
       the future. Although the problem is undecidable in general, many common
       cases may be straightforward in practice. Currently, a call of a
       function pointer is represented as @('nil') in the call graph, so that
       we can distinguish between function call subgraphs which are known to be
       complete, and those which contain unresolved function calls. See also
       @(tsee uncertain-call-pathp)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod qualified-ident
  :short "Fixtype for fully qualified identifiers"
  :long
  (xdoc::topstring
    (xdoc::p
      "This type tags an identifiers with an optional filepath for the
       translation unit in which it was defined. This tagged identifier is
       unique across a translation unit ensemble.")
    (xdoc::p
      "Only identifiers with internal linkage are tagged with a
       filepath. External identifiers do not need qualification, as they are
       already unique across the translation unit ensemble."))
  ((filepath? c$::filepath-option)
   (ident ident))
  :pred qualified-identp)

(fty::defoption qualified-ident-option
  qualified-ident
  :pred qualified-ident-optionp)

(fty::defset qualified-ident-option-set
  :elt-type qualified-ident-option
  :elementp-of-nil t
  :pred qualified-ident-option-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define qualified-ident-externalp
  ((ident qualified-identp))
  (declare (xargs :type-prescription
                  (booleanp (qualified-ident-externalp ident))))
  :parents (qualified-ident)
  (not (qualified-ident->filepath? ident)))

(define qualified-ident-internalp
  ((ident qualified-identp))
  (declare (xargs :type-prescription
                  (booleanp (qualified-ident-internalp ident))))
  :parents (qualified-ident)
  (and (qualified-ident->filepath? ident) t))

(defrule qualified-ident-internalp-becomes-not-qualified-ident-externalp
  (equal (qualified-ident-internalp ident)
         (not (qualified-ident-externalp ident)))
  :enable (qualified-ident-internalp
           qualified-ident-externalp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define external-ident
  ((ident identp))
  :returns (qualified-ident qualified-identp)
  :parents (qualified-ident)
  (make-qualified-ident
   :ident ident))

(defrule qualified-ident-externalp-of-external-ident
  (qualified-ident-externalp (external-ident ident))
  :enable (qualified-ident-externalp
           external-ident))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define internal-ident
  ((filepath filepathp)
   (ident identp))
  :returns (qualified-ident qualified-identp)
  :parents (qualified-ident)
  (make-qualified-ident
   :filepath? (c$::filepath-fix filepath)
   :ident ident))

(defrule qualified-ident-internalp-of-internal-ident
  (qualified-ident-internalp (internal-ident filepath ident))
  :enable (qualified-ident-internalp
           internal-ident)
  :disable qualified-ident-internalp-becomes-not-qualified-ident-externalp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap call-graph
  :key-type qualified-ident
  :val-type qualified-ident-option-set
  :pred call-graphp)

(defrulel qualified-ident-option-setp-of-cdr-assoc-when-call-graphp
  (implies (call-graphp graph)
           (qualified-ident-option-setp (cdr (omap::assoc key graph))))
  :induct t
  :enable omap::assoc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define call-graph-update
  ((fn-name qualified-identp)
   (called-fn-name? qualified-ident-optionp)
   (call-graph call-graphp))
  :returns (call-graph$ call-graphp)
  (b* ((call-graph (call-graph-fix call-graph))
       (assoc (omap::assoc fn-name call-graph))
       (set (if assoc (cdr assoc) nil)))
    (omap::update (qualified-ident-fix fn-name)
                  (insert (qualified-ident-option-fix called-fn-name?) set)
                  call-graph)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define qualify-ident
  ((filepath filepathp)
   (valid-table c$::valid-tablep)
   (ident identp))
  :returns (qualified-ident qualified-identp)
  (b* ((info? (c$::valid-lookup-ord-file-scope ident valid-table))
       (is-internal
         (and info?
              (c$::valid-ord-info-case
                info?
                :objfun (equal (c$::valid-ord-info-objfun->linkage info?)
                               (c$::linkage-internal))
                :otherwise nil))))
    (if is-internal
        (internal-ident filepath ident)
      (external-ident ident))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define direct-fun-refp
  ((ident identp)
   (valid-table c$::valid-tablep))
  (declare (xargs :type-prescription
                  (booleanp (direct-fun-refp ident valid-table))))
  (b* ((info? (c$::valid-lookup-ord-file-scope ident valid-table)))
    (and info?
         (c$::valid-ord-info-case
           info?
           :objfun t
           :otherwise nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines call-graph-exprs-decls
  (define call-graph-expr
    ((expr exprp)
     (fn-name qualified-identp)
     (filepath filepathp)
     (valid-table c$::valid-tablep)
     (call-graph call-graphp))
    ;; :guard (expr-annop expr)
    :returns (call-graph$ call-graphp)
    (expr-case
     expr
     :paren (call-graph-expr expr.inner fn-name filepath valid-table call-graph)
     ;; :gensel?
     :arrsub (call-graph-expr
               expr.arg2
               fn-name
               filepath
               valid-table
               (call-graph-expr
                 expr.arg1
                 fn-name
                 filepath
                 valid-table
                 call-graph))
     ;; TODO: add a test of function calls appearing in function call arguments
     :funcall (b* ((qualified-ident?
                     (expr-case
                       expr.fun
                       :ident (and (direct-fun-refp expr.fun.ident valid-table)
                                   (qualify-ident filepath
                                                  valid-table
                                                  expr.fun.ident))
                       :otherwise nil)))
                (call-graph-expr-list expr.args
                                      fn-name
                                      filepath
                                      valid-table
                                      (call-graph-update fn-name
                                                         qualified-ident?
                                                         call-graph)))
     :member (call-graph-expr
               expr.arg
               fn-name
               filepath
               valid-table
               call-graph)
     :memberp (call-graph-expr
                expr.arg
                fn-name
                filepath
                valid-table
                call-graph)
     :complit (call-graph-desiniter-list
                expr.elems
                fn-name
                filepath
                valid-table
                call-graph)
     :unary (call-graph-expr
              expr.arg
              fn-name
              filepath
              valid-table
              call-graph)
     :cast (call-graph-expr
             expr.arg
             fn-name
             filepath
             valid-table
             call-graph)
     :binary (call-graph-expr
               expr.arg2
               fn-name
               filepath
               valid-table
               (call-graph-expr
                 expr.arg1
                 fn-name
                 filepath
                 valid-table
                 call-graph))
     :cond (call-graph-expr
             expr.else
             fn-name
             filepath
             valid-table
             (call-graph-expr-option
               expr.then
               fn-name
               filepath
               valid-table
               (call-graph-expr
                 expr.test
                 fn-name
                 filepath
                 valid-table
                 call-graph)))
     :comma (call-graph-expr
              expr.next
              fn-name
              filepath
              valid-table
              (call-graph-expr
                expr.first
                fn-name
                filepath
                valid-table
                call-graph))
     ;; TODO: error on ambiguous constructs
     :otherwise (call-graph-fix call-graph))
    :measure (expr-count expr))

  (define call-graph-expr-list
    ((exprs expr-listp)
     (fn-name qualified-identp)
     (filepath filepathp)
     (valid-table c$::valid-tablep)
     (call-graph call-graphp))
    :returns (call-graph$ call-graphp)
    (if (endp exprs)
        (call-graph-fix call-graph)
      (call-graph-expr-list (rest exprs)
                            fn-name
                            filepath
                            valid-table
                            (call-graph-expr (first exprs)
                                             fn-name
                                             filepath
                                             valid-table
                                             call-graph)))
    :measure (expr-list-count exprs))

  (define call-graph-expr-option
    ((expr? expr-optionp)
     (fn-name qualified-identp)
     (filepath filepathp)
     (valid-table c$::valid-tablep)
     (call-graph call-graphp))
    :returns (call-graph$ call-graphp)
    (expr-option-case
     expr?
     :some (call-graph-expr expr?.val fn-name filepath valid-table call-graph)
     :none (call-graph-fix call-graph))
    :measure (expr-option-count expr?))

  (define call-graph-initer
    ((initer initerp)
     (fn-name qualified-identp)
     (filepath filepathp)
     (valid-table c$::valid-tablep)
     (call-graph call-graphp))
    :returns (call-graph$ call-graphp)
    (initer-case
     initer
     :single (call-graph-expr initer.expr fn-name filepath valid-table call-graph)
     :list (call-graph-desiniter-list initer.elems fn-name filepath valid-table call-graph))
    :measure (initer-count initer))

  (define call-graph-initer-option
    ((initer? initer-optionp)
     (fn-name qualified-identp)
     (filepath filepathp)
     (valid-table c$::valid-tablep)
     (call-graph call-graphp))
    :returns (call-graph$ call-graphp)
    (initer-option-case
     initer?
     :some (call-graph-initer initer?.val fn-name filepath valid-table call-graph)
     :none (call-graph-fix call-graph))
    :measure (initer-option-count initer?))

  (define call-graph-desiniter
    ((desiniter desiniterp)
     (fn-name qualified-identp)
     (filepath filepathp)
     (valid-table c$::valid-tablep)
     (call-graph call-graphp))
    :returns (call-graph$ call-graphp)
    (b* (((desiniter desiniter) desiniter))
      (call-graph-initer desiniter.initer fn-name filepath valid-table call-graph))
    :measure (desiniter-count desiniter))

  (define call-graph-desiniter-list
    ((desiniters desiniter-listp)
     (fn-name qualified-identp)
     (filepath filepathp)
     (valid-table c$::valid-tablep)
     (call-graph call-graphp))
    :returns (call-graph$ call-graphp)
    (if (endp desiniters)
        (call-graph-fix call-graph)
      (call-graph-desiniter-list
        (rest desiniters)
        fn-name
        filepath
        valid-table
        (call-graph-desiniter (first desiniters) fn-name filepath valid-table call-graph)))
    :measure (desiniter-list-count desiniters))

  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns)

(define call-graph-const-expr
  ((const-expr const-exprp)
   (fn-name qualified-identp)
   (filepath filepathp)
   (valid-table c$::valid-tablep)
   (call-graph call-graphp))
  :returns (call-graph$ call-graphp)
  (b* (((const-expr const-expr) const-expr))
    (call-graph-expr const-expr.expr fn-name filepath valid-table call-graph)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define call-graph-initdeclor
  ((initdeclor initdeclorp)
   (fn-name qualified-identp)
   (filepath filepathp)
   (valid-table c$::valid-tablep)
   (call-graph call-graphp))
  :returns (call-graph$ call-graphp)
  (b* (((initdeclor initdeclor) initdeclor))
    ;; TODO: need to look at initdeclor.declor?
    (call-graph-initer-option initdeclor.init? fn-name filepath valid-table call-graph)))

(define call-graph-initdeclor-list
  ((initdeclors initdeclor-listp)
   (fn-name qualified-identp)
   (filepath filepathp)
   (valid-table c$::valid-tablep)
   (call-graph call-graphp))
  :returns (call-graph$ call-graphp)
  (if (endp initdeclors)
      (call-graph-fix call-graph)
    (call-graph-initdeclor-list
      (rest initdeclors)
      fn-name
      filepath
      valid-table
      (call-graph-initdeclor (first initdeclors) fn-name filepath valid-table call-graph))))

(define call-graph-statassert
  ((statassert statassertp)
   (fn-name qualified-identp)
   (filepath filepathp)
   (valid-table c$::valid-tablep)
   (call-graph call-graphp))
  :returns (call-graph$ call-graphp)
  (b* (((statassert statassert) statassert))
    (call-graph-const-expr statassert.test fn-name filepath valid-table call-graph)))

(define call-graph-decl
  ((decl declp)
   (fn-name qualified-identp)
   (filepath filepathp)
   (valid-table c$::valid-tablep)
   (call-graph call-graphp))
  :returns (call-graph$ call-graphp)
  (decl-case
   decl
   :decl (call-graph-initdeclor-list decl.init fn-name filepath valid-table call-graph)
   ;; TODO: Do we want function calls in statasserts to be part of our call
   ;;   graph?
   :statassert (call-graph-statassert decl.unwrap fn-name filepath valid-table call-graph)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines call-graph-stmts/block
  (define call-graph-stmt
    ((stmt stmtp)
     (fn-name qualified-identp)
     (filepath filepathp)
     (valid-table c$::valid-tablep)
     (call-graph call-graphp))
    :returns (call-graph$ call-graphp)
    (stmt-case
     stmt
     :labeled (call-graph-stmt stmt.stmt fn-name filepath valid-table call-graph)
     :compound (call-graph-block-item-list stmt.items fn-name filepath valid-table call-graph)
     :expr (call-graph-expr-option stmt.expr? fn-name filepath valid-table call-graph)
     :if (call-graph-stmt
           stmt.then
           fn-name
           filepath
           valid-table
           (call-graph-expr stmt.test fn-name filepath valid-table call-graph))
     :ifelse (call-graph-stmt
               stmt.else
               fn-name
               filepath
               valid-table
               (call-graph-stmt
                 stmt.then
                 fn-name
                 filepath
                 valid-table
                 (call-graph-expr stmt.test fn-name filepath valid-table call-graph)))
     :switch (call-graph-stmt
               stmt.body
               fn-name
               filepath
               valid-table
               (call-graph-expr stmt.target fn-name filepath valid-table call-graph))
     :while (call-graph-stmt
              stmt.body
              fn-name
              filepath
              valid-table
              (call-graph-expr stmt.test fn-name filepath valid-table call-graph))
     :dowhile (call-graph-expr
                stmt.test
                fn-name
                filepath
                valid-table
                (call-graph-stmt stmt.body fn-name filepath valid-table call-graph))
     :for-expr (call-graph-stmt
                 stmt.body
                 fn-name
                 filepath
                 valid-table
                 (call-graph-expr-option
                   stmt.next
                   fn-name
                   filepath
                   valid-table
                   (call-graph-expr-option
                     stmt.test
                     fn-name
                     filepath
                     valid-table
                     (call-graph-expr-option
                       stmt.init
                       fn-name
                       filepath
                       valid-table
                       call-graph))))
     :for-decl (call-graph-stmt
                 stmt.body
                 fn-name
                 filepath
                 valid-table
                 (call-graph-expr-option
                   stmt.next
                   fn-name
                   filepath
                   valid-table
                   (call-graph-expr-option
                     stmt.test
                     fn-name
                     filepath
                     valid-table
                     (call-graph-decl
                       stmt.init
                       fn-name
                       filepath
                       valid-table
                       call-graph))))
     ;; TODO: error on ambiguous constructs
     ;; :for-ambig
     :return (call-graph-expr-option stmt.expr? fn-name filepath valid-table call-graph)
     :otherwise (call-graph-fix call-graph))
    :measure (stmt-count stmt))

  (define call-graph-block-item
    ((item block-itemp)
     (fn-name qualified-identp)
     (filepath filepathp)
     (valid-table c$::valid-tablep)
     (call-graph call-graphp))
    :returns (call-graph$ call-graphp)
    (block-item-case
     item
     :decl (call-graph-decl item.decl fn-name filepath valid-table call-graph)
     :stmt (call-graph-stmt item.stmt fn-name filepath valid-table call-graph)
     ;; TODO: error on ambiguous constructs
     :ambig (call-graph-fix call-graph))
    :measure (block-item-count item))

  (define call-graph-block-item-list
    ((items block-item-listp)
     (fn-name qualified-identp)
     (filepath filepathp)
     (valid-table c$::valid-tablep)
     (call-graph call-graphp))
    :returns (call-graph$ call-graphp)
    (if (endp items)
        (call-graph-fix call-graph)
      (call-graph-block-item-list
        (rest items)
        fn-name
        filepath
        valid-table
        (call-graph-block-item (first items) fn-name filepath valid-table call-graph)))
    :measure (block-item-list-count items))

   :hints (("Goal" :in-theory (enable o< o-finp)))
   :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define call-graph-fundef
  ((fundef fundefp)
   (filepath filepathp)
   (valid-table c$::valid-tablep)
   (call-graph call-graphp))
  :returns (call-graph$ call-graphp)
  (b* (((fundef fundef) fundef)
       ((declor fundef.declor) fundef.declor))
    (dirdeclor-case
      fundef.declor.direct
      :function-params (b* ((fn-name
                              (c$::dirdeclor->ident fundef.declor.direct.declor))
                            (qualified-fn-name
                              (qualify-ident filepath valid-table fn-name)))
                         (call-graph-block-item-list
                           fundef.body
                           qualified-fn-name
                           filepath
                           valid-table
                           call-graph))
      :function-names (b* ((fn-name
                             (c$::dirdeclor->ident fundef.declor.direct.declor))
                           (qualified-fn-name
                             (qualify-ident filepath valid-table fn-name)))
                        (call-graph-block-item-list
                          fundef.body
                          qualified-fn-name
                          filepath
                          valid-table
                          call-graph))
      :otherwise (call-graph-fix call-graph))))

(define call-graph-extdecl
  ((extdecl extdeclp)
   (filepath filepathp)
   (valid-table c$::valid-tablep)
   (call-graph call-graphp))
  :returns (call-graph$ call-graphp)
  (extdecl-case
   extdecl
   :fundef (call-graph-fundef extdecl.unwrap filepath valid-table call-graph)
   :decl (call-graph-fix call-graph)
   :empty (call-graph-fix call-graph)
   :asm (call-graph-fix call-graph)))

(define call-graph-extdecl-list
  ((extdecls extdecl-listp)
   (filepath filepathp)
   (valid-table c$::valid-tablep)
   (call-graph call-graphp))
  :returns (call-graph$ call-graphp)
  (if (endp extdecls)
      (call-graph-fix call-graph)
    (call-graph-extdecl-list
      (rest extdecls)
      filepath
      valid-table
      (call-graph-extdecl
        (first extdecls)
        filepath
        valid-table
        call-graph))))

(define call-graph-transunit
  ((filepath filepathp)
   (transunit transunitp)
   (call-graph call-graphp))
  :guard (c$::transunit-annop transunit)
  :returns (call-graph$ call-graphp)
  :short "Build a call graph corresponding to a translation unit."
  (b* (((transunit transunit) transunit)
       (info (c$::transunit-info-fix (c$::transunit->info transunit)))
       (valid-table (c$::transunit-info->table info)))
    (call-graph-extdecl-list transunit.decls filepath valid-table call-graph))
  :guard-hints (("Goal" :in-theory (enable c$::transunit-annop))))

(define call-graph-filepath-transunit-map
  ((map filepath-transunit-mapp)
   (call-graph call-graphp))
  :guard (c$::filepath-transunit-map-annop map)
  :returns (call-graph$ call-graphp)
  (if (omap::emptyp map)
      (call-graph-fix call-graph)
    (call-graph-filepath-transunit-map
      (omap::tail map)
      (call-graph-transunit
        (omap::head-key map)
        (omap::head-val map)
        call-graph)))
  :guard-hints
  (("Goal" :in-theory (acl2::enable* c$::abstract-syntax-annop-rules))))

(define call-graph-transunit-ensemble
  ((ensemble transunit-ensemblep))
  :guard (c$::transunit-ensemble-annop ensemble)
  :returns (call-graph$ call-graphp)
  :short "Build a call graph corresponding to a translation unit ensemble."
  (call-graph-filepath-transunit-map
   (c$::transunit-ensemble->unwrap ensemble)
   nil)
  :guard-hints (("Goal" :in-theory (enable c$::transunit-ensemble-annop))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define call-graph-transitive-closure
  ((ident qualified-identp)
   (call-graph call-graphp))
  :returns (called qualified-ident-option-setp)
  :short "Build a transitive closure for some identifier in the given call graph."
  :long
  (xdoc::topstring
   (xdoc::p
     "If a function @('f') calls @('g') (i.e. the call graph has an edge from
      @('f') to @('g')), @('g') is in @('f')'s transitive closure. If @('h')
      calls @('i'), and @('h') is in @('f')'s transitive closure, then @('i') is
      also in @('f')'s transitive closure)."))
  (call-graph-transitive-closure0
   (insert ident nil)
   call-graph
   nil
   (acl2::the-fixnat (- (expt 2 acl2::*fixnat-bits*) 1)))

  :prepwork
  ((local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
   (local (include-book "kestrel/utilities/nfix" :dir :system))

   ;; Currently we are using a step counter for termination.
   ;; TODO: replace step with termination argument. The measure may be
   ;; lexicographic, primarily measuring the difference in size of call-graph with
   ;; respect to the identifiers in the call graph (call-graph is a subset of the this
   ;; finite set of identifiers), and secondarily the decrease of ident?s.
   (define call-graph-transitive-closure0
     ((ident?s qualified-ident-option-setp)
      (call-graph call-graphp)
      (called qualified-ident-option-setp)
      (steps :type (unsigned-byte 60)))
     :returns (called$ qualified-ident-option-setp)
     (b* (((when (or (int= 0 (mbe :logic (if (natp (acl2::the-fixnat steps))
                                             (acl2::the-fixnat steps)
                                           0)
                                  :exec (acl2::the-fixnat steps)))
                     (emptyp ident?s)))
           (qualified-ident-option-set-fix called))
          (ident? (head ident?s))
          ((when (not ident?))
           (call-graph-transitive-closure0
             (tail ident?s)
             call-graph
             (insert nil called)
             (- steps 1)))
          (lookup (omap::assoc ident? call-graph))
          (ident?s
            (if lookup
                (union (difference (cdr lookup) called)
                       (tail ident?s))
              (tail ident?s)))
          (called
            (if lookup
                (union (cdr lookup) called)
              called)))
       (call-graph-transitive-closure0
         ident?s
         call-graph
         called
         (- steps 1)))
     :measure (nfix steps)
     :hints (("Goal" :in-theory (enable o< o-finp))))))

(define exists-call-pathp
  ((from qualified-identp)
   (to qualified-ident-optionp)
   (call-graph call-graphp))
  :short "Check for the existence of a call path from the destination to the
          target."
  :long
  (xdoc::topstring
   (xdoc::p
     "That is, the function checks whether @('to') is in @('from')'s transitive
      closure. See @(tsee call-graph-transitive-closure)."))
  (in to (call-graph-transitive-closure from call-graph)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define direct-recursivep
  ((ident qualified-identp)
   (call-graph call-graphp))
  :short "Recognizes functions which calls themselves."
  :long
  (xdoc::topstring
   (xdoc::p
     "This function checks where the @('ident') is related to itself under the
      call graph. See @(tsee call-graph-transitive-closure) and (see
      call-graph)."))
  (b* ((lookup (omap::assoc ident call-graph)))
    (and lookup
         (in ident (cdr lookup)))))

(define recursivep
  ((ident qualified-identp)
   (call-graph call-graphp))
  :short "Recognizes directly or mutually recursive functions."
  :long
  (xdoc::topstring
   (xdoc::p
     "This function checks whether @('ident') is in its own transitive
      closure. See @(tsee call-graph-transitive-closure) and (see
      call-graph)."))
  (exists-call-pathp ident ident call-graph))

(define uncertain-call-pathp
  ((ident qualified-identp)
   (call-graph call-graphp))
  :short "Recognizes functions which possess an unresolved function call path."
  :long
  (xdoc::topstring
   (xdoc::p
     "This function checks whether nil is in @('ident')'s transitive
      closure. See @(tsee call-graph-transitive-closure) and (see
      call-graph)."))
  (exists-call-pathp ident nil call-graph))
