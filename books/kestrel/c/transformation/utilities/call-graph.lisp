; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
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

(include-book "../../syntax/abstract-syntax")
(include-book "free-vars")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ call-graph
  :parents (utilities)
  :short "A utility to build a call graph given a C translation unit."
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

(encapsulate ()
  (set-induction-depth-limit 1)

  (fty::defomap ident-ident-option-set-map
    :key-type ident
    :val-type ident-option-set
    :pred ident-ident-option-set-mapp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define call-graph-update
  ((fn-name identp)
   (called-fn-name ident-optionp)
   (call-graph ident-ident-option-set-mapp))
  :returns (new-call-graph ident-ident-option-set-mapp)
  (b* ((call-graph (ident-ident-option-set-map-fix call-graph))
       (assoc (omap::assoc fn-name call-graph))
       (set (if assoc (cdr assoc) nil)))
    (omap::update (ident-fix fn-name)
                  (insert (ident-option-fix called-fn-name) set)
                  call-graph)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines call-graph-exprs-decls
  (define call-graph-expr
    ((expr exprp)
     (fn-name identp)
     (acc ident-ident-option-set-mapp))
    :returns (call-graph ident-ident-option-set-mapp)
    (expr-case
     expr
     :paren (call-graph-expr expr.unwrap fn-name acc)
     ;; :gensel?
     :arrsub (call-graph-expr
               expr.arg2
               fn-name
               (call-graph-expr
                 expr.arg1
                 fn-name
                 acc))
     :funcall (call-graph-update fn-name
                                 (expr-case
                                   expr.fun
                                   :ident expr.fun.unwrap
                                   :otherwise nil)
                                 acc)
     :member (call-graph-expr
               expr.arg
               fn-name
               acc)
     :memberp (call-graph-expr
                expr.arg
                fn-name
                acc)
     :complit (call-graph-desiniter-list
                expr.elems
                fn-name
                acc)
     :unary (call-graph-expr
              expr.arg
              fn-name
              acc)
     :cast (call-graph-expr
             expr.arg
             fn-name
             acc)
     :binary (call-graph-expr
               expr.arg2
               fn-name
               (call-graph-expr
                 expr.arg1
                 fn-name
                 acc))
     :cond (call-graph-expr
             expr.else
             fn-name
             (call-graph-expr
               expr.then
               fn-name
               (call-graph-expr
                 expr.test
                 fn-name
                 acc)))
     :comma (call-graph-expr
              expr.next
              fn-name
              (call-graph-expr
                expr.first
                fn-name
                acc))
     ;; TODO: error on ambiguous constructs
     :otherwise (ident-ident-option-set-map-fix acc))
    :measure (expr-count expr))

  (define call-graph-initer
    ((initer initerp)
     (fn-name identp)
     (acc ident-ident-option-set-mapp))
    :returns (call-graph ident-ident-option-set-mapp)
    (initer-case
     initer
     :single (call-graph-expr initer.expr fn-name acc)
     :list (call-graph-desiniter-list initer.elems fn-name acc))
    :measure (initer-count initer))

  (define call-graph-initer-option
    ((initer? initer-optionp)
     (fn-name identp)
     (acc ident-ident-option-set-mapp))
    :returns (call-graph ident-ident-option-set-mapp)
    (initer-option-case
     initer?
     :some (call-graph-initer initer?.val fn-name acc)
     :none (ident-ident-option-set-map-fix acc))
    :measure (initer-option-count initer?))

  (define call-graph-desiniter
    ((desiniter desiniterp)
     (fn-name identp)
     (acc ident-ident-option-set-mapp))
    :returns (call-graph ident-ident-option-set-mapp)
    (b* (((desiniter desiniter) desiniter))
      (call-graph-initer desiniter.init fn-name acc))
    :measure (desiniter-count desiniter))

  (define call-graph-desiniter-list
    ((desiniters desiniter-listp)
     (fn-name identp)
     (acc ident-ident-option-set-mapp))
    :returns (call-graph ident-ident-option-set-mapp)
    (if (endp desiniters)
        (ident-ident-option-set-map-fix acc)
      (call-graph-desiniter-list
        (rest desiniters)
        fn-name
        (call-graph-desiniter (first desiniters) fn-name acc)))
    :measure (desiniter-list-count desiniters))

  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns)

(define call-graph-const-expr
  ((const-expr const-exprp)
   (fn-name identp)
   (acc ident-ident-option-set-mapp))
  :returns (call-graph ident-ident-option-set-mapp)
  (b* (((const-expr const-expr) const-expr))
    (call-graph-expr const-expr.unwrap fn-name acc)))

(define call-graph-expr-option
  ((expr? expr-optionp)
   (fn-name identp)
   (acc ident-ident-option-set-mapp))
  :returns (call-graph ident-ident-option-set-mapp)
  (expr-option-case
   expr?
   :some (call-graph-expr expr?.val fn-name acc)
   :none (ident-ident-option-set-map-fix acc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define call-graph-initdeclor
  ((initdeclor initdeclorp)
   (fn-name identp)
   (acc ident-ident-option-set-mapp))
  :returns (call-graph ident-ident-option-set-mapp)
  (b* (((initdeclor initdeclor) initdeclor))
    ;; TODO: need to look at initdeclor.declor?
    (call-graph-initer-option initdeclor.init? fn-name acc)))

(define call-graph-initdeclor-list
  ((initdeclors initdeclor-listp)
   (fn-name identp)
   (acc ident-ident-option-set-mapp))
  :returns (call-graph ident-ident-option-set-mapp)
  (if (endp initdeclors)
      (ident-ident-option-set-map-fix acc)
    (call-graph-initdeclor-list
      (rest initdeclors)
      fn-name
      (call-graph-initdeclor (first initdeclors) fn-name acc))))

(define call-graph-statassert
  ((statassert statassertp)
   (fn-name identp)
   (acc ident-ident-option-set-mapp))
  :returns (call-graph ident-ident-option-set-mapp)
  (b* (((statassert statassert) statassert))
    (call-graph-const-expr statassert.test fn-name acc)))

(define call-graph-decl
  ((decl declp)
   (fn-name identp)
   (acc ident-ident-option-set-mapp))
  :returns (call-graph ident-ident-option-set-mapp)
  (decl-case
   decl
   :decl (call-graph-initdeclor-list decl.init fn-name acc)
   ;; TODO: Do we want function calls in statasserts to be part of our call
   ;;   graph?
   :statassert (call-graph-statassert decl.unwrap fn-name acc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines call-graph-stmts/block
  (define call-graph-stmt
    ((stmt stmtp)
     (fn-name identp)
     (acc ident-ident-option-set-mapp))
    :returns (call-graph ident-ident-option-set-mapp)
    (stmt-case
     stmt
     :labeled (call-graph-stmt stmt.stmt fn-name acc)
     :compound (call-graph-block-item-list stmt.items fn-name acc)
     :expr (call-graph-expr-option stmt.expr? fn-name acc)
     :if (call-graph-stmt
           stmt.then
           fn-name
           (call-graph-expr stmt.test fn-name acc))
     :ifelse (call-graph-stmt
               stmt.else
               fn-name
               (call-graph-stmt
                 stmt.then
                 fn-name
                 (call-graph-expr stmt.test fn-name acc)))
     :switch (call-graph-stmt
               stmt.body
               fn-name
               (call-graph-expr stmt.target fn-name acc))
     :while (call-graph-stmt
              stmt.body
              fn-name
              (call-graph-expr stmt.test fn-name acc))
     :dowhile (call-graph-expr
                stmt.test
                fn-name
                (call-graph-stmt stmt.body fn-name acc))
     :for-expr (call-graph-stmt
                 stmt.body
                 fn-name
                 (call-graph-expr-option
                   stmt.next
                   fn-name
                   (call-graph-expr-option
                     stmt.test
                     fn-name
                     (call-graph-expr-option
                       stmt.init
                       fn-name
                       acc))))
     :for-decl (call-graph-stmt
                 stmt.body
                 fn-name
                 (call-graph-expr-option
                   stmt.next
                   fn-name
                   (call-graph-expr-option
                     stmt.test
                     fn-name
                     (call-graph-decl
                       stmt.init
                       fn-name
                       acc))))
     ;; TODO: error on ambiguous constructs
     ;; :for-ambig
     :return (call-graph-expr-option stmt.expr? fn-name acc)
     :otherwise (ident-ident-option-set-map-fix acc))
    :measure (stmt-count stmt))

  (define call-graph-block-item
    ((item block-itemp)
     (fn-name identp)
     (acc ident-ident-option-set-mapp))
    :returns (call-graph ident-ident-option-set-mapp)
    (block-item-case
     item
     :decl (call-graph-decl item.unwrap fn-name acc)
     :stmt (call-graph-stmt item.unwrap fn-name acc)
     ;; TODO: error on ambiguous constructs
     :ambig (ident-ident-option-set-map-fix acc))
    :measure (block-item-count item))

  (define call-graph-block-item-list
    ((items block-item-listp)
     (fn-name identp)
     (acc ident-ident-option-set-mapp))
    :returns (call-graph ident-ident-option-set-mapp)
    (if (endp items)
        (ident-ident-option-set-map-fix acc)
      (call-graph-block-item-list
        (rest items)
        fn-name
        (call-graph-block-item (first items) fn-name acc)))
    :measure (block-item-list-count items))

   :hints (("Goal" :in-theory (enable o< o-finp)))
   :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define call-graph-fundef
  ((fundef fundefp)
   (acc ident-ident-option-set-mapp))
  :returns (call-graph ident-ident-option-set-mapp)
  (b* (((fundef fundef) fundef)
       ((declor fundef.declor) fundef.declor))
    (dirdeclor-case
      fundef.declor.decl
      :function-params (b* ((fn-name (dirdeclor-get-ident fundef.declor.decl.decl)))
                         (call-graph-stmt fundef.body fn-name acc))
      :function-names (b* ((fn-name (dirdeclor-get-ident fundef.declor.decl.decl)))
                         (call-graph-stmt fundef.body fn-name acc))
      :otherwise (ident-ident-option-set-map-fix acc))))

(define call-graph-extdecl
  ((extdecl extdeclp)
   (acc ident-ident-option-set-mapp))
  :returns (call-graph ident-ident-option-set-mapp)
  (extdecl-case
   extdecl
   :fundef (call-graph-fundef extdecl.unwrap acc)
   :decl (ident-ident-option-set-map-fix acc)))

(define call-graph-extdecl-list
  ((extdecls extdecl-listp)
   (acc ident-ident-option-set-mapp))
  :returns (call-graph ident-ident-option-set-mapp)
  (if (endp extdecls)
      (ident-ident-option-set-map-fix acc)
    (call-graph-extdecl-list
      (rest extdecls)
      (call-graph-extdecl (first extdecls)
                          acc))))

(define call-graph-transunit
  ((transunit transunitp))
  :returns (call-graph ident-ident-option-set-mapp)
  :short "Build a call graph corresponding to a translation unit."
  (b* (((transunit transunit) transunit))
    (call-graph-extdecl-list transunit.decls nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define call-graph-transitive-closure
  ((ident identp)
   (call-graph ident-ident-option-set-mapp))
  :returns (called ident-option-setp)
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
   ;; lexicographic, primarily measuring the difference in size of acc with
   ;; respect to the identifiers in the call graph (acc is a subset of the this
   ;; finite set of identifiers), and secondarily the decrease if ident?s.
   (define call-graph-transitive-closure0
     ((ident?s ident-option-setp)
      (call-graph ident-ident-option-set-mapp)
      (acc ident-option-setp)
      (steps :type (unsigned-byte 60)))
     :returns (called ident-option-setp)
     (b* (((when (or (int= 0 (mbe :logic (if (natp (acl2::the-fixnat steps))
                                             (acl2::the-fixnat steps)
                                           0)
                                  :exec (acl2::the-fixnat steps)))
                     (emptyp ident?s)))
           (ident-option-set-fix acc))
          (ident? (head ident?s))
          ((when (not ident?))
           (call-graph-transitive-closure0
             (tail ident?s)
             call-graph
             (insert nil acc)
             (- steps 1)))
          (lookup (omap::assoc ident? call-graph))
          (ident?s
            (if lookup
                (union (difference (cdr lookup) acc)
                       (tail ident?s))
              (tail ident?s)))
          (acc
            (if lookup
                (union (cdr lookup) acc)
              acc)))
       (call-graph-transitive-closure0
         ident?s
         call-graph
         acc
         (- steps 1)))
     :measure (nfix steps)
     :hints (("Goal" :in-theory (enable o< o-finp))))))

(define exists-call-pathp
  ((from identp)
   (to ident-optionp)
   (call-graph ident-ident-option-set-mapp))
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
  ((ident identp)
   (call-graph ident-ident-option-set-mapp))
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
  ((ident identp)
   (call-graph ident-ident-option-set-mapp))
  :short "Recognizes directly or mutually recursive functions."
  :long
  (xdoc::topstring
   (xdoc::p
     "This function checks whether @('ident') is in its own transitive
      closure. See @(tsee call-graph-transitive-closure) and (see
      call-graph)."))
  (exists-call-pathp ident ident call-graph))

(define uncertain-call-pathp
  ((ident identp)
   (call-graph ident-ident-option-set-mapp))
  :short "Recognizes functions which possess an unresolved function call path."
  :long
  (xdoc::topstring
   (xdoc::p
     "This function checks whether nil is in @('ident')'s transitive
      closure. See @(tsee call-graph-transitive-closure) and (see
      call-graph)."))
  (exists-call-pathp ident nil call-graph))
