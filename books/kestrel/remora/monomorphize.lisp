; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-trees")
(include-book "integer-lists")
(include-book "nat-lists")
(include-book "unique-names")
(include-book "variable-substitution-operations")
(include-book "utility-transforms")

(include-book "kestrel/fty/deffold-map" :dir :system)
(include-book "kestrel/fty/deffold-reduce" :dir :system)
(include-book "kestrel/fty/string-nat-map" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/alists/put-assoc-equal" :dir :system)

(include-book "portcullis")

(local (include-book "std/typed-lists/string-listp" :dir :system))
(local (include-book "std/omaps/top" :dir :system))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ monomorphize
  :parents (remora)
  :short "Monomorphize a Remora program by instantiating
          @(':cfun') and @(':ifun') definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Traverses a Remora program, replacing every @(':capp') call to a known
     @(':cfun') that carries non-empty ispace arguments with a plain @(':app')
     call to a freshly generated, fully-instantiated @(':fun') definition.
     The new function is built by binding the @(':cfun')'s ispace parameters to
     the evaluated nat values and partially evaluating dimensions throughout the
     type and body.")
   (xdoc::p
    "Index-function definitions are handled the same way: every @(':iappn')
     call to a known @(':ifun') with non-empty ispace arguments is replaced by
     a reference to a freshly generated, fully-instantiated @(':val') definition
     (an @(':ifun') abstracts only ispace parameters, so the instance has no
     value parameters and is a @(':val') rather than a @(':fun')).")
   (xdoc::p
    "The two main maps are:")
   (xdoc::ul
    (xdoc::li
     "@('fn-info-map'): a @(tsee fn-info-map), i.e. an alist from @(':cfun')
      and @(':ifun') name strings to @(tsee bind+bind-map) pairs, where the
      @('bind') component is the definition (:cfun or :ifun) and the
      @('bind-map') component (a @(tsee bind-map)) maps instance-name strings
      to the corresponding @(':fun') (for a @(':cfun')) or @(':val') (for an
      @(':ifun')) @(tsee bind) nodes.")
    (xdoc::li
     "@('dim-var-map'): a @(tsee acl2::string-nat-map), i.e. an omap from ispace
      dimension-variable name strings to their nat values, used to evaluate
      @(':dim') ispace arguments."))
   (xdoc::p
    "A termination fuel parameter bounds how many levels of nested cfun
     instantiation are performed. The fuel should never reach zero, so it is an
     errorif it does. The top-level entry point @(tsee monomorphize-top-expr)
     supplies @('(* 10 (expr-count expr))') as the initial fuel: a margin
     above the expression size, since each cfun instantiation grows the tree
     (the instance body is spliced in) and so the fuel must exceed the original
     size for nested instantiation to terminate without reunning out of fuel."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Fixtypes for the maps used to accumulate cfun/instance and ifun/instance information.

(fty::defalist bind-map
  :short "Fixtype of alists from instance-name strings to @(tsee bind) nodes."
  :key-type string
  :val-type bind
  :pred bind-mapp
  :true-listp t)

(fty::defprod bind+bind-map
  :short "Fixtype of pairs consisting of a @(tsee bind) and a @(tsee bind-map)."
  ((bind bind)
   (bind-map bind-map))
  :pred bind+bind-map-p)

(fty::defalist fn-info-map
  :short "Fixtype of alists from @(':cfun') name strings to
          @(tsee bind+bind-map) pairs."
  :key-type string
  :val-type bind+bind-map
  :pred fn-info-mapp
  :true-listp t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Map from type-variable name strings to types, used to resolve type arguments.
; We use the library @(tsee string-type-map) omap so that the type-variable
; substitution operations from @(see variable-substitution-operations) can be
; applied directly to the type arguments (see the @(':capp') case below).

(define extend-type-var-map ((tvars type-var-listp)
                             (tys type-listp)
                             (type-map string-type-mapp))
  :returns (new-type-map string-type-mapp)
  :short "Extend @('type-map') with @('tvars[i] -> tys[i]') for each index."
  (if (or (endp tvars) (endp tys))
      (string-type-map-fix type-map)
    (b* ((name (type-var->name (car tvars)))
         (ty   (type-fix (car tys))))
      (extend-type-var-map (cdr tvars) (cdr tys)
                           (omap::update name ty
                                         (string-type-map-fix type-map))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Logic-mode helpers for instance-name construction.

; SHORT-NAME-FOR-TYPE follows type-var bindings through TYPE-MAP, dropping each
; binding it resolves; termination follows because deleting a present key from
; an omap strictly shrinks its size (omap::size-of-delete-when-assoc-linear).

(define short-name-for-type ((ty typep) (type-map string-type-mapp))
  :returns (short-nm stringp)
  :measure (omap::size (string-type-map-fix type-map))
  (type-case ty
     :base (base-type-case ty.type
             :bool  "b"
             :int   "i"
             :float "f")
     :var (b* ((type-map (string-type-map-fix type-map))
               (name (type-var->name ty.var))
               (v-ty-pr (omap::assoc name type-map))
               ((unless v-ty-pr) "unbound"))
            (short-name-for-type (cdr v-ty-pr)
                                 (omap::delete name type-map)))
     :otherwise "nyi"))

(define name-for-type-list ((tys type-listp) (type-map string-type-mapp))
  :returns (ty-nms string-listp)
  (if (endp tys)
      nil
    (cons (short-name-for-type (car tys) type-map)
          (name-for-type-list (cdr tys) type-map))))

(define string-list-dash-suffix ((strs string-listp))
  :returns (suffix stringp :hyp :guard)
  :short "Build a dash-separated suffix from a list of strs, e.g. @('\"-f-i\"')."
  (if (endp strs)
      ""
    (if (endp (cdr strs))
        (car strs)
      (str::cat (car strs) "-"
                (string-list-dash-suffix (cdr strs))))))

(define nat-list-dash-suffix ((nats nat-listp))
  :returns (suffix stringp)
  :short "Build a dash-separated suffix from a list of nats, e.g. @('\"-5-3\"')."
  (if (endp nats)
      ""
    (if (endp (cdr nats))
        (str::nat-to-dec-string (nfix (car nats)))
      (str::cat (str::nat-to-dec-string (nfix (car nats))) "-"
                (nat-list-dash-suffix (cdr nats))))))

(define cfun-inst-name ((base stringp) (strs string-listp) (nats nat-listp))
  :returns (name stringp)
  :short "Form the monomorphized instance name @('base-n1-n2-...')."
  (b* ((strs-suffix (string-list-dash-suffix strs))
       (ints-suffix (nat-list-dash-suffix nats)))
    (if (null strs)
        (str::cat base "/" ints-suffix)
      (if (null nats)
          (str::cat base "/" strs-suffix)
        (str::cat base "/" strs-suffix "/" ints-suffix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Extend dim-var-map by pairing up ispace vars with nat values.  We use the
; library acl2::string-nat-map omap so that this map is handled the same way
; as the string-type-map used for type arguments.

(define extend-ispace-val-map ((ivars ispace-var-listp)
                               (nats nat-listp)
                               (dim-var-map acl2::string-nat-mapp))
  :returns (new-dim-var-map acl2::string-nat-mapp)
  :short "Extend @('dim-var-map') with @('ivars[i] -> nats[i]') for each index."
  (if (or (endp ivars) (endp nats))
      (acl2::string-nat-map-fix dim-var-map)
    (b* ((name (ispace-var->name (car ivars)))
         (val  (nfix (car nats))))
      (extend-ispace-val-map (cdr ivars) (cdr nats)
                             (omap::update name val
                                           (acl2::string-nat-map-fix dim-var-map))))))

; Disable the tau system to speed up certification (matching the house style of
; the sibling abstract-syntax books, which call (acl2::controlled-configuration)).
(local (in-theory (disable (:e tau-system))))

; With the tau system disabled, the guard proofs that do ASSOC-EQUAL / STRIP-CDRS
; on these alists need the recognizer-implies-alistp facts that tau would
; otherwise supply.

(local
 (defthm alistp-when-bind-mapp-rw
   (implies (bind-mapp x) (alistp x))
   :hints (("Goal" :in-theory (enable bind-mapp)))))

(local
 (defthm alistp-when-fn-info-mapp-rw
   (implies (fn-info-mapp x) (alistp x))
   :hints (("Goal" :in-theory (enable fn-info-mapp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Collect, via a reducing fold, the variable and constant leaf dims occurring in
; an ispace tree; eval-iargs then evaluates each leaf dim to a nat.  Shape
; variables are reified as @(':var') dims so they are handled uniformly.

(fty::deffold-reduce leaf-dims
  :short "Collect the variable and constant leaf dims occurring in an ispace tree."
  :types (dims
          shapes/ispaces)
  :result dim-listp
  :default nil
  :combine append
  :override
  ((dim :var   (list (dim-fix dim)))
   (dim :const (list (dim-fix dim)))
   (shape :var (list (dim-var (shape-var->name shape)))))
  :name ast-leaf-dims)

(define eval-var-nat ((name stringp) (dim-var-map acl2::string-nat-mapp))
  :returns (mv (err booleanp) (val natp))
  :short "Look up @('name') in @('dim-var-map'); fail if it is absent."
  (b* ((pair (omap::assoc (str-fix name) (acl2::string-nat-map-fix dim-var-map)))
       ((unless pair) (mv t 0)))
    (mv nil (nfix (cdr pair)))))

(define eval-leaf-dim ((d dimp) (dim-var-map acl2::string-nat-mapp))
  ; tau (disabled book-wide) closes the natp return type via eval-var-nat.
  :returns (mv (err booleanp)
               (val natp :hints (("Goal" :in-theory (enable (:e tau-system))))))
  :short "Evaluate a collected leaf dim to a nat."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @(':var') dim is evaluated through @('dim-var-map'), failing if it is
     absent; a @(':const') dim yields its value.  Other dims do not occur among
     the collected leaves, so they are treated as an error."))
  (dim-case d
    :var   (eval-var-nat d.name dim-var-map)
    :const (mv nil d.val)
    :otherwise (mv t 0)))

(define eval-leaf-dims ((ds dim-listp) (dim-var-map acl2::string-nat-mapp))
  :returns (mv (err booleanp) (nats nat-listp))
  :short "Evaluate each collected leaf dim to a nat; fail if any does."
  (b* (((when (endp ds)) (mv nil nil))
       ((mv err n)  (eval-leaf-dim (car ds) dim-var-map))
       ((when err)  (mv t nil))
       ((mv err ns) (eval-leaf-dims (cdr ds) dim-var-map))
       ((when err)  (mv t nil)))
    (mv nil (cons n ns))))

(define eval-iargs ((isps ispace-listp) (dim-var-map acl2::string-nat-mapp))
  :returns (mv (err booleanp) (nats nat-listp))
  :short "Evaluate every variable or dim occurring in an ispace-list to a nat."
  :long
  (xdoc::topstring
   (xdoc::p
    "Traverses @('isps') and all its sub-trees via @(tsee ispace-list-leaf-dims),
     collecting each variable and constant leaf dim in left-to-right order, then
     evaluates each one: a variable through @('dim-var-map'), a constant to its
     value.  Returns @('(mv t nil)') if any variable was missing, otherwise
     @('(mv nil nats)')."))
  (eval-leaf-dims (ispace-list-leaf-dims isps) dim-var-map))


; Fold: substitute dimension variables with their nat values, constant-fold
; arithmetic operators when all sub-dimensions become :const, and propagate this
; through shapes, ispaces, types, and the full expression/atom/bind hierarchy.
; Because the @(tsee dims) clique is included in the fold, every embedded dim is
; visited automatically; only the four arithmetic dim cases need overrides.

(fty::deffold-map partial-eval-dims
  :short "Partially evaluate dimensions throughout Remora ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "Every @(':var') dim whose name appears in @('dim-var-map') is replaced by the
     corresponding @(':const') dim.  After substitution, @(':add') and @(':mul')
     dims whose sub-dimensions are all @(':const') are reduced to a single
     @(':const').  @(':sub') is reduced likewise, but only when the result is
     non-negative (natural).  These transformations are applied to every dim
     occurring anywhere in the traversed ASTs (shapes, ispaces, types, and
     expressions); all other sub-trees are rebuilt recursively unchanged."))
  :types (dims
          shapes/ispaces
          ispace-list-option
          types
          type-option
          type-list-option
          var+type?
          var+type?-list
          exprs/atoms/binds)
  :extra-args ((dim-var-map acl2::string-nat-mapp))
  :override
  ((dim :var (b* ((dim-var-map (acl2::string-nat-map-fix dim-var-map))
                  (pair (omap::assoc dim.name dim-var-map))
                  ((unless pair) (dim-var dim.name)))
               (dim-const (nfix (cdr pair)))))
   (dim :add (b* ((new-dims (dim-list-partial-eval-dims dim.dims dim-var-map))
                  ((unless (dim-list-case-const new-dims)) (dim-add new-dims)))
               (dim-const (nat-list-sum (dim-const-list->val new-dims)))))
   (dim :mul (b* ((new-dims (dim-list-partial-eval-dims dim.dims dim-var-map))
                  ((unless (dim-list-case-const new-dims)) (dim-mul new-dims)))
               (dim-const (nat-list-product (dim-const-list->val new-dims)))))
   (dim :sub (b* ((new-dims (dim-list-partial-eval-dims dim.dims dim-var-map))
                  ((unless (and (consp new-dims)
                                (dim-list-case-const new-dims)))
                   (dim-sub new-dims))
                  (result (nat-list-subtraction (dim-const-list->val new-dims)))
                  ((unless (natp result)) (dim-sub new-dims)))
               (dim-const (nfix result)))))
  :name ast-partial-eval-dims)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Type-variable substitution is provided by the deffold-map SUBST-TYPE-VARS in
; variable-substitution-operations.lisp, which generates TYPE-SUBST-TYPE-VARS,
; EXPR-SUBST-TYPE-VARS, etc.  Those operations take two string-type-map
; substitutions, one for atom-kind and one for array-kind type variables; the
; :capp case below passes the same name->type map (built by EXTEND-TYPE-VAR-MAP)
; for both, since each instantiated tparam name has a single kind.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The @(':let') normalization transforms used below (SINGLETONIZE-LET and
; FLATTEN-LET, with helpers NEST-LET-BINDS and COALESCE-LET) live in
; utility-transforms.lisp, included above.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lemmas relating fn-info-mapp lookups to the bind+bind-map value type;
; needed for guard verification of the assoc-equal-based lookups below.

(local
 (defthm consp-of-assoc-equal-when-fn-info-mapp
   (implies (and (fn-info-mapp x) (assoc-equal k x))
            (consp (assoc-equal k x)))))

(local
 (defthm bind+bind-map-p-of-cdr-of-assoc-equal-when-fn-info-mapp
   (implies (and (fn-info-mapp x) (assoc-equal k x))
            (bind+bind-map-p (cdr (assoc-equal k x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Helper: update fn-info-map entry for cfun-name to include a new instance.

(define fn-info-map-add-instance ((fn-info-map fn-info-mapp)
                                  (cfun-name stringp)
                                  (inst-name stringp)
                                  (new-bind bindp))
  :returns (new-fn-info-map fn-info-mapp :hyp :guard)
  :short "Replace the instance-alist entry for @('cfun-name') with one that
          prepends @('(inst-name . new-bind)')."
  (b* ((entry (assoc-equal cfun-name fn-info-map))
       ((unless entry) fn-info-map)
       (pair          (cdr entry))
       (cfun-b        (bind+bind-map->bind pair))
       (new-instances (cons (cons inst-name new-bind)
                            (bind+bind-map->bind-map pair))))
    (put-assoc-equal cfun-name (bind+bind-map cfun-b new-instances) fn-info-map)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Helper: look up a fun name in the fn-info-map and return its instance
; binds (the range of the bind-map), or nil if the name is not present.

(define c-or-i-fun-instance-binds ((fn-info-map fn-info-mapp) (fun-name stringp))
  :returns (binds bind-listp :hyp :guard)
  :prepwork
  ((local
    (defthm bind-listp-of-strip-cdrs-when-bind-mapp
      (implies (bind-mapp x)
               (bind-listp (strip-cdrs x)))
      :hints (("Goal" :in-theory (enable strip-cdrs))))))
  :short "Return the list of instance @(tsee bind) nodes recorded for @('fun-name'),
          or @('nil') if @('fun-name') is not in @('fn-info-map')."
  (b* ((entry (assoc-equal fun-name fn-info-map))
       ((unless entry) nil)
       (pair     (cdr entry))
       (bind-map (bind+bind-map->bind-map pair)))
    (strip-cdrs bind-map)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Main monomorphization traversal.
;
; The traversal functions (MONO-EXPR and friends) take:
;   fuel        : natp                  — limits depth of cfun/ifun-body recursion
;   x           : AST node              — the node being processed
;   fn-info-map : fn-info-mapp          — accumulated cfun/ifun instance info
;   dim-var-map : acl2::string-nat-mapp — ispace dimension-variable -> nat bindings
;   type-map    : string-type-mapp      — type-variable -> type bindings
; and return (mv err fn-info-map new-x).
;
; The two instance generators MONO-CFUN-INSTANCE / MONO-IFUN-INSTANCE are part of
; the same clique (they monomorphize a cfun/ifun body); they return (mv err
; fn-info-map) and do the only non-structural, fuel-decrementing recursion.
;
; The :measure (two-nats-measure fuel (count x)) lets ACL2 verify termination:
;   - structural recursive calls keep fuel fixed and decrease the count;
;   - the instance generators have measure (two-nats-measure fuel 0) and call
;     MONO-EXPR on the instance body with fuel decremented.

; For the :let case with a single bind, MONO-EXPR calls MONO-BIND on the car of
; the binds list.  Its measure is (two-nats-measure fuel (bind-count ...)), so
; termination needs (bind-count (car (expr-let->binds x))) < (expr-count x).
; The :let test below is written as (and (consp x.binds) (endp (cdr x.binds)))
; rather than (equal (len x.binds) 1) so that (consp (expr-let->binds x)) appears
; directly in the measure ruler; this lets the measure prover chain the linear
; rules BIND-COUNT-OF-CAR and BIND-LIST-COUNT-OF-EXPR-LET->BINDS on its own.

(defines monomorphize-impl
  :verify-guards :after-returns
  :ruler-extenders :all

  (define mono-expr ((fuel natp) (x exprp) (fn-info-map fn-info-mapp) (dim-var-map acl2::string-nat-mapp) (type-map string-type-mapp))
    :short "Monomorphize an expression."
    :returns (mv err (new-fn-info-map fn-info-mapp :hyp :guard) (new-expr exprp :hyp :guard))
    :measure (two-nats-measure fuel (expr-count x))
    (expr-case x
      :var
      (mv nil fn-info-map (expr-fix x))

      :atom (b* (((mv err fn-info-map new-a) (mono-atom fuel x.atom fn-info-map dim-var-map type-map)))
              (mv err fn-info-map (expr-atom new-a)))

      :array (b* (((mv err fn-info-map new-atoms)
                   (mono-atom-list fuel x.atoms fn-info-map dim-var-map type-map)))
               (mv err fn-info-map (expr-array x.dims new-atoms)))

      :array-empty (mv nil fn-info-map (expr-fix x))

       :frame (b* (((mv err fn-info-map new-es)
                   (mono-expr-list fuel x.exprs fn-info-map dim-var-map type-map)))
               (mv err fn-info-map (expr-frame x.dims new-es)))

      :frame-empty (mv nil fn-info-map (expr-fix x))

      :string (mv nil fn-info-map (expr-fix x))

      :app (b* (((mv err fn-info-map new-fun)
                 (mono-expr fuel x.fun fn-info-map dim-var-map type-map))
                ((when err) (mv err fn-info-map (expr-app new-fun x.args)))
                ((mv err fn-info-map new-args)
                 (mono-expr-list fuel x.args fn-info-map dim-var-map type-map)))
             (mv err fn-info-map (expr-app new-fun new-args)))

      :tappn (b* (((mv err fn-info-map new-fun)
                   (mono-expr fuel x.fun fn-info-map dim-var-map type-map)))
               (mv err fn-info-map (expr-tappn new-fun x.args)))

      :iapp (b* (((mv err fn-info-map new-fun)
                  (mono-expr fuel x.fun fn-info-map dim-var-map type-map)))
              (mv err fn-info-map (expr-iapp new-fun x.arg)))

      :iappn
      (b* (((mv err fn-info-map new-fun)
            (mono-expr fuel x.fun fn-info-map dim-var-map type-map))
           ((when err) (mv err fn-info-map (expr-iappn new-fun x.args)))
           (fun new-fun)
           ; Only monomorphize an :iappn of a known :ifun :var to non-empty ispace args.
           ((mv err fn-info-map new-expr)
            (if (not (consp x.args))
                (mv nil fn-info-map (expr-iappn fun x.args))
              (expr-case fun
                :var (b* ((ifun-name fun.name)
                          ((unless (assoc-equal ifun-name fn-info-map))
                           (mv nil fn-info-map (expr-iappn fun x.args)))
                          ((mv eval-err nats) (eval-iargs x.args dim-var-map))
                          ((when eval-err)
                           (mv :ispace-eval-error fn-info-map (expr-iappn fun x.args)))
                          (inst-name (cfun-inst-name ifun-name nil nats))
                          ((mv err fn-info-map)
                           (mono-ifun-instance fuel ifun-name inst-name nats
                                               fn-info-map dim-var-map type-map))
                          ((when err) (mv err fn-info-map (expr-iappn fun x.args))))
                       (mv nil fn-info-map (expr-var inst-name)))
                :otherwise (mv nil fn-info-map (expr-iappn fun x.args)))))
           ((when err) (mv err fn-info-map new-expr)))
        (mv nil fn-info-map new-expr))

      :capp
      (b* (((mv err fn-info-map new-fun)
            (mono-expr fuel x.fun fn-info-map dim-var-map type-map))
           ((when err) (mv err fn-info-map (expr-capp new-fun x.targs x.iargs x.args)))
           ((mv err fn-info-map new-args)
            (mono-expr-list fuel x.args fn-info-map dim-var-map type-map))
           ((when err) (mv err fn-info-map (expr-capp new-fun x.targs x.iargs new-args)))
           (fun new-fun)
           ; Only monomorphize a :capp of a :var to non-empty :some iargs.
           ((mv err fn-info-map new-expr)
            (ispace-list-option-case x.iargs
              :none (mv nil fn-info-map (expr-capp fun x.targs x.iargs new-args))
              :some (if (not (consp x.iargs.val))
                        (mv nil fn-info-map (expr-capp fun x.targs x.iargs new-args))
                      (expr-case fun
                        :var (b* ((cfun-name fun.name)
                                  ((mv eval-err nats) (eval-iargs x.iargs.val dim-var-map))
                                  ((when eval-err)
                                   (mv :ispace-eval-error fn-info-map
                                       (expr-capp fun x.targs x.iargs new-args)))
                                  (tnames    (type-list-option-case x.targs
                                               :some (name-for-type-list x.targs.val type-map)
                                               :none nil))
                                  (inst-name (cfun-inst-name cfun-name tnames nats))
                                  (targ-tys  (type-list-option-case x.targs
                                               :some x.targs.val :none nil))
                                  (mono-expr (expr-app (expr-var inst-name) new-args))
                                  ; An unknown cfun is built-in: emit the same instance call
                                  ; as for a known cfun, but do not build/register an instance.
                                  ((unless (assoc-equal cfun-name fn-info-map))
                                   (mv nil fn-info-map mono-expr))
                                  ((mv err fn-info-map)
                                   (mono-cfun-instance fuel cfun-name inst-name nats targ-tys
                                                       fn-info-map dim-var-map type-map))
                                  ((when err)
                                   (mv err fn-info-map (expr-capp fun x.targs x.iargs new-args))))
                                (mv nil fn-info-map mono-expr))
                        :otherwise (mv nil fn-info-map (expr-capp fun x.targs x.iargs new-args))))))
           ((when err) (mv err fn-info-map new-expr)))
        (mv nil fn-info-map new-expr))

      :unbox (b* (((mv err fn-info-map new-target)
                   (mono-expr fuel x.target fn-info-map dim-var-map type-map))
                  ((when err) (mv err fn-info-map (expr-unbox x.ispaces x.var new-target x.body x.type?)))
                  ((mv err fn-info-map new-body) (mono-expr fuel x.body fn-info-map dim-var-map type-map)))
               (mv err fn-info-map (expr-unbox x.ispaces x.var new-target new-body x.type?)))

      :bracket (b* (((mv err fn-info-map new-es)
                     (mono-expr-list fuel x.exprs fn-info-map dim-var-map type-map)))
                 (mv err fn-info-map (expr-bracket new-es)))

      :let (if (and (consp x.binds) (endp (cdr x.binds)))
               ;; Lets should have been normalized before calling this to have obly one bind
               (b* (((mv err fn-info-map new-bind)
                     (mono-bind fuel (car x.binds)
                                fn-info-map dim-var-map type-map))
                    ((when err) (mv err fn-info-map (expr-let (list new-bind) x.body)))
                    ((mv err fn-info-map new-body)
                     (mono-expr fuel x.body fn-info-map dim-var-map type-map))
                    ;; For a :cfun/:ifun bind, splice in the instances generated for it
                    ;; (replacing the now-unused definition); otherwise keep the bind.
                    (new-binds (bind-case new-bind
                                          :cfun (c-or-i-fun-instance-binds fn-info-map new-bind.var)
                                          :ifun (c-or-i-fun-instance-binds fn-info-map new-bind.var)
                                          :otherwise nil)))
                 (mv err fn-info-map
                     (expr-let (if (consp new-binds) new-binds (list new-bind))
                               new-body)))
             (mv :let-not-normalized fn-info-map x))))

  (define mono-expr-list ((fuel natp) (x expr-listp)
                          (fn-info-map fn-info-mapp) (dim-var-map acl2::string-nat-mapp) (type-map string-type-mapp))
    :short "Monomorphize a list of expressions."
    :returns (mv err (new-fn-info-map fn-info-mapp :hyp :guard) (new-exprs expr-listp :hyp :guard))
    :measure (two-nats-measure fuel (expr-list-count x))
    (if (endp x)
        (mv nil fn-info-map nil)
      (b* (((mv err fn-info-map new-e)
            (mono-expr fuel (car x) fn-info-map dim-var-map type-map))
           ((when err) (mv err fn-info-map (list* new-e (expr-list-fix (cdr x)))))
           ((mv err fn-info-map new-rest)
            (mono-expr-list fuel (cdr x) fn-info-map dim-var-map type-map)))
        (mv err fn-info-map (cons new-e new-rest)))))

  (define mono-atom ((fuel natp) (x atomp) (fn-info-map fn-info-mapp) (dim-var-map acl2::string-nat-mapp) (type-map string-type-mapp))
    :short "Monomorphize an atom."
    :returns (mv err (new-fn-info-map fn-info-mapp :hyp :guard) (new-atom atomp :hyp :guard))
    :measure (two-nats-measure fuel (atom-count x))
    (atom-case x
      :base    (mv nil fn-info-map (atom-fix x))
      :lambda  (b* (((mv err fn-info-map new-body)
                     (mono-expr fuel x.body fn-info-map dim-var-map type-map)))
                 (mv err fn-info-map (atom-lambda x.params new-body x.type?)))
      :tlambda (b* (((mv err fn-info-map new-body)
                     (mono-expr fuel x.body fn-info-map dim-var-map type-map)))
                 (mv err fn-info-map (atom-tlambda x.params new-body)))
      :ilambda (b* (((mv err fn-info-map new-body)
                     (mono-expr fuel x.body fn-info-map dim-var-map type-map)))
                 (mv err fn-info-map (atom-ilambda x.param new-body)))
      :ilambdan (b* (((mv err fn-info-map new-body)
                      (mono-expr fuel x.body fn-info-map dim-var-map type-map)))
                  (mv err fn-info-map (atom-ilambdan x.params new-body)))
      :box     (b* (((mv err fn-info-map new-array)
                     (mono-expr fuel x.array fn-info-map dim-var-map type-map)))
                 (mv err fn-info-map (atom-box x.ispaces new-array x.type)))))

  (define mono-atom-list ((fuel natp) (x atom-listp)
                          (fn-info-map fn-info-mapp) (dim-var-map acl2::string-nat-mapp) (type-map string-type-mapp))
    :short "Monomorphize a list of atoms."
    :returns (mv err (new-fn-info-map fn-info-mapp :hyp :guard) (new-atoms atom-listp :hyp :guard))
    :measure (two-nats-measure fuel (atom-list-count x))
    (if (endp x)
        (mv nil fn-info-map nil)
      (b* (((mv err fn-info-map new-a)
            (mono-atom fuel (car x) fn-info-map dim-var-map type-map))
           ((when err) (mv err fn-info-map (list* new-a (atom-list-fix (cdr x)))))
           ((mv err fn-info-map new-rest)
            (mono-atom-list fuel (cdr x) fn-info-map dim-var-map type-map)))
        (mv err fn-info-map (cons new-a new-rest)))))

  (define mono-bind ((fuel natp) (x bindp) (fn-info-map fn-info-mapp) (dim-var-map acl2::string-nat-mapp) (type-map string-type-mapp))
    :short "Monomorphize a binding, registering @(':cfun') and @(':ifun')
            definitions in fn-info-map."
    :returns (mv err (new-fn-info-map fn-info-mapp :hyp :guard) (new-bind bindp :hyp :guard))
    :long
    (xdoc::topstring
     (xdoc::p
      "For a @(':cfun') (respectively @(':ifun')) bind, the entry mapping
       @('name') to a @(tsee bind+bind-map) pair with an empty @('bind-map') is
       added to @('fn-info-map') and the bind is returned unchanged: the body is
       @('not') monomorphized here.  The body is processed later, at the
       @(':capp') (respectively @(':iappn')) call site that instantiates it, with
       the fuel decremented.  The registration done here lets those call sites,
       and subsequent @(':capp')/@(':iappn') expressions in the enclosing
       @(':let') body, look up the name."))
    :measure (two-nats-measure fuel (bind-count x))
    (bind-case x
      :ispace (mv nil fn-info-map (bind-fix x))
      :type   (mv nil fn-info-map (bind-fix x))
      :val    (b* (((mv err fn-info-map new-expr)
                    (mono-expr fuel x.expr fn-info-map dim-var-map type-map)))
                (mv err fn-info-map (bind-val x.var x.type? new-expr)))
      :fun    (b* (((mv err fn-info-map new-expr)
                    (mono-expr fuel x.expr fn-info-map dim-var-map type-map)))
                (mv err fn-info-map (bind-fun x.var x.params x.type? new-expr)))
      :tfun   (b* (((mv err fn-info-map new-expr)
                    (mono-expr fuel x.expr fn-info-map dim-var-map type-map)))
                (mv err fn-info-map (bind-tfun x.var x.params x.type? new-expr)))
      :ifun   (b* (; Register ifun but don't process body because we are only interested in the mono versions
                   (fn-info-map (acons x.var (bind+bind-map (bind-fix x) nil) fn-info-map))
                  )
                (mv nil fn-info-map (bind-fix x)))
      :cfun   (b* (; Register cfun but don't process body because we are only interested in the mono versions
                   (fn-info-map (acons x.var (bind+bind-map (bind-fix x) nil) fn-info-map))
                  )
                (mv nil fn-info-map (bind-fix x)))))

  ; Instance generators for the :capp / :iappn cases of mono-expr.  Each builds
  ; the monomorphized instance body by recursing with the fuel decremented.
  ; It is and error for fuel to be exhausted.

  (define mono-cfun-instance ((fuel natp) (cfun-name stringp) (inst-name stringp)
                              (nats nat-listp) (targ-tys type-listp)
                              (fn-info-map fn-info-mapp)
                              (dim-var-map acl2::string-nat-mapp)
                              (type-map string-type-mapp))
    :short "Generate and register the monomorphized @(':fun') instance for a
            @(':capp') call to @('cfun-name'), unless it already exists."
    :long
    (xdoc::topstring
     (xdoc::p
      "@('cfun-name') is assumed to be registered in @('fn-info-map').  If
       @('inst-name') is already among its instances, this is a no-op.
       Otherwise the @(':cfun')'s ispace parameters are bound to @('nats') and
       its type parameters to @('targ-tys'); its value parameters, return type,
       and body are partially evaluated and type-substituted accordingly; and
       the resulting @(':fun') @(tsee bind) is registered under @('cfun-name').
       Fails with @(':bad-cfun-entry') if @('cfun-name') is not bound to a
       @(':cfun')."))
    :returns (mv err (new-fn-info-map fn-info-mapp :hyp :guard))
    :measure (two-nats-measure fuel 0)
    (b* ((entry (assoc-equal cfun-name fn-info-map))
         ((unless entry) (mv nil fn-info-map))
         (pair       (cdr entry))
         (cfun-bind  (bind+bind-map->bind pair))
         (inst-alist (bind+bind-map->bind-map pair))
         ((when (assoc-equal inst-name inst-alist)) (mv nil fn-info-map)))
      (bind-case cfun-bind
        :cfun
        (b* ((iparams (ispace-var-list-option-case cfun-bind.iparams?
                        :some cfun-bind.iparams?.val :none nil))
             (ext-dim-var-map (extend-ispace-val-map iparams nats dim-var-map))
             (tparams (type-var-list-option-case cfun-bind.tparams?
                        :some cfun-bind.tparams?.val :none nil))
             (ext-type-map (extend-type-var-map tparams targ-tys type-map))
             (new-params (var+type?-list-subst-type-vars
                          (var+type?-list-partial-eval-dims cfun-bind.params ext-dim-var-map)
                          ext-type-map ext-type-map))
             (new-type (type-subst-type-vars
                        (type-partial-eval-dims cfun-bind.type ext-dim-var-map)
                        ext-type-map ext-type-map))
             (body-in (expr-subst-type-vars
                       (expr-partial-eval-dims cfun-bind.expr ext-dim-var-map)
                       ext-type-map ext-type-map))
             ; Monomorphize the cfun body (with decremented fuel; error on exhaustion).
             ((mv body-err fn-info-map new-body)
              (if (posp fuel)
                  (mono-expr (1- fuel) body-in fn-info-map ext-dim-var-map ext-type-map)
                (mv :fuel-exhausted fn-info-map body-in)))
             ((when body-err) (mv body-err fn-info-map))
             (new-fun-bind (bind-fun inst-name new-params new-type new-body)))
          (mv nil (fn-info-map-add-instance fn-info-map cfun-name inst-name new-fun-bind)))
        :otherwise
        ; Not a :cfun under a cfun-name: malformed call; fail loudly.
        (mv :bad-cfun-entry fn-info-map))))

  (define mono-ifun-instance ((fuel natp) (ifun-name stringp) (inst-name stringp)
                              (nats nat-listp)
                              (fn-info-map fn-info-mapp)
                              (dim-var-map acl2::string-nat-mapp)
                              (type-map string-type-mapp))
    :short "Generate and register the monomorphized @(':val') instance for an
            @(':iappn') call to @('ifun-name'), unless it already exists."
    :long
    (xdoc::topstring
     (xdoc::p
      "Like @(tsee mono-cfun-instance), but for an @(':ifun'), which abstracts
       only ispace parameters: the instance is a @(':val') (no value parameters
       remain) rather than a @(':fun'), and only dimension substitution is
       applied.  Fails with @(':bad-ifun-entry') if @('ifun-name') is not bound
       to an @(':ifun')."))
    :returns (mv err (new-fn-info-map fn-info-mapp :hyp :guard))
    :measure (two-nats-measure fuel 0)
    (b* ((entry (assoc-equal ifun-name fn-info-map))
         ((unless entry) (mv nil fn-info-map))
         (pair       (cdr entry))
         (ifun-bind  (bind+bind-map->bind pair))
         (inst-alist (bind+bind-map->bind-map pair))
         ((when (assoc-equal inst-name inst-alist)) (mv nil fn-info-map)))
      (bind-case ifun-bind
        :ifun
        (b* ((ext-dim-var-map (extend-ispace-val-map ifun-bind.params nats dim-var-map))
             (new-type? (type-option-partial-eval-dims ifun-bind.type? ext-dim-var-map))
             (body-in (expr-partial-eval-dims ifun-bind.expr ext-dim-var-map))
             ((mv body-err fn-info-map new-body)
              (if (posp fuel)
                  (mono-expr (1- fuel) body-in fn-info-map ext-dim-var-map type-map)
                (mv :fuel-exhausted fn-info-map body-in)))
             ((when body-err) (mv body-err fn-info-map))
             (new-val-bind (bind-val inst-name new-type? new-body)))
          (mv nil (fn-info-map-add-instance fn-info-map ifun-name inst-name new-val-bind)))
        :otherwise
        ; Not an :ifun under an ifun-name: malformed call; fail loudly.
        (mv :bad-ifun-entry fn-info-map)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define monomorphize-top-expr ((expr exprp))
  :returns (mv err (fn-info-map fn-info-mapp) (new-expr exprp))
  :short "Monomorphize a standalone (top-level) Remora expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "Top-level entry point.  Returns @('(mv error fn-info-map new-expr)').
     The expression is first run through @(tsee expr-uniquify-names) so
     that every binder name (bind, or lambda/unbox/function parameter) is
     distinct: the traversal below substitutes ispace and type variables
     throughout whole subtrees, including into the as-yet-unprocessed bodies
     of nested @(':cfun')/@(':ifun') binds, so without this precondition a
     nested binder reusing an enclosing ispace or type variable's name could
     have its own parameter occurrences captured by the enclosing
     substitution.
     On success @('error') is @('nil') and @('fn-info-map') is a
     @(tsee fn-info-map) mapping each @(':cfun') and @(':ifun') name to a
     @(tsee bind+bind-map) pair, whose @('bind-map') component maps each
     instance-name string to the corresponding monomorphized @(':fun') (for a
     @(':cfun')) or @(':val') (for an @(':ifun')) @(tsee bind) node.
     On failure @('error') is a keyword: currently
     @(':ispace-eval-error') (an ispace argument failed to evaluate to a nat),
     or @(':bad-ifun-entry') / @(':bad-cfun-entry') (a name registered as an
     @(':ifun') / @(':cfun') resolved to a binding of the wrong kind)."))
  (b* ((expr (expr-uniquify-names expr))
       (expr (expr-singletonize-let expr))
       (fuel (expr-count expr))
       ((mv err fn-info-map new-expr)
        (mono-expr (* 10 fuel) expr nil nil nil)))
    (mv err fn-info-map (expr-flatten-let new-expr))))
