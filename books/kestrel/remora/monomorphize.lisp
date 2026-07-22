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
(include-book "kestrel/utilities/defopeners" :dir :system)
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
     @(':cfun') that carries non-empty ispace arguments with a plain @(':appn')
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
      and @(':ifun') name strings to lists of @(tsee inst-request)s, the
      instantiations requested by the @(':capp')/@(':iappn') call sites seen
      so far; the instances themselves are created when the definition's
      @(':let') is exited.")
    (xdoc::li
     "@('dim-var-map'): a @(tsee acl2::string-nat-map), i.e. an omap from ispace
      dimension-variable name strings to their nat values, used to evaluate
      @(':dim') ispace arguments."))
   (xdoc::p
    "Termination of the traversal does not need a fuel parameter: Remora
     @('let')s are non-recursive, so a @(':cfun')/@(':ifun') body can only
     call functions bound strictly before it.  The traversal makes this
     visible to the termination proof by passing the definitions in scope
     downward in an environment; call sites only record instantiation
     requests, and the instances are created when the definition's
     @(':let') is exited, whose environment is exactly the scope of the
     definition's body.  A @(':capp')/@(':iapp') of a known
     function that is not in scope (a recursive or forward reference) is
     rejected with the @(':out-of-scope-fun-reference') error."))
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

(fty::defprod inst-request
  :short "Fixtype of pending instantiation requests for a @(':cfun') or
          @(':ifun'): the instance name, the evaluated ispace arguments,
          and (for a @(':cfun')) the resolved type arguments."
  ((inst-name string)
   (nats nat-list)
   (targ-tys type-list))
  :pred inst-requestp)

(fty::deflist inst-request-list
  :short "Fixtype of lists of @(tsee inst-request)s."
  :elt-type inst-request
  :true-listp t
  :elementp-of-nil nil
  :pred inst-request-listp)

(fty::defalist fn-info-map
  :short "Fixtype of alists from @(':cfun') and @(':ifun') name strings to
          the @(tsee inst-request-list)s recorded at their call sites."
  :key-type string
  :val-type inst-request-list
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

; Lemmas relating fn-info-mapp lookups to the inst-request-list value type;
; needed for guard verification of the assoc-equal-based lookups below.

(local
 (defthm consp-of-assoc-equal-when-fn-info-mapp
   (implies (and (fn-info-mapp x) (assoc-equal k x))
            (consp (assoc-equal k x)))))

(local
 (defthm inst-request-listp-of-cdr-of-assoc-equal-when-fn-info-mapp
   (implies (fn-info-mapp x)
            (inst-request-listp (cdr (assoc-equal k x))))))

(local
 (defthm fn-info-mapp-of-remove1-assoc-equal
   (implies (fn-info-mapp x)
            (fn-info-mapp (remove1-assoc-equal k x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Helpers: record an instantiation request under a fun name in fn-info-map.

(define request-recorded-p ((inst-name stringp) (requests inst-request-listp))
  :returns (yes/no booleanp)
  :short "Whether a request with name @('inst-name') is in @('requests')."
  (cond ((endp requests) nil)
        ((equal (inst-request->inst-name (car requests)) inst-name) t)
        (t (request-recorded-p inst-name (cdr requests)))))

(define fn-info-map-add-request ((fn-info-map fn-info-mapp)
                                 (fun-name stringp)
                                 (request inst-requestp))
  :returns (new-fn-info-map fn-info-mapp :hyp :guard)
  :short "Record @('request') under @('fun-name'), unless an identically
          named instance has already been requested (or @('fun-name') is
          not registered)."
  (b* ((entry (assoc-equal fun-name fn-info-map))
       ((unless entry) fn-info-map)
       (requests (cdr entry))
       ((when (request-recorded-p (inst-request->inst-name request) requests))
        fn-info-map))
    (put-assoc-equal fun-name
                     (cons (inst-request-fix request) requests)
                     fn-info-map)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Termination infrastructure for the monomorphization traversal.
;
; The only non-structural recursion in the traversal is the instantiation of a
; cfun/ifun body, performed at the definition's :let when its scope is exited:
; the body comes from the definition bind, not from the expression being
; traversed.  Remora :let is non-recursive (see EVAL-BIND in evaluation.lisp:
; a bind's closure captures the environment before the bind itself is added),
; so a cfun/ifun body can only call cfuns/ifuns bound strictly before it, and
; instantiation depth is bounded by the scope chain.  The traversal passes the
; definitions in scope downward in an environment DEFS (a BIND-MAP from names
; to :cfun/:ifun binds, most recently bound first); the DEFS at a definition's
; :let is exactly the scope of the definition's body, so instance bodies are
; processed with the :let's own DEFS.
;
; The measure of a traversal function is
;   (two-nats-measure (+ (defs-weight defs) (<type>-cfun-count x))
;                     (<type>-count x))
; where <type>-CFUN-COUNT counts the :cfun/:ifun bind nodes in an AST (nested
; ones included) and DEFS-WEIGHT sums those counts over the definitions in
; DEFS:
;   - structural recursive calls keep DEFS fixed, do not increase the first
;     component, and decrease the count;
;   - extending DEFS at a :let of a :cfun/:ifun moves the bind's cfun-count
;     from the expression into DEFS-WEIGHT, keeping the first component
;     unchanged while the count decreases;
;   - the instance-creation fold at a :let (MONO-FUN-INSTANCES, measure
;     (two-nats-measure (+ (defs-weight defs) (bind-cfun-count bnd))
;                       (len requests))
;     with BND the :let's own definition bind) is below the :let either
;     because the :let body binds further cfuns/ifuns (its cfun-count makes
;     the :let's first component strictly larger) or, when the body binds
;     none, because the number of requests is then bounded by the body's
;     call sites; the latter bound is not visible to the measure prover, so
;     the fold is guarded by the test
;     (or (< 0 (cfun-count body)) (< (len requests) (expr-count x))),
;     whose failure arm is unreachable (see the :let case);
;   - entering an instance body from MONO-CFUN-INSTANCE / MONO-IFUN-INSTANCE
;     strictly decreases the first component: the body's cfun-count is one
;     less than the definition bind's own cfun-count.
; The substitutions applied to an instance body before recursion
; (PARTIAL-EVAL-DIMS and SUBST-TYPE-VARS) only rewrite dims and types, so
; they preserve cfun-count (flag-induction defthms below).

(fty::deffold-reduce cfun-count
  :short "Number of @(':cfun') and @(':ifun') definition nodes in an AST."
  :types (exprs/atoms/binds)
  :result natp
  :default 0
  :combine +
  :override
  ((bind :cfun (+ 1 (expr-cfun-count (bind-cfun->expr bind))))
   (bind :ifun (+ 1 (expr-cfun-count (bind-ifun->expr bind)))))
  :name ast-cfun-count)

; Opening rules for the CFUN-COUNT fold, one per branch of each function's
; case structure, conditioned on the node kind: the measure conjectures (and
; the preservation proofs below) see (EXPR-CFUN-COUNT X) with X's kind known
; from the governing tests, whereas the deffold-reduce-generated theorems are
; in constructor form (and there are none for the overridden :cfun/:ifun
; cases).

(local (acl2::defopeners expr-cfun-count))
(local (acl2::defopeners expr-list-cfun-count))
(local (acl2::defopeners atom-cfun-count))
(local (acl2::defopeners atom-list-cfun-count))
(local (acl2::defopeners bind-cfun-count))
(local (acl2::defopeners bind-list-cfun-count))

(local (in-theory (disable expr-cfun-count expr-list-cfun-count
                           atom-cfun-count atom-list-cfun-count
                           bind-cfun-count bind-list-cfun-count)))

; The dim and type-variable substitutions applied to an instance body before
; it is monomorphized only rewrite dims and types, never bind structure, so
; they preserve the cfun-count of the body.

(local
 (defthm-exprs/atoms/binds-partial-eval-dims-flag
   (defthm expr-cfun-count-of-expr-partial-eval-dims
     (equal (expr-cfun-count (expr-partial-eval-dims expr dim-var-map))
            (expr-cfun-count expr))
     :flag expr-partial-eval-dims)
   (defthm expr-list-cfun-count-of-expr-list-partial-eval-dims
     (equal (expr-list-cfun-count (expr-list-partial-eval-dims expr-list dim-var-map))
            (expr-list-cfun-count expr-list))
     :flag expr-list-partial-eval-dims)
   (defthm atom-cfun-count-of-atom-partial-eval-dims
     (equal (atom-cfun-count (atom-partial-eval-dims atom dim-var-map))
            (atom-cfun-count atom))
     :flag atom-partial-eval-dims)
   (defthm atom-list-cfun-count-of-atom-list-partial-eval-dims
     (equal (atom-list-cfun-count (atom-list-partial-eval-dims atom-list dim-var-map))
            (atom-list-cfun-count atom-list))
     :flag atom-list-partial-eval-dims)
   (defthm bind-cfun-count-of-bind-partial-eval-dims
     (equal (bind-cfun-count (bind-partial-eval-dims bind dim-var-map))
            (bind-cfun-count bind))
     :flag bind-partial-eval-dims)
   (defthm bind-list-cfun-count-of-bind-list-partial-eval-dims
     (equal (bind-list-cfun-count (bind-list-partial-eval-dims bind-list dim-var-map))
            (bind-list-cfun-count bind-list))
     :flag bind-list-partial-eval-dims)
   :hints (("Goal" :in-theory (acl2::enable* ast-cfun-count-rules
                                             expr-partial-eval-dims
                                             expr-list-partial-eval-dims
                                             atom-partial-eval-dims
                                             atom-list-partial-eval-dims
                                             bind-partial-eval-dims
                                             bind-list-partial-eval-dims)))))

(local
 (defthm-exprs/atoms/binds-subst-type-vars-flag
   (defthm expr-cfun-count-of-expr-subst-type-vars
     (equal (expr-cfun-count (expr-subst-type-vars expr atom-subst array-subst))
            (expr-cfun-count expr))
     :flag expr-subst-type-vars)
   (defthm expr-list-cfun-count-of-expr-list-subst-type-vars
     (equal (expr-list-cfun-count (expr-list-subst-type-vars expr-list atom-subst array-subst))
            (expr-list-cfun-count expr-list))
     :flag expr-list-subst-type-vars)
   (defthm atom-cfun-count-of-atom-subst-type-vars
     (equal (atom-cfun-count (atom-subst-type-vars atom atom-subst array-subst))
            (atom-cfun-count atom))
     :flag atom-subst-type-vars)
   (defthm atom-list-cfun-count-of-atom-list-subst-type-vars
     (equal (atom-list-cfun-count (atom-list-subst-type-vars atom-list atom-subst array-subst))
            (atom-list-cfun-count atom-list))
     :flag atom-list-subst-type-vars)
   (defthm bind-cfun-count-of-bind-subst-type-vars
     (equal (bind-cfun-count (bind-subst-type-vars bind atom-subst array-subst))
            (bind-cfun-count bind))
     :flag bind-subst-type-vars)
   (defthm bind-list-cfun-count-of-bind-list-subst-type-vars
     (equal (bind-list-cfun-count (bind-list-subst-type-vars bind-list atom-subst array-subst))
            (bind-list-cfun-count bind-list))
     :flag bind-list-subst-type-vars)
   :hints (("Goal" :in-theory (acl2::enable* ast-cfun-count-rules
                                             expr-subst-type-vars
                                             expr-list-subst-type-vars
                                             atom-subst-type-vars
                                             atom-list-subst-type-vars
                                             bind-subst-type-vars
                                             bind-list-subst-type-vars)))))

; Scope environment operations.

(define defs-weight ((defs bind-mapp))
  :returns (weight natp)
  :short "Sum of the @(tsee bind-cfun-count)s of the definitions in scope."
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable bind-mapp)))
  (if (endp defs)
      0
    (+ (bind-cfun-count (cdar defs))
       (defs-weight (cdr defs)))))

(local
 (defthm defs-weight-of-acons
   (equal (defs-weight (cons (cons name bind) defs))
          (+ (bind-cfun-count bind) (defs-weight defs)))
   :hints (("Goal" :expand ((defs-weight (cons (cons name bind) defs)))))))

(local
 (defthm expr-count-positive
   (< 0 (expr-count x))
   :rule-classes :linear
   :hints (("Goal" :expand ((expr-count x))))))

; Guard lemmas for looking up definition binds in the scope environment.

(local
 (defthm consp-of-assoc-equal-when-bind-mapp
   (implies (and (bind-mapp x) (assoc-equal k x))
            (consp (assoc-equal k x)))
   :hints (("Goal" :in-theory (enable bind-mapp)))))

(local
 (defthm bindp-of-cdr-of-assoc-equal-when-bind-mapp
   (implies (and (bind-mapp x) (assoc-equal k x))
            (bindp (cdr (assoc-equal k x))))
   :hints (("Goal" :in-theory (enable bind-mapp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Main monomorphization traversal.
;
; The traversal functions (MONO-EXPR and friends) take:
;   x           : AST node              — the node being processed
;   defs        : bind-mapp             — cfun/ifun definitions in scope,
;                                         most recently bound first
;   fn-info-map : fn-info-mapp          — accumulated cfun/ifun instance info
;   dim-var-map : acl2::string-nat-mapp — ispace dimension-variable -> nat bindings
;   type-map    : string-type-mapp      — type-variable -> type bindings
; and return (mv err fn-info-map new-x).
;
; DEFS flows downward only (it is never returned): it is extended at a :let
; that binds a :cfun/:ifun, enforcing Remora's non-recursive scoping.
; FN-INFO-MAP is threaded through the returns; it accumulates the
; instantiation REQUESTS recorded at :capp/:iappn call sites (evaluated
; ispace arguments and resolved type arguments, see INST-REQUEST).  Whether
; a call site is instantiated is decided by DEFS.  A name that is registered
; in FN-INFO-MAP but not in scope in DEFS is a recursive or forward
; reference, rejected with :OUT-OF-SCOPE-FUN-REFERENCE.
;
; The instances themselves are created when the definition's :let is exited:
; the :let case extracts the requests recorded for its bind, drops the
; registration, and calls the fold MONO-FUN-INSTANCES, which builds one
; instance bind per request via MONO-CFUN-INSTANCE / MONO-IFUN-INSTANCE;
; those generators do the only non-structural recursion, into the
; (substituted) definition body, in the scope DEFS of the :let itself.
;
; The :measure (two-nats-measure (+ (defs-weight defs) (cfun-count x)) (count x))
; lets ACL2 verify termination; see the termination infrastructure above for
; why each kind of recursive call decreases it.

; For the :let case with a single bind, MONO-EXPR calls MONO-BIND on the car of
; the binds list.  Its measure has second component (bind-count ...), so
; termination needs (bind-count (car (expr-let->binds x))) < (expr-count x).
; The :let test below is written as (and (consp x.binds) (endp (cdr x.binds)))
; rather than (equal (len x.binds) 1) so that (consp (expr-let->binds x)) appears
; directly in the measure ruler; this lets the measure prover chain the linear
; rules BIND-COUNT-OF-CAR and BIND-LIST-COUNT-OF-EXPR-LET->BINDS on its own.

(defines monomorphize-impl
  :verify-guards :after-returns
  :ruler-extenders :all

  (define mono-expr ((x exprp) (defs bind-mapp) (fn-info-map fn-info-mapp) (dim-var-map acl2::string-nat-mapp) (type-map string-type-mapp))
    :short "Monomorphize an expression."
    :returns (mv err (new-fn-info-map fn-info-mapp :hyp :guard) (new-expr exprp :hyp :guard))
    :measure (two-nats-measure (+ (defs-weight defs) (expr-cfun-count x))
                               (expr-count x))
    (expr-case x
      :var
      (mv nil fn-info-map (expr-fix x))

      :atom (b* (((mv err fn-info-map new-a) (mono-atom x.atom defs fn-info-map dim-var-map type-map)))
              (mv err fn-info-map (expr-atom new-a)))

      :array (b* (((mv err fn-info-map new-atoms)
                   (mono-atom-list x.atoms defs fn-info-map dim-var-map type-map)))
               (mv err fn-info-map (expr-array x.dims new-atoms)))

      :array-empty (mv nil fn-info-map (expr-fix x))

       :frame (b* (((mv err fn-info-map new-es)
                   (mono-expr-list x.exprs defs fn-info-map dim-var-map type-map)))
               (mv err fn-info-map (expr-frame x.dims new-es)))

      :frame-empty (mv nil fn-info-map (expr-fix x))

      :string (mv nil fn-info-map (expr-fix x))

      :app (b* (((mv err fn-info-map new-fun)
                 (mono-expr x.fun defs fn-info-map dim-var-map type-map))
                ((when err) (mv err fn-info-map (expr-app new-fun x.arg)))
                ((mv err fn-info-map new-arg)
                 (mono-expr x.arg defs fn-info-map dim-var-map type-map)))
             (mv err fn-info-map (expr-app new-fun new-arg)))

      :appn (b* (((mv err fn-info-map new-fun)
                  (mono-expr x.fun defs fn-info-map dim-var-map type-map))
                 ((when err) (mv err fn-info-map (expr-appn new-fun x.args)))
                 ((mv err fn-info-map new-args)
                  (mono-expr-list x.args defs fn-info-map dim-var-map type-map)))
              (mv err fn-info-map (expr-appn new-fun new-args)))

      :tapp (b* (((mv err fn-info-map new-fun)
                  (mono-expr x.fun defs fn-info-map dim-var-map type-map)))
              (mv err fn-info-map (expr-tapp new-fun x.arg)))

      :tappn (b* (((mv err fn-info-map new-fun)
                   (mono-expr x.fun defs fn-info-map dim-var-map type-map)))
               (mv err fn-info-map (expr-tappn new-fun x.args)))

      :iapp (b* (((mv err fn-info-map new-fun)
                  (mono-expr x.fun defs fn-info-map dim-var-map type-map)))
              (mv err fn-info-map (expr-iapp new-fun x.arg)))

      :iappn
      (b* (((mv err fn-info-map new-fun)
            (mono-expr x.fun defs fn-info-map dim-var-map type-map))
           ((when err) (mv err fn-info-map (expr-iappn new-fun x.args)))
           (fun new-fun)
           ; Only monomorphize an :iappn of a known :ifun :var to non-empty ispace args.
           ((mv err fn-info-map new-expr)
            (if (not (consp x.args))
                (mv nil fn-info-map (expr-iappn fun x.args))
              (expr-case fun
                :var (b* ((ifun-name fun.name)
                          (def-entry (assoc-equal ifun-name defs))
                          ((unless def-entry)
                           (if (assoc-equal ifun-name fn-info-map)
                               (mv :out-of-scope-fun-reference fn-info-map
                                   (expr-iappn fun x.args))
                             (mv nil fn-info-map (expr-iappn fun x.args))))
                          ((mv eval-err nats) (eval-iargs x.args dim-var-map))
                          ((when eval-err)
                           (mv :ispace-eval-error fn-info-map (expr-iappn fun x.args)))
                          (inst-name (cfun-inst-name ifun-name nil nats))
                          ; Record the request; the instance is created when
                          ; the ifun's :let is exited.
                          (fn-info-map
                           (fn-info-map-add-request
                            fn-info-map ifun-name
                            (make-inst-request :inst-name inst-name
                                               :nats nats
                                               :targ-tys nil))))
                       (mv nil fn-info-map (expr-var inst-name)))
                :otherwise (mv nil fn-info-map (expr-iappn fun x.args)))))
           ((when err) (mv err fn-info-map new-expr)))
        (mv nil fn-info-map new-expr))

      :capp
      (b* (((mv err fn-info-map new-fun)
            (mono-expr x.fun defs fn-info-map dim-var-map type-map))
           ((when err) (mv err fn-info-map (expr-capp new-fun x.targs x.iargs x.args)))
           ((mv err fn-info-map new-args)
            (mono-expr-list x.args defs fn-info-map dim-var-map type-map))
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
                                  (mono-expr (expr-appn (expr-var inst-name) new-args))
                                  (def-entry (assoc-equal cfun-name defs))
                                  ; An unknown cfun is built-in: emit the same instance call
                                  ; as for a known cfun, but do not build/register an instance.
                                  ; A registered but out-of-scope cfun is a recursive or
                                  ; forward reference, which non-recursive scoping rules out.
                                  ((unless def-entry)
                                   (if (assoc-equal cfun-name fn-info-map)
                                       (mv :out-of-scope-fun-reference fn-info-map
                                           (expr-capp fun x.targs x.iargs new-args))
                                     (mv nil fn-info-map mono-expr)))
                                  ; Record the request, with the type arguments
                                  ; resolved through the call site's type-map;
                                  ; the instance is created when the cfun's
                                  ; :let is exited.
                                  (fn-info-map
                                   (fn-info-map-add-request
                                    fn-info-map cfun-name
                                    (make-inst-request
                                     :inst-name inst-name
                                     :nats nats
                                     :targ-tys (type-list-subst-type-vars
                                                targ-tys type-map type-map)))))
                                (mv nil fn-info-map mono-expr))
                        :otherwise (mv nil fn-info-map (expr-capp fun x.targs x.iargs new-args))))))
           ((when err) (mv err fn-info-map new-expr)))
        (mv nil fn-info-map new-expr))

      :unbox (b* (((mv err fn-info-map new-target)
                   (mono-expr x.target defs fn-info-map dim-var-map type-map))
                  ((when err) (mv err fn-info-map (expr-unbox x.ispaces x.var new-target x.body x.type?)))
                  ((mv err fn-info-map new-body) (mono-expr x.body defs fn-info-map dim-var-map type-map)))
               (mv err fn-info-map (expr-unbox x.ispaces x.var new-target new-body x.type?)))

      :bracket (b* (((mv err fn-info-map new-es)
                     (mono-expr-list x.exprs defs fn-info-map dim-var-map type-map)))
                 (mv err fn-info-map (expr-bracket new-es)))

      :let (if (and (consp x.binds) (endp (cdr x.binds)))
               ;; Lets should have been normalized before calling this to have obly one bind
               (b* ((bnd (car x.binds))
                    ((mv err fn-info-map new-bind)
                     (mono-bind bnd defs fn-info-map dim-var-map type-map))
                    ((when err) (mv err fn-info-map (expr-let (list new-bind) x.body)))
                    ;; For a :cfun/:ifun bind, bring the definition into scope
                    ;; for the body.
                    (body-defs (bind-case bnd
                                          :cfun (acons bnd.var bnd defs)
                                          :ifun (acons bnd.var bnd defs)
                                          :otherwise defs))
                    ((mv err fn-info-map new-body)
                     (mono-expr x.body body-defs fn-info-map dim-var-map type-map))
                    ((when err)
                     (mv err fn-info-map (expr-let (list new-bind) new-body)))
                    ;; For a :cfun/:ifun bind, extract the requests recorded
                    ;; for it and drop its registration: the definition is out
                    ;; of scope past this :let.
                    (requests (bind-case bnd
                                         :cfun (cdr (assoc-equal bnd.var fn-info-map))
                                         :ifun (cdr (assoc-equal bnd.var fn-info-map))
                                         :otherwise nil))
                    (fn-info-map (bind-case bnd
                                            :cfun (remove1-assoc-equal bnd.var fn-info-map)
                                            :ifun (remove1-assoc-equal bnd.var fn-info-map)
                                            :otherwise fn-info-map))
                    ;; Measure headroom for the creation fold: when the body
                    ;; binds no cfuns/ifuns, no instances are created while it
                    ;; is processed, so each request comes from a distinct
                    ;; :capp/:iappn node of the body, and their number is less
                    ;; than (expr-count x).  The test makes that bound
                    ;; available to the measure prover; its failure arm is
                    ;; unreachable.
                    ((unless (or (< 0 (expr-cfun-count x.body))
                                 (< (len requests) (expr-count x))))
                     (mv :too-many-instance-requests fn-info-map
                         (expr-let (list new-bind) new-body)))
                    ;; Create the instances requested for the bind and splice
                    ;; them in (replacing the now-unused definition); for other
                    ;; binds (no requests) keep the bind.
                    ((mv err fn-info-map new-binds)
                     (mono-fun-instances bnd requests defs fn-info-map
                                         dim-var-map type-map))
                    ((when err)
                     (mv err fn-info-map (expr-let (list new-bind) new-body))))
                 (mv nil fn-info-map
                     (expr-let (if (consp new-binds) new-binds (list new-bind))
                               new-body)))
             (mv :let-not-normalized fn-info-map x))))

  (define mono-expr-list ((x expr-listp) (defs bind-mapp)
                          (fn-info-map fn-info-mapp) (dim-var-map acl2::string-nat-mapp) (type-map string-type-mapp))
    :short "Monomorphize a list of expressions."
    :returns (mv err (new-fn-info-map fn-info-mapp :hyp :guard) (new-exprs expr-listp :hyp :guard))
    :measure (two-nats-measure (+ (defs-weight defs) (expr-list-cfun-count x))
                               (expr-list-count x))
    (if (endp x)
        (mv nil fn-info-map nil)
      (b* (((mv err fn-info-map new-e)
            (mono-expr (car x) defs fn-info-map dim-var-map type-map))
           ((when err) (mv err fn-info-map (list* new-e (expr-list-fix (cdr x)))))
           ((mv err fn-info-map new-rest)
            (mono-expr-list (cdr x) defs fn-info-map dim-var-map type-map)))
        (mv err fn-info-map (cons new-e new-rest)))))

  (define mono-atom ((x atomp) (defs bind-mapp) (fn-info-map fn-info-mapp) (dim-var-map acl2::string-nat-mapp) (type-map string-type-mapp))
    :short "Monomorphize an atom."
    :returns (mv err (new-fn-info-map fn-info-mapp :hyp :guard) (new-atom atomp :hyp :guard))
    :measure (two-nats-measure (+ (defs-weight defs) (atom-cfun-count x))
                               (atom-count x))
    (atom-case x
      :base    (mv nil fn-info-map (atom-fix x))
      :lambda (b* (((mv err fn-info-map new-body)
                   (mono-expr x.body defs fn-info-map dim-var-map type-map)))
               (mv err fn-info-map (atom-lambda x.param new-body x.type?)))
      :lambdan (b* (((mv err fn-info-map new-body)
                    (mono-expr x.body defs fn-info-map dim-var-map type-map)))
                (mv err fn-info-map (atom-lambdan x.params new-body x.type?)))
      :tlambda (b* (((mv err fn-info-map new-body)
                     (mono-expr x.body defs fn-info-map dim-var-map type-map)))
                 (mv err fn-info-map (atom-tlambda x.param new-body)))
      :tlambdan (b* (((mv err fn-info-map new-body)
                      (mono-expr x.body defs fn-info-map dim-var-map type-map)))
                  (mv err fn-info-map (atom-tlambdan x.params new-body)))
      :ilambda (b* (((mv err fn-info-map new-body)
                     (mono-expr x.body defs fn-info-map dim-var-map type-map)))
                 (mv err fn-info-map (atom-ilambda x.param new-body)))
      :ilambdan (b* (((mv err fn-info-map new-body)
                      (mono-expr x.body defs fn-info-map dim-var-map type-map)))
                  (mv err fn-info-map (atom-ilambdan x.params new-body)))
      :box     (b* (((mv err fn-info-map new-array)
                     (mono-expr x.array defs fn-info-map dim-var-map type-map)))
                 (mv err fn-info-map (atom-box x.ispaces new-array x.type)))))

  (define mono-atom-list ((x atom-listp) (defs bind-mapp)
                          (fn-info-map fn-info-mapp) (dim-var-map acl2::string-nat-mapp) (type-map string-type-mapp))
    :short "Monomorphize a list of atoms."
    :returns (mv err (new-fn-info-map fn-info-mapp :hyp :guard) (new-atoms atom-listp :hyp :guard))
    :measure (two-nats-measure (+ (defs-weight defs) (atom-list-cfun-count x))
                               (atom-list-count x))
    (if (endp x)
        (mv nil fn-info-map nil)
      (b* (((mv err fn-info-map new-a)
            (mono-atom (car x) defs fn-info-map dim-var-map type-map))
           ((when err) (mv err fn-info-map (list* new-a (atom-list-fix (cdr x)))))
           ((mv err fn-info-map new-rest)
            (mono-atom-list (cdr x) defs fn-info-map dim-var-map type-map)))
        (mv err fn-info-map (cons new-a new-rest)))))

  (define mono-bind ((x bindp) (defs bind-mapp) (fn-info-map fn-info-mapp) (dim-var-map acl2::string-nat-mapp) (type-map string-type-mapp))
    :short "Monomorphize a binding, registering @(':cfun') and @(':ifun')
            definitions in fn-info-map."
    :returns (mv err (new-fn-info-map fn-info-mapp :hyp :guard) (new-bind bindp :hyp :guard))
    :long
    (xdoc::topstring
     (xdoc::p
      "For a @(':cfun') (respectively @(':ifun')) bind, the entry mapping
       @('name') to an empty request list is
       added to @('fn-info-map') and the bind is returned unchanged: the body is
       @('not') monomorphized here.  The call sites in the enclosing
       @(':let') body record instantiation requests under the entry, and the
       instances are created when that @(':let') is exited, in the scope of
       the definitions bound before it.  The registration done here
       lets those call sites, and subsequent @(':capp')/@(':iapp') expressions
       in the enclosing @(':let') body, distinguish a known function from a
       built-in one."))
    :measure (two-nats-measure (+ (defs-weight defs) (bind-cfun-count x))
                               (bind-count x))
    (bind-case x
      :ispace (mv nil fn-info-map (bind-fix x))
      :type   (mv nil fn-info-map (bind-fix x))
      :val    (b* (((mv err fn-info-map new-expr)
                    (mono-expr x.expr defs fn-info-map dim-var-map type-map)))
                (mv err fn-info-map (bind-val x.var x.type? new-expr)))
      :fun    (b* (((mv err fn-info-map new-expr)
                    (mono-expr x.expr defs fn-info-map dim-var-map type-map)))
                (mv err fn-info-map (bind-fun x.var x.params x.type? new-expr)))
      :tfun   (b* (((mv err fn-info-map new-expr)
                    (mono-expr x.expr defs fn-info-map dim-var-map type-map)))
                (mv err fn-info-map (bind-tfun x.var x.params x.type? new-expr)))
      :ifun   (b* (; Register ifun but don't process body because we are only interested in the mono versions
                   (fn-info-map (acons x.var nil fn-info-map))
                  )
                (mv nil fn-info-map (bind-fix x)))
      :cfun   (b* (; Register cfun but don't process body because we are only interested in the mono versions
                   (fn-info-map (acons x.var nil fn-info-map))
                  )
                (mv nil fn-info-map (bind-fix x)))))

  ; Instance creation for the :let case of mono-expr.  MONO-FUN-INSTANCES
  ; folds over the requests recorded for the :let's own :cfun/:ifun bind,
  ; building one instance bind per request; the generators recurse on the
  ; (substituted) definition body in the :let's own scope DEFS, which is
  ; exactly the scope of the definition's body.

  (define mono-fun-instances ((fun-bind bindp) (requests inst-request-listp)
                              (defs bind-mapp) (fn-info-map fn-info-mapp)
                              (dim-var-map acl2::string-nat-mapp)
                              (type-map string-type-mapp))
    :short "Create the monomorphized instance binds for the requests
            recorded for a @(':cfun') or @(':ifun') definition."
    :returns (mv err (new-fn-info-map fn-info-mapp :hyp :guard)
                 (insts bind-listp :hyp :guard))
    :measure (two-nats-measure (+ (defs-weight defs) (bind-cfun-count fun-bind))
                               (len requests))
    (b* (((when (endp requests)) (mv nil fn-info-map nil))
         ((inst-request req) (car requests))
         ((mv err fn-info-map inst-bind)
          (bind-case fun-bind
            :cfun (mono-cfun-instance req.inst-name req.nats req.targ-tys
                                      fun-bind defs fn-info-map
                                      dim-var-map type-map)
            :ifun (mono-ifun-instance req.inst-name req.nats
                                      fun-bind defs fn-info-map
                                      dim-var-map type-map)
            ; Requests are only recorded for registered :cfun/:ifun binds.
            :otherwise (mv :bad-fun-bind fn-info-map (bind-fix fun-bind))))
         ((when err) (mv err fn-info-map nil))
         ((mv err fn-info-map rest-binds)
          (mono-fun-instances fun-bind (cdr requests) defs fn-info-map
                              dim-var-map type-map))
         ((when err) (mv err fn-info-map nil)))
      (mv nil fn-info-map (cons inst-bind rest-binds))))

  (define mono-cfun-instance ((inst-name stringp)
                              (nats nat-listp) (targ-tys type-listp)
                              (cfun-bind bindp) (defs bind-mapp)
                              (fn-info-map fn-info-mapp)
                              (dim-var-map acl2::string-nat-mapp)
                              (type-map string-type-mapp))
    :short "Generate the monomorphized @(':fun') instance bind for a
            recorded request to instantiate a @(':cfun')."
    :long
    (xdoc::topstring
     (xdoc::p
      "@('cfun-bind') is the definition bound by the @(':let') being exited,
       and @('defs') is the @(':let')'s scope environment, i.e. the
       definitions bound before the @(':cfun').
       The @(':cfun')'s ispace parameters are bound to @('nats') and
       its type parameters to @('targ-tys'); its value parameters, return type,
       and body are partially evaluated and type-substituted accordingly; and
       the resulting @(':fun') @(tsee bind) is returned.
       Fails with @(':bad-cfun-entry') if @('cfun-bind') is not a
       @(':cfun')."))
    :returns (mv err (new-fn-info-map fn-info-mapp :hyp :guard)
                 (inst-bind bindp :hyp :guard))
    :measure (two-nats-measure (+ (defs-weight defs) (bind-cfun-count cfun-bind))
                               0)
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
           ; Monomorphize the cfun body, in the scope of the definitions
           ; bound before the cfun itself.
           ((mv body-err fn-info-map new-body)
            (mono-expr body-in defs fn-info-map ext-dim-var-map ext-type-map))
           ((when body-err) (mv body-err fn-info-map (bind-fix cfun-bind))))
        (mv nil fn-info-map (bind-fun inst-name new-params new-type new-body)))
      :otherwise
      ; Not a :cfun request: malformed call; fail loudly.
      (mv :bad-cfun-entry fn-info-map (bind-fix cfun-bind))))

  (define mono-ifun-instance ((inst-name stringp)
                              (nats nat-listp)
                              (ifun-bind bindp) (defs bind-mapp)
                              (fn-info-map fn-info-mapp)
                              (dim-var-map acl2::string-nat-mapp)
                              (type-map string-type-mapp))
    :short "Generate the monomorphized @(':val') instance bind for a
            recorded request to instantiate an @(':ifun')."
    :long
    (xdoc::topstring
     (xdoc::p
      "Like @(tsee mono-cfun-instance), but for an @(':ifun'), which abstracts
       only ispace parameters: the instance is a @(':val') (no value parameters
       remain) rather than a @(':fun'), and only dimension substitution is
       applied.  Fails with @(':bad-ifun-entry') if @('ifun-bind') is not an
       @(':ifun')."))
    :returns (mv err (new-fn-info-map fn-info-mapp :hyp :guard)
                 (inst-bind bindp :hyp :guard))
    :measure (two-nats-measure (+ (defs-weight defs) (bind-cfun-count ifun-bind))
                               0)
    (bind-case ifun-bind
      :ifun
      (b* ((ext-dim-var-map (extend-ispace-val-map ifun-bind.params nats dim-var-map))
           (new-type? (type-option-partial-eval-dims ifun-bind.type? ext-dim-var-map))
           (body-in (expr-partial-eval-dims ifun-bind.expr ext-dim-var-map))
           ((mv body-err fn-info-map new-body)
            (mono-expr body-in defs fn-info-map ext-dim-var-map type-map))
           ((when body-err) (mv body-err fn-info-map (bind-fix ifun-bind))))
        (mv nil fn-info-map (bind-val inst-name new-type? new-body)))
      :otherwise
      ; Not an :ifun request: malformed call; fail loudly.
      (mv :bad-ifun-entry fn-info-map (bind-fix ifun-bind)))))

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
     On success @('error') is @('nil'); the monomorphized instances are
     spliced into the @(':let')s of the definitions they instantiate, and
     @('fn-info-map') is empty (every registration is dropped when its
     @(':let') is exited).
     On failure @('error') is a keyword: currently
     @(':ispace-eval-error') (an ispace argument failed to evaluate to a nat),
     @(':out-of-scope-fun-reference') (a @(':capp')/@(':iapp') of a known
     @(':cfun')/@(':ifun') outside its scope, i.e. a recursive or forward
     reference, which Remora's non-recursive @('let') scoping rules out),
     @(':let-not-normalized') (a @(':let') with other than one bind survived
     the normalization),
     @(':bad-ifun-entry') / @(':bad-cfun-entry') / @(':bad-fun-bind') (an
     instantiation request resolved to a binding of the wrong kind),
     or @(':too-many-instance-requests') (unreachable; see the @(':let')
     case of @(tsee mono-expr))."))
  (b* ((expr (expr-uniquify-names expr))
       (expr (expr-singletonize-let expr))
       ((mv err fn-info-map new-expr)
        (mono-expr expr nil nil nil nil)))
    (mv err fn-info-map (expr-flatten-let new-expr))))
