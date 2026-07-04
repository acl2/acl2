; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-structurals")
(include-book "abstract-syntax-trees")
(include-book "bound-and-free-variable-operations")
(include-book "fresh-variable-operations")
(include-book "variable-renaming-operations")

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(include-book "portcullis")

(local (include-book "std/omaps/top" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unique-names
  :parents (remora)
  :short "Detection of duplicate bind names in Remora programs,
          and renaming of binds to make all bind names unique."
  :long
  (xdoc::topstring
   (xdoc::p
    "Transformations that substitute variables without regard to shadowing
     (e.g. the maps applied by @(see monomorphize)) are only safe when
     the names introduced by binders are unique.
     @(tsee prog-duplicate-bind-names) checks that property for
     @(':let') binds, @(tsee prog-duplicate-binder-names) checks it for
     all binders (binds as well as lambda, unbox, and function-bind
     parameters), and @(tsee prog-uniquify-bind-names) establishes it by
     renaming binds and parameters,
     keeping the original names where possible."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Duplicate bind-name detection.

(define bind-name ((b bindp))
  :returns (name stringp)
  :short "Name string bound by a @(tsee bind) of any kind."
  (bind-case b
    :ispace (ispace-var->name b.var)
    :type   (type-var->name b.var)
    :val    b.var
    :fun    b.var
    :tfun   b.var
    :ifun   b.var
    :cfun   b.var))

(define bind-list-names ((binds bind-listp))
  :returns (names string-listp)
  :short "Names bound by a list of binds, in order."
  (if (endp binds)
      nil
    (cons (bind-name (car binds))
          (bind-list-names (cdr binds)))))

; Fold: collect the names of all binds occurring anywhere in an AST.  Binds
; occur only in :let expressions, so only that case needs an override: it
; contributes the let's own bind names in addition to the names collected
; from the binds' sub-expressions and from the body.

(fty::deffold-reduce bind-names
  :short "Collect the names of all @(tsee bind)s occurring in an AST."
  :types (exprs/atoms/binds
          prog)
  :result string-listp
  :default nil
  :combine append
  :override
  ((expr :let (append (bind-list-names expr.binds)
                      (append (bind-list-bind-names expr.binds)
                              (expr-bind-names expr.body)))))
  :name ast-bind-names)

(define prog-duplicate-bind-names ((prog progp))
  :returns (dup-names string-listp)
  :short "List the names bound by more than one @(tsee bind) in a program."
  :long
  (xdoc::topstring
   (xdoc::p
    "Returns @('nil') if all binds in the program bind distinct names;
     otherwise returns the duplicated names (a name bound @('n') times
     is listed @('n - 1') times)."))
  (duplicated-names (prog-bind-names prog))
  :prepwork
  ((define duplicated-names ((names string-listp))
     :returns (dups string-listp)
     :parents nil
     (cond ((endp names) nil)
           ((member-equal (car names) (cdr names))
            (cons (str-fix (car names))
                  (duplicated-names (cdr names))))
           (t (duplicated-names (cdr names)))))))

; Fold: collect the names of all binders (bind names as well as parameter
; names of lambdas, unboxes, and function binds) occurring anywhere in an
; AST, so that the uniqueness of all binder names can be checked.

(fty::deffold-reduce binder-names
  :short "Collect the names of all binders occurring in an AST:
          bind names and parameter names."
  :types (exprs/atoms/binds
          prog)
  :result string-listp
  :default nil
  :combine append
  :override
  ((expr :let (append (bind-list-names expr.binds)
                      (append (bind-list-binder-names expr.binds)
                              (expr-binder-names expr.body))))
   (expr :unbox (cons expr.var
                      (append (ispace-var-list->name expr.ispaces)
                              (append (expr-binder-names expr.target)
                                      (expr-binder-names expr.body)))))
   (atom :lambda (append (var+type?-list->var atom.params)
                         (expr-binder-names atom.body)))
   (atom :tlambda (append (type-var-list->name atom.params)
                          (expr-binder-names atom.body)))
   (atom :ilambda (append (ispace-var-list->name atom.params)
                          (expr-binder-names atom.body)))
   (bind :fun (append (var+type?-list->var bind.params)
                      (expr-binder-names bind.expr)))
   (bind :tfun (append (type-var-list->name bind.params)
                       (expr-binder-names bind.expr)))
   (bind :ifun (append (ispace-var-list->name bind.params)
                       (expr-binder-names bind.expr)))
   (bind :cfun (append (type-var-list-option-case
                        bind.tparams?
                        :some (type-var-list->name bind.tparams?.val)
                        :none nil)
                       (append (ispace-var-list-option-case
                                bind.iparams?
                                :some (ispace-var-list->name
                                       bind.iparams?.val)
                                :none nil)
                               (append (var+type?-list->var bind.params)
                                       (expr-binder-names bind.expr))))))
  :name ast-binder-names)

(define prog-duplicate-binder-names ((prog progp))
  :returns (dup-names string-listp)
  :short "List the names bound by more than one binder
          (bind or parameter) in a program."
  :long
  (xdoc::topstring
   (xdoc::p
    "Returns @('nil') if all binders in the program bind distinct names;
     otherwise returns the duplicated names (a name bound @('n') times
     is listed @('n - 1') times).
     After @(tsee prog-uniquify-bind-names) this returns @('nil')."))
  (duplicated-names (prog-binder-names prog)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Binder-name uniquification: rename binds and parameters so that all binder
; names in a program are distinct, keeping the original names where possible.
; A binder (a bind, or a parameter of a lambda, unbox, or function bind)
; keeps its name unless that name has already been seen (as an earlier
; binder name or a free variable name of the program); in that case it is
; renamed to a fresh variant of the name, and the renaming is applied to the
; binder's scope via the renaming operations from
; variable-renaming-operations.lisp.  Since fresh names avoid all names seen
; so far and all free variable names, the renamings cannot capture.

; The five renaming maps, one per variable namespace (dimension and shape
; ispace variables, atom-kind and array-kind type variables, and expression
; variables), bundled so that the traversal threads a single value.

(fty::defprod var-renamings
  :short "Fixtype of renaming maps for all five variable namespaces,
          plus the constant set of names that fresh names must avoid."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('avoid') component is not a renaming: it is the set of all
     variable names occurring anywhere in the program (in any namespace and
     any role), fixed throughout the traversal.  Freshly generated bind
     names must avoid it, so that they can never capture (or be captured
     by) an occurrence of an existing name --- in particular one whose
     binder has not been encountered yet, such as a parameter of a lambda
     abstraction later in the program."))
  ((dim acl2::string-string-map)
   (shape acl2::string-string-map)
   (atom acl2::string-string-map)
   (array acl2::string-string-map)
   (expr acl2::string-string-map)
   (avoid acl2::string-set))
  :pred var-renamings-p)

(define rename-var-string ((name stringp) (renam string-string-mapp))
  :returns (new-name stringp)
  :short "Apply a renaming map to a variable name."
  (b* ((pair (omap::assoc (str-fix name) (string-string-map-fix renam))))
    (if pair (str-fix (cdr pair)) (str-fix name))))

(define fresh-bind-name ((name stringp) (used string-setp) (avoid string-setp))
  :returns (new-name stringp)
  :short "Keep @('name') if it is not in @('used');
          otherwise generate a fresh variant of it,
          avoiding both @('used') and @('avoid')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The fresh variant is generated by @(tsee fresh-expr-var), which appends
     a numeric index to the name.  Although that operation is nominally about
     expression variables, it is pure string generation, so we use it for
     bind names of every namespace.")
   (xdoc::p
    "The variant avoids not only the names seen so far (@('used')) but also
     all names occurring anywhere in the program (@('avoid')), so that it
     cannot capture, or be captured by, any binder --- including binders not
     yet encountered by the traversal."))
  (if (set::in (str-fix name) (string-sfix used))
      (fresh-expr-var name (set::union (string-sfix used)
                                       (string-sfix avoid)))
    (str-fix name)))

(define extend-renaming ((name stringp) (new-name stringp)
                         (renam string-string-mapp))
  :returns (new-renam string-string-mapp)
  :short "Record @('name -> new-name') in a renaming map if the names differ;
          otherwise delete any stale entry for @('name')."
  (b* ((renam (string-string-map-fix renam))
       (name (str-fix name)))
    (if (equal name (str-fix new-name))
        (omap::delete name renam)
      (omap::update name (str-fix new-name) renam))))

; Parameter uniquification: parameters are renamed exactly like bind names.
; Each parameter keeps its name if it has not been seen, and otherwise is
; renamed to a fresh variant; the renamings are extended accordingly (which
; also clears any stale outer entry when a name is kept, so the outer
; renaming cannot capture the parameter).  The parameters of a single
; binder are processed sequentially, so duplicate names within one
; parameter list are also made distinct, consistently with the sequential
; extension of the dynamic environment at application time.

(define uniq-expr-params ((params var+type?-listp)
                          (used string-setp)
                          (avoid string-setp)
                          (renam string-string-mapp))
  :returns (mv (new-used string-setp :hyp :guard)
               (new-params var+type?-listp :hyp :guard)
               (new-renam string-string-mapp :hyp :guard))
  :short "Uniquify the names of a list of expression-variable parameters.
          The types in the parameters must have been renamed already."
  (b* (((when (endp params))
        (mv (string-sfix used) nil (string-string-map-fix renam)))
       ((var+type? p) (car params))
       (new-name (fresh-bind-name p.var used avoid))
       (used (set::insert new-name (string-sfix used)))
       (renam (extend-renaming p.var new-name renam))
       ((mv used new-rest renam)
        (uniq-expr-params (cdr params) used avoid renam)))
    (mv used
        (cons (make-var+type? :var new-name :type? p.type?) new-rest)
        renam)))

(define uniq-type-var-params ((params type-var-listp)
                              (used string-setp)
                              (avoid string-setp)
                              (atom-renam string-string-mapp)
                              (array-renam string-string-mapp))
  :returns (mv (new-used string-setp :hyp :guard)
               (new-params type-var-listp :hyp :guard)
               (new-atom-renam string-string-mapp :hyp :guard)
               (new-array-renam string-string-mapp :hyp :guard))
  :short "Uniquify the names of a list of type-variable parameters."
  (b* (((when (endp params))
        (mv (string-sfix used) nil
            (string-string-map-fix atom-renam)
            (string-string-map-fix array-renam)))
       (var (car params))
       (name (type-var->name var))
       (new-name (fresh-bind-name name used avoid))
       (used (set::insert new-name (string-sfix used)))
       ((mv new-var atom-renam array-renam)
        (type-var-case var
          :atom (mv (type-var-atom new-name)
                    (extend-renaming name new-name atom-renam)
                    (string-string-map-fix array-renam))
          :array (mv (type-var-array new-name)
                     (string-string-map-fix atom-renam)
                     (extend-renaming name new-name array-renam))))
       ((mv used new-rest atom-renam array-renam)
        (uniq-type-var-params (cdr params) used avoid
                              atom-renam array-renam)))
    (mv used (cons new-var new-rest) atom-renam array-renam)))

(define uniq-ispace-var-params ((params ispace-var-listp)
                                (used string-setp)
                                (avoid string-setp)
                                (dim-renam string-string-mapp)
                                (shape-renam string-string-mapp))
  :returns (mv (new-used string-setp :hyp :guard)
               (new-params ispace-var-listp :hyp :guard)
               (new-dim-renam string-string-mapp :hyp :guard)
               (new-shape-renam string-string-mapp :hyp :guard))
  :short "Uniquify the names of a list of ispace-variable parameters."
  (b* (((when (endp params))
        (mv (string-sfix used) nil
            (string-string-map-fix dim-renam)
            (string-string-map-fix shape-renam)))
       (var (car params))
       (name (ispace-var->name var))
       (new-name (fresh-bind-name name used avoid))
       (used (set::insert new-name (string-sfix used)))
       ((mv new-var dim-renam shape-renam)
        (ispace-var-case var
          :dim (mv (ispace-var-dim new-name)
                   (extend-renaming name new-name dim-renam)
                   (string-string-map-fix shape-renam))
          :shape (mv (ispace-var-shape new-name)
                     (string-string-map-fix dim-renam)
                     (extend-renaming name new-name shape-renam))))
       ((mv used new-rest dim-renam shape-renam)
        (uniq-ispace-var-params (cdr params) used avoid
                                dim-renam shape-renam)))
    (mv used (cons new-var new-rest) dim-renam shape-renam)))

; Apply all applicable renamings (ispace and type variables; expression
; variables do not occur in types) to type-level components.

(define type-rename-all-vars ((ty typep) (r var-renamings-p))
  :returns (new-ty typep)
  :short "Apply all five renamings to a type."
  (b* (((var-renamings r) r))
    (type-rename-type-vars
     (type-rename-ispace-vars ty r.dim r.shape)
     r.atom r.array)))

(define type-option-rename-all-vars ((ty? type-optionp) (r var-renamings-p))
  :returns (new-ty? type-optionp)
  :short "Apply all five renamings to an optional type."
  (b* (((var-renamings r) r))
    (type-option-rename-type-vars
     (type-option-rename-ispace-vars ty? r.dim r.shape)
     r.atom r.array)))

(define type-list-rename-all-vars ((tys type-listp) (r var-renamings-p))
  :returns (new-tys type-listp)
  :short "Apply all five renamings to a list of types."
  (b* (((var-renamings r) r))
    (type-list-rename-type-vars
     (type-list-rename-ispace-vars tys r.dim r.shape)
     r.atom r.array)))

(define type-list-option-rename-all-vars ((tys? type-list-optionp)
                                          (r var-renamings-p))
  :returns (new-tys? type-list-optionp)
  :short "Apply all five renamings to an optional list of types."
  (b* (((var-renamings r) r))
    (type-list-option-rename-type-vars
     (type-list-option-rename-ispace-vars tys? r.dim r.shape)
     r.atom r.array)))

(define var+type?-list-rename-all-vars ((params var+type?-listp)
                                        (r var-renamings-p))
  :returns (new-params var+type?-listp)
  :short "Apply all five renamings to the types in a parameter list
          (the parameter names themselves are not renamed)."
  (b* (((var-renamings r) r))
    (var+type?-list-rename-type-vars
     (var+type?-list-rename-ispace-vars params r.dim r.shape)
     r.atom r.array)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Main uniquification traversal.
;
; The traversal functions take:
;   x    : AST node          — the node being processed
;   used : string-setp       — all names seen so far (bind names, parameter
;                              names, and the program's free variable names)
;   r    : var-renamings-p   — the renamings currently in scope
; and return (mv new-used new-x), plus, for binds, the renamings extended
; with the scope of the processed bind(s).
;
; Parameter-like binders (lambda/tlambda/ilambda parameters, unbox variables,
; function parameters) are uniquified exactly like bind names: each keeps
; its name if unseen and is otherwise renamed to a fresh variant, and the
; in-scope renamings are extended accordingly (which clears any stale outer
; entry when a name is kept, so the outer renamings do not capture the
; parameter); see the UNIQ-*-PARAMS functions above.

(defines uniquify-bind-names-impl
  :verify-guards :after-returns
  :ruler-extenders :all

  (define uniq-expr ((x exprp) (used string-setp) (r var-renamings-p))
    :short "Uniquify binder names in an expression."
    :returns (mv (new-used string-setp :hyp :guard)
                 (new-x exprp :hyp :guard))
    :measure (expr-count x)
    (expr-case x
      :var (mv used (expr-var (rename-var-string x.name (var-renamings->expr r))))

      :atom (b* (((mv used new-a) (uniq-atom x.atom used r)))
              (mv used (expr-atom new-a)))

      :array (b* (((mv used new-atoms) (uniq-atom-list x.atoms used r)))
               (mv used (expr-array x.dims new-atoms)))

      :array-empty (mv used (expr-array-empty x.dims
                                              (type-rename-all-vars x.type r)))

      :frame (b* (((mv used new-es) (uniq-expr-list x.exprs used r)))
               (mv used (expr-frame x.dims new-es)))

      :frame-empty (mv used (expr-frame-empty x.dims
                                              (type-rename-all-vars x.type r)))

      :string (mv used (expr-fix x))

      :app (b* (((mv used new-fun) (uniq-expr x.fun used r))
                ((mv used new-args) (uniq-expr-list x.args used r)))
             (mv used (expr-app new-fun new-args)))

      :tapp (b* (((mv used new-fun) (uniq-expr x.fun used r)))
              (mv used (expr-tapp new-fun (type-list-rename-all-vars x.args r))))

      :iapp (b* (((var-renamings r-) r)
                 ((mv used new-fun) (uniq-expr x.fun used r)))
              (mv used (expr-iapp new-fun
                                  (ispace-list-rename-ispace-vars
                                   x.args r-.dim r-.shape))))

      :capp (b* (((var-renamings r-) r)
                 ((mv used new-fun) (uniq-expr x.fun used r))
                 ((mv used new-args) (uniq-expr-list x.args used r)))
              (mv used (expr-capp new-fun
                                  (type-list-option-rename-all-vars x.targs r)
                                  (ispace-list-option-rename-ispace-vars
                                   x.iargs r-.dim r-.shape)
                                  new-args)))

      :unbox (b* (((var-renamings r-) r)
                  ((mv used new-target) (uniq-expr x.target used r))
                  ;; The result type is outside the scope of the unboxed
                  ;; ispaces, so we rename it under the incoming renamings.
                  (new-type? (type-option-rename-all-vars x.type? r))
                  ((mv used new-ispaces dim-renam shape-renam)
                   (uniq-ispace-var-params x.ispaces used r-.avoid
                                           r-.dim r-.shape))
                  (new-var (fresh-bind-name x.var used r-.avoid))
                  (used (set::insert new-var (string-sfix used)))
                  (expr-renam (extend-renaming x.var new-var r-.expr))
                  (body-r (change-var-renamings r
                                                :dim dim-renam
                                                :shape shape-renam
                                                :expr expr-renam))
                  ((mv used new-body) (uniq-expr x.body used body-r)))
               (mv used (make-expr-unbox :ispaces new-ispaces
                                         :var new-var
                                         :target new-target
                                         :body new-body
                                         :type? new-type?)))

      :bracket (b* (((mv used new-es) (uniq-expr-list x.exprs used r)))
                 (mv used (expr-bracket new-es)))

      :let (b* (((mv used new-binds new-r) (uniq-bind-list x.binds used r))
                ((mv used new-body) (uniq-expr x.body used new-r)))
             (mv used (expr-let new-binds new-body)))))

  (define uniq-expr-list ((x expr-listp) (used string-setp) (r var-renamings-p))
    :short "Uniquify binder names in a list of expressions."
    :returns (mv (new-used string-setp :hyp :guard)
                 (new-x expr-listp :hyp :guard))
    :measure (expr-list-count x)
    (if (endp x)
        (mv used nil)
      (b* (((mv used new-e) (uniq-expr (car x) used r))
           ((mv used new-rest) (uniq-expr-list (cdr x) used r)))
        (mv used (cons new-e new-rest)))))

  (define uniq-atom ((x atomp) (used string-setp) (r var-renamings-p))
    :short "Uniquify binder names in an atom."
    :returns (mv (new-used string-setp :hyp :guard)
                 (new-x atomp :hyp :guard))
    :measure (atom-count x)
    (atom-case x
      :base (mv used (atom-fix x))

      :lambda (b* (((var-renamings r-) r)
                   (typed-params (var+type?-list-rename-all-vars x.params r))
                   (new-type? (type-option-rename-all-vars x.type? r))
                   ((mv used new-params expr-renam)
                    (uniq-expr-params typed-params used r-.avoid r-.expr))
                   ((mv used new-body)
                    (uniq-expr x.body used
                               (change-var-renamings r :expr expr-renam))))
                (mv used (make-atom-lambda :params new-params
                                           :body new-body
                                           :type? new-type?)))

      :tlambda (b* (((var-renamings r-) r)
                    ((mv used new-params atom-renam array-renam)
                     (uniq-type-var-params x.params used r-.avoid
                                           r-.atom r-.array))
                    ((mv used new-body)
                     (uniq-expr x.body used
                                (change-var-renamings r
                                                      :atom atom-renam
                                                      :array array-renam))))
                 (mv used (atom-tlambda new-params new-body)))

      :ilambda (b* (((var-renamings r-) r)
                    ((mv used new-params dim-renam shape-renam)
                     (uniq-ispace-var-params x.params used r-.avoid
                                             r-.dim r-.shape))
                    ((mv used new-body)
                     (uniq-expr x.body used
                                (change-var-renamings r
                                                      :dim dim-renam
                                                      :shape shape-renam))))
                 (mv used (atom-ilambda new-params new-body)))

      :box (b* (((var-renamings r-) r)
                ((mv used new-array) (uniq-expr x.array used r)))
             (mv used (atom-box (ispace-list-rename-ispace-vars
                                 x.ispaces r-.dim r-.shape)
                                new-array
                                (type-rename-all-vars x.type r))))))

  (define uniq-atom-list ((x atom-listp) (used string-setp) (r var-renamings-p))
    :short "Uniquify binder names in a list of atoms."
    :returns (mv (new-used string-setp :hyp :guard)
                 (new-x atom-listp :hyp :guard))
    :measure (atom-list-count x)
    (if (endp x)
        (mv used nil)
      (b* (((mv used new-a) (uniq-atom (car x) used r))
           ((mv used new-rest) (uniq-atom-list (cdr x) used r)))
        (mv used (cons new-a new-rest)))))

  (define uniq-bind ((x bindp) (used string-setp) (r var-renamings-p))
    :short "Uniquify binder names in a bind, renaming the bind itself
            if its name has been seen before."
    :returns (mv (new-used string-setp :hyp :guard)
                 (new-x bindp :hyp :guard)
                 (new-r var-renamings-p :hyp :guard))
    :long
    (xdoc::topstring
     (xdoc::p
      "The bind's components are processed under the incoming renamings
       (the bind's own name is not in scope in its own definition, since
       @('let') binds are not recursive).  Then the bind's name is kept if
       it has not been seen, and otherwise renamed to a fresh variant; the
       returned renamings, to be used for the remainder of the enclosing
       @('let')'s scope, record the renaming (or clear a stale entry when
       the name is kept)."))
    :measure (bind-count x)
    (bind-case x
      :ispace (b* (((var-renamings r-) r)
                   (new-ispace (ispace-rename-ispace-vars x.ispace
                                                          r-.dim r-.shape))
                   (name (ispace-var->name x.var))
                   (new-name (fresh-bind-name name used r-.avoid))
                   (used (set::insert new-name (string-sfix used)))
                   ((mv new-var new-r)
                    (ispace-var-case x.var
                      :dim (mv (ispace-var-dim new-name)
                               (change-var-renamings
                                r :dim (extend-renaming name new-name r-.dim)))
                      :shape (mv (ispace-var-shape new-name)
                                 (change-var-renamings
                                  r :shape (extend-renaming name new-name
                                                            r-.shape))))))
                (mv used (bind-ispace new-var new-ispace) new-r))

      :type (b* (((var-renamings r-) r)
                 (new-type (type-rename-all-vars x.type r))
                 (name (type-var->name x.var))
                 (new-name (fresh-bind-name name used r-.avoid))
                 (used (set::insert new-name (string-sfix used)))
                 ((mv new-var new-r)
                  (type-var-case x.var
                    :atom (mv (type-var-atom new-name)
                              (change-var-renamings
                               r :atom (extend-renaming name new-name r-.atom)))
                    :array (mv (type-var-array new-name)
                               (change-var-renamings
                                r :array (extend-renaming name new-name
                                                          r-.array))))))
              (mv used (bind-type new-var new-type) new-r))

      :val (b* (((var-renamings r-) r)
                (new-type? (type-option-rename-all-vars x.type? r))
                ((mv used new-expr) (uniq-expr x.expr used r))
                (new-name (fresh-bind-name x.var used r-.avoid))
                (used (set::insert new-name (string-sfix used)))
                (new-r (change-var-renamings
                        r :expr (extend-renaming x.var new-name r-.expr))))
             (mv used (bind-val new-name new-type? new-expr) new-r))

      :fun (b* (((var-renamings r-) r)
                (typed-params (var+type?-list-rename-all-vars x.params r))
                (new-type? (type-option-rename-all-vars x.type? r))
                ((mv used new-params expr-renam)
                 (uniq-expr-params typed-params used r-.avoid r-.expr))
                ((mv used new-expr)
                 (uniq-expr x.expr used
                            (change-var-renamings r :expr expr-renam)))
                (new-name (fresh-bind-name x.var used r-.avoid))
                (used (set::insert new-name (string-sfix used)))
                (new-r (change-var-renamings
                        r :expr (extend-renaming x.var new-name r-.expr))))
             (mv used (bind-fun new-name new-params new-type? new-expr) new-r))

      :tfun (b* (((var-renamings r-) r)
                 ((mv used new-params atom-renam array-renam)
                  (uniq-type-var-params x.params used r-.avoid
                                        r-.atom r-.array))
                 (inner-r (change-var-renamings r
                                                :atom atom-renam
                                                :array array-renam))
                 (new-type? (type-option-rename-all-vars x.type? inner-r))
                 ((mv used new-expr) (uniq-expr x.expr used inner-r))
                 (new-name (fresh-bind-name x.var used r-.avoid))
                 (used (set::insert new-name (string-sfix used)))
                 (new-r (change-var-renamings
                         r :expr (extend-renaming x.var new-name r-.expr))))
              (mv used
                  (bind-tfun new-name new-params new-type? new-expr)
                  new-r))

      :ifun (b* (((var-renamings r-) r)
                 ((mv used new-params dim-renam shape-renam)
                  (uniq-ispace-var-params x.params used r-.avoid
                                          r-.dim r-.shape))
                 (inner-r (change-var-renamings r
                                                :dim dim-renam
                                                :shape shape-renam))
                 (new-type? (type-option-rename-all-vars x.type? inner-r))
                 ((mv used new-expr) (uniq-expr x.expr used inner-r))
                 (new-name (fresh-bind-name x.var used r-.avoid))
                 (used (set::insert new-name (string-sfix used)))
                 (new-r (change-var-renamings
                         r :expr (extend-renaming x.var new-name r-.expr))))
              (mv used
                  (bind-ifun new-name new-params new-type? new-expr)
                  new-r))

      :cfun (b* (((var-renamings r-) r)
                 (tparams (type-var-list-option-case x.tparams?
                            :some x.tparams?.val :none nil))
                 (iparams (ispace-var-list-option-case x.iparams?
                            :some x.iparams?.val :none nil))
                 ((mv used new-tparams atom-renam array-renam)
                  (uniq-type-var-params tparams used r-.avoid
                                        r-.atom r-.array))
                 ((mv used new-iparams dim-renam shape-renam)
                  (uniq-ispace-var-params iparams used r-.avoid
                                          r-.dim r-.shape))
                 (inner-r (change-var-renamings r
                                                :dim dim-renam
                                                :shape shape-renam
                                                :atom atom-renam
                                                :array array-renam))
                 (typed-params (var+type?-list-rename-all-vars x.params
                                                               inner-r))
                 (new-type (type-rename-all-vars x.type inner-r))
                 ((mv used new-params expr-renam)
                  (uniq-expr-params typed-params used r-.avoid r-.expr))
                 ((mv used new-expr)
                  (uniq-expr x.expr used
                             (change-var-renamings inner-r :expr expr-renam)))
                 (new-name (fresh-bind-name x.var used r-.avoid))
                 (used (set::insert new-name (string-sfix used)))
                 (new-r (change-var-renamings
                         r :expr (extend-renaming x.var new-name r-.expr))))
              (mv used
                  (make-bind-cfun :var new-name
                                  :tparams? (type-var-list-option-case
                                             x.tparams?
                                             :some (type-var-list-option-some
                                                    new-tparams)
                                             :none (type-var-list-option-none))
                                  :iparams? (ispace-var-list-option-case
                                             x.iparams?
                                             :some (ispace-var-list-option-some
                                                    new-iparams)
                                             :none (ispace-var-list-option-none))
                                  :params new-params
                                  :type new-type
                                  :expr new-expr)
                  new-r))))

  (define uniq-bind-list ((x bind-listp) (used string-setp) (r var-renamings-p))
    :short "Uniquify binder names in a list of binds, threading the renamings
            through the binds' sequential scopes."
    :returns (mv (new-used string-setp :hyp :guard)
                 (new-x bind-listp :hyp :guard)
                 (new-r var-renamings-p :hyp :guard))
    :measure (bind-list-count x)
    (if (endp x)
        (mv used nil (var-renamings-fix r))
      (b* (((mv used new-bind r) (uniq-bind (car x) used r))
           ((mv used new-rest r) (uniq-bind-list (cdr x) used r)))
        (mv used (cons new-bind new-rest) r)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prog-uniquify-bind-names ((prog progp))
  :returns (new-prog progp)
  :short "Rename binds and parameters so that all binder names in a program
          are distinct, keeping the original names where possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "Traverses the program left-to-right, accumulating the set of names seen
     so far, initialized with the names of the program's free variables in
     all namespaces (so that no binder is renamed to, or left colliding with,
     e.g. a built-in function name).  A binder --- a bind, or a parameter of
     a lambda (of any kind), an unbox, or a function bind --- whose name has
     not been seen keeps it; otherwise the binder is renamed to a fresh
     variant of its name (the name with a numeric suffix), and the renaming
     is applied throughout the binder's scope.")
   (xdoc::p
    "Afterwards @(tsee prog-duplicate-binder-names) returns @('nil') (so in
     particular @(tsee prog-duplicate-bind-names) does too), and no binder
     name coincides with a free variable name of the program.")
   (xdoc::p
    "The generated fresh names avoid the names of all the variables
     occurring anywhere in the program, in any namespace and any role
     (see the @('avoid') component of @(tsee var-renamings)), so the
     renamings applied to the binds' scopes are capture-free."))
  (b* (((mv free-dim-names free-shape-names)
        (dim/shape-names-of-ispace-vars (prog-free-ispace-vars prog)))
       ((mv free-atom-names free-array-names)
        (atom/array-names-of-type-vars (prog-free-type-vars prog)))
       (used (set::union
              (prog-free-expr-vars prog)
              (set::union
               free-dim-names
               (set::union free-shape-names
                           (set::union free-atom-names free-array-names)))))
       ((mv all-dim-names all-shape-names)
        (dim/shape-names-of-ispace-vars (prog-all-ispace-vars prog)))
       ((mv all-atom-names all-array-names)
        (atom/array-names-of-type-vars (prog-all-type-vars prog)))
       (avoid (set::union
               (prog-all-expr-vars prog)
               (set::union
                all-dim-names
                (set::union all-shape-names
                            (set::union all-atom-names all-array-names)))))
       (r (make-var-renamings :dim nil :shape nil :atom nil :array nil
                              :expr nil :avoid avoid))
       ((mv & new-expr) (uniq-expr (prog->expr prog) used r)))
    (make-prog :expr new-expr)))
