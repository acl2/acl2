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
     the names bound by @(':let') binds are unique.
     @(tsee prog-duplicate-bind-names) checks that property, and
     @(tsee prog-uniquify-bind-names) establishes it by renaming binds,
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Bind-name uniquification: rename binds so that all bind names in a program
; are distinct, keeping the original names where possible.  A bind keeps its
; name unless that name has already been seen (as an earlier bind name, a
; lambda/unbox/function parameter name, or a free variable name of the
; program); in that case it is renamed to a fresh variant of the name, and the
; renaming is applied to the bind's scope via the renaming operations from
; variable-renaming-operations.lisp.  Since fresh names avoid all names seen
; so far and all free variable names, the renamings cannot capture.

; The five renaming maps, one per variable namespace (dimension and shape
; ispace variables, atom-kind and array-kind type variables, and expression
; variables), bundled so that the traversal threads a single value.

(fty::defprod var-renamings
  :short "Fixtype of renaming maps for all five variable namespaces."
  ((dim acl2::string-string-map)
   (shape acl2::string-string-map)
   (atom acl2::string-string-map)
   (array acl2::string-string-map)
   (expr acl2::string-string-map))
  :pred var-renamings-p)

(define rename-var-string ((name stringp) (renam string-string-mapp))
  :returns (new-name stringp)
  :short "Apply a renaming map to a variable name."
  (b* ((pair (omap::assoc (str-fix name) (string-string-map-fix renam))))
    (if pair (str-fix (cdr pair)) (str-fix name))))

(define fresh-bind-name ((name stringp) (used string-setp))
  :returns (new-name stringp)
  :short "Keep @('name') if it is not in @('used');
          otherwise generate a fresh variant of it."
  :long
  (xdoc::topstring
   (xdoc::p
    "The fresh variant is generated by @(tsee fresh-expr-var), which appends
     a numeric index to the name.  Although that operation is nominally about
     expression variables, it is pure string generation, so we use it for
     bind names of every namespace."))
  (if (set::in (str-fix name) (string-sfix used))
      (fresh-expr-var name used)
    (str-fix name)))

(define string-set-insert-list ((names string-listp) (used string-setp))
  :returns (new-used string-setp)
  :short "Insert a list of names into a set of used names."
  (if (endp names)
      (string-sfix used)
    (string-set-insert-list (cdr names)
                            (set::insert (str-fix (car names))
                                         (string-sfix used)))))

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
; function parameters) are not renamed; their names are added to `used' (so
; later bind names avoid them) and removed from the in-scope renamings (so
; the renamings do not capture them), following the same scoping treatment
; as the renaming folds in variable-renaming-operations.lisp.

(defines uniquify-bind-names-impl
  :verify-guards :after-returns
  :ruler-extenders :all

  (define uniq-expr ((x exprp) (used string-setp) (r var-renamings-p))
    :short "Uniquify bind names in an expression."
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
                  ;; ispaces, so we rename it under the unreduced renamings.
                  (new-type? (type-option-rename-all-vars x.type? r))
                  (used (string-set-insert-list
                         (cons x.var (ispace-var-list->name x.ispaces)) used))
                  ((mv & & dim-renam shape-renam)
                   (dim/shape-rename-remove-bound (set::mergesort x.ispaces)
                                                  r-.dim r-.shape))
                  (expr-renam (omap::delete (str-fix x.var)
                                            (string-string-map-fix r-.expr)))
                  (body-r (change-var-renamings r
                                                :dim dim-renam
                                                :shape shape-renam
                                                :expr expr-renam))
                  ((mv used new-body) (uniq-expr x.body used body-r)))
               (mv used (make-expr-unbox :ispaces x.ispaces
                                         :var x.var
                                         :target new-target
                                         :body new-body
                                         :type? new-type?)))

      :bracket (b* (((mv used new-es) (uniq-expr-list x.exprs used r)))
                 (mv used (expr-bracket new-es)))

      :let (b* (((mv used new-binds new-r) (uniq-bind-list x.binds used r))
                ((mv used new-body) (uniq-expr x.body used new-r)))
             (mv used (expr-let new-binds new-body)))))

  (define uniq-expr-list ((x expr-listp) (used string-setp) (r var-renamings-p))
    :short "Uniquify bind names in a list of expressions."
    :returns (mv (new-used string-setp :hyp :guard)
                 (new-x expr-listp :hyp :guard))
    :measure (expr-list-count x)
    (if (endp x)
        (mv used nil)
      (b* (((mv used new-e) (uniq-expr (car x) used r))
           ((mv used new-rest) (uniq-expr-list (cdr x) used r)))
        (mv used (cons new-e new-rest)))))

  (define uniq-atom ((x atomp) (used string-setp) (r var-renamings-p))
    :short "Uniquify bind names in an atom."
    :returns (mv (new-used string-setp :hyp :guard)
                 (new-x atomp :hyp :guard))
    :measure (atom-count x)
    (atom-case x
      :base (mv used (atom-fix x))

      :lambda (b* (((var-renamings r-) r)
                   (new-params (var+type?-list-rename-all-vars x.params r))
                   (new-type? (type-option-rename-all-vars x.type? r))
                   (param-names (var+type?-list->var x.params))
                   (used (string-set-insert-list param-names used))
                   (expr-renam (omap::delete* (set::mergesort param-names)
                                              (string-string-map-fix r-.expr)))
                   ((mv used new-body)
                    (uniq-expr x.body used
                               (change-var-renamings r :expr expr-renam))))
                (mv used (make-atom-lambda :params new-params
                                           :body new-body
                                           :type? new-type?)))

      :tlambda (b* (((var-renamings r-) r)
                    (used (string-set-insert-list
                           (type-var-list->name x.params) used))
                    ((mv & & atom-renam array-renam)
                     (atom/array-rename-remove-bound (set::mergesort x.params)
                                                     r-.atom r-.array))
                    ((mv used new-body)
                     (uniq-expr x.body used
                                (change-var-renamings r
                                                      :atom atom-renam
                                                      :array array-renam))))
                 (mv used (atom-tlambda x.params new-body)))

      :ilambda (b* (((var-renamings r-) r)
                    (used (string-set-insert-list
                           (ispace-var-list->name x.params) used))
                    ((mv & & dim-renam shape-renam)
                     (dim/shape-rename-remove-bound (set::mergesort x.params)
                                                    r-.dim r-.shape))
                    ((mv used new-body)
                     (uniq-expr x.body used
                                (change-var-renamings r
                                                      :dim dim-renam
                                                      :shape shape-renam))))
                 (mv used (atom-ilambda x.params new-body)))

      :box (b* (((var-renamings r-) r)
                ((mv used new-array) (uniq-expr x.array used r)))
             (mv used (atom-box (ispace-list-rename-ispace-vars
                                 x.ispaces r-.dim r-.shape)
                                new-array
                                (type-rename-all-vars x.type r))))))

  (define uniq-atom-list ((x atom-listp) (used string-setp) (r var-renamings-p))
    :short "Uniquify bind names in a list of atoms."
    :returns (mv (new-used string-setp :hyp :guard)
                 (new-x atom-listp :hyp :guard))
    :measure (atom-list-count x)
    (if (endp x)
        (mv used nil)
      (b* (((mv used new-a) (uniq-atom (car x) used r))
           ((mv used new-rest) (uniq-atom-list (cdr x) used r)))
        (mv used (cons new-a new-rest)))))

  (define uniq-bind ((x bindp) (used string-setp) (r var-renamings-p))
    :short "Uniquify bind names in a bind, renaming the bind itself
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
                   (new-name (fresh-bind-name name used))
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
                 (new-name (fresh-bind-name name used))
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
                (new-name (fresh-bind-name x.var used))
                (used (set::insert new-name (string-sfix used)))
                (new-r (change-var-renamings
                        r :expr (extend-renaming x.var new-name r-.expr))))
             (mv used (bind-val new-name new-type? new-expr) new-r))

      :fun (b* (((var-renamings r-) r)
                (new-params (var+type?-list-rename-all-vars x.params r))
                (new-type? (type-option-rename-all-vars x.type? r))
                (param-names (var+type?-list->var x.params))
                (used (string-set-insert-list param-names used))
                (expr-renam (omap::delete* (set::mergesort param-names)
                                           (string-string-map-fix r-.expr)))
                ((mv used new-expr)
                 (uniq-expr x.expr used
                            (change-var-renamings r :expr expr-renam)))
                (new-name (fresh-bind-name x.var used))
                (used (set::insert new-name (string-sfix used)))
                (new-r (change-var-renamings
                        r :expr (extend-renaming x.var new-name r-.expr))))
             (mv used (bind-fun new-name new-params new-type? new-expr) new-r))

      :tfun (b* (((var-renamings r-) r)
                 (used (string-set-insert-list
                        (type-var-list->name x.params) used))
                 ((mv & & atom-renam array-renam)
                  (atom/array-rename-remove-bound (set::mergesort x.params)
                                                  r-.atom r-.array))
                 (inner-r (change-var-renamings r
                                                :atom atom-renam
                                                :array array-renam))
                 (new-type? (type-option-rename-all-vars x.type? inner-r))
                 ((mv used new-expr) (uniq-expr x.expr used inner-r))
                 (new-name (fresh-bind-name x.var used))
                 (used (set::insert new-name (string-sfix used)))
                 (new-r (change-var-renamings
                         r :expr (extend-renaming x.var new-name r-.expr))))
              (mv used (bind-tfun new-name x.params new-type? new-expr) new-r))

      :ifun (b* (((var-renamings r-) r)
                 (used (string-set-insert-list
                        (ispace-var-list->name x.params) used))
                 ((mv & & dim-renam shape-renam)
                  (dim/shape-rename-remove-bound (set::mergesort x.params)
                                                 r-.dim r-.shape))
                 (inner-r (change-var-renamings r
                                                :dim dim-renam
                                                :shape shape-renam))
                 (new-type? (type-option-rename-all-vars x.type? inner-r))
                 ((mv used new-expr) (uniq-expr x.expr used inner-r))
                 (new-name (fresh-bind-name x.var used))
                 (used (set::insert new-name (string-sfix used)))
                 (new-r (change-var-renamings
                         r :expr (extend-renaming x.var new-name r-.expr))))
              (mv used (bind-ifun new-name x.params new-type? new-expr) new-r))

      :cfun (b* (((var-renamings r-) r)
                 (tparams (type-var-list-option-case x.tparams?
                            :some x.tparams?.val :none nil))
                 (iparams (ispace-var-list-option-case x.iparams?
                            :some x.iparams?.val :none nil))
                 (used (string-set-insert-list
                        (type-var-list->name tparams) used))
                 (used (string-set-insert-list
                        (ispace-var-list->name iparams) used))
                 ((mv & & atom-renam array-renam)
                  (atom/array-rename-remove-bound (set::mergesort tparams)
                                                  r-.atom r-.array))
                 ((mv & & dim-renam shape-renam)
                  (dim/shape-rename-remove-bound (set::mergesort iparams)
                                                 r-.dim r-.shape))
                 (inner-r (change-var-renamings r
                                                :dim dim-renam
                                                :shape shape-renam
                                                :atom atom-renam
                                                :array array-renam))
                 (new-params (var+type?-list-rename-all-vars x.params inner-r))
                 (new-type (type-rename-all-vars x.type inner-r))
                 (param-names (var+type?-list->var x.params))
                 (used (string-set-insert-list param-names used))
                 (expr-renam (omap::delete*
                              (set::mergesort param-names)
                              (string-string-map-fix
                               (var-renamings->expr inner-r))))
                 ((mv used new-expr)
                  (uniq-expr x.expr used
                             (change-var-renamings inner-r :expr expr-renam)))
                 (new-name (fresh-bind-name x.var used))
                 (used (set::insert new-name (string-sfix used)))
                 (new-r (change-var-renamings
                         r :expr (extend-renaming x.var new-name r-.expr))))
              (mv used
                  (make-bind-cfun :var new-name
                                  :tparams? x.tparams?
                                  :iparams? x.iparams?
                                  :params new-params
                                  :type new-type
                                  :expr new-expr)
                  new-r))))

  (define uniq-bind-list ((x bind-listp) (used string-setp) (r var-renamings-p))
    :short "Uniquify bind names in a list of binds, threading the renamings
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
  :short "Rename binds so that all bind names in a program are distinct,
          keeping the original names where possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "Traverses the program left-to-right, accumulating the set of names seen
     so far, initialized with the names of the program's free variables in
     all namespaces (so that no bind is renamed to, or left colliding with,
     e.g. a built-in function name).  A bind whose name has not been seen
     keeps it; otherwise the bind is renamed to a fresh variant of its name
     (the name with a numeric suffix), and the renaming is applied throughout
     the bind's scope.  Parameter-like binders (lambda/unbox/function
     parameters) are not renamed, but their names are also avoided by
     the generated names.")
   (xdoc::p
    "Afterwards @(tsee prog-duplicate-bind-names) returns @('nil'), and no
     bind name coincides with a free variable name of the program or with a
     parameter name seen before the bind."))
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
       (r (make-var-renamings :dim nil :shape nil :atom nil :array nil
                              :expr nil))
       ((mv & new-expr) (uniq-expr (prog->expr prog) used r)))
    (make-prog :expr new-expr)))
