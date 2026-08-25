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
(include-book "all-variable-operations")
(include-book "fresh-variable-operations")
(include-book "variable-renaming-operations")
(include-book "osets")

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(include-book "portcullis")
(local (include-book "std/omaps/top" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "kestrel/utilities/lists/len-const-theorems" :dir :system))

; The SUBSETP-EQUAL reasoning used below is supplied by KESTREL/LISTS-LIGHT
; rather than proved here.  That book carries some fifty rules, all enabled,
; which the large traversal proofs below were not tuned for (and several of
; which -- transitivity, right-monotonicity, membership transport -- have
; free variables and are far too expensive as blanket rewrites).  So we take
; from it only the three rules we want enabled globally, leaving the rest
; disabled; the free-variable ones are switched on in the individual hints
; that need them, exactly as the local rules they replace were.

(local (deftheory theory-before-lists-light (current-theory :here)))

(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/intersectp-equal" :dir :system))

(local (in-theory
        (union-theories (theory 'theory-before-lists-light)
                              '(acl2::subsetp-equal-self
                                acl2::subsetp-equal-of-append
                                acl2::subsetp-equal-of-cons-arg1
                                acl2::intersectp-equal-of-nil-arg2
                                acl2::intersectp-equal-of-cons-arg2
                                acl2::intersectp-equal-of-append-arg1
                                acl2::intersectp-equal-of-append-arg2
                                acl2::no-duplicatesp-equal-of-append-alt))))

; The tau system contributes to no proof in this book: the reasoning here is
; about list membership, containment, and disjointness, none of which tau
; handles.  Running it on every goal of the large traversal proofs below is
; therefore pure overhead, so we turn it off.  This must come after the
; THEORY-BEFORE-LISTS-LIGHT restore above, which would otherwise put it back.
(local (in-theory (disable (:e tau-system))))

; USED is now a CONS-built list, which wakes up the SET-EQUIV congruence
; machinery from STD/LISTS/SETS -- including two permutative commutativity
; rules on APPEND.  None of it contributes here (the reasoning is ordinary
; SUBSETP-EQUAL/INTERSECTP-EQUAL), and it cost several seconds in the
; identity proof, so it is turned off.
(local (in-theory
        (disable acl2::append-of-cons-under-set-equiv
                       acl2::commutativity-of-append-under-set-equiv
                       acl2::commutativity-2-of-append-under-set-equiv
                       acl2::set-equiv-implies-set-equiv-cons-2
                       acl2::set-equiv-implies-set-equiv-append-2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unique-names
  :parents (remora)
  :short "Detection of duplicate bind names in Remora ASTs,
          and renaming of binds to make all bind names unique."
  :long
  (xdoc::topstring
   (xdoc::p
    "Transformations that substitute variables without regard to shadowing
     (e.g. the maps applied by @(see monomorphize)) are only safe when the
     names introduced by binders are unique.  @(tsee expr-duplicate-names)
     checks that property for all binders (binds as well as lambda, unbox,
     and function-bind parameters), and @(tsee expr-uniquify-names)
     establishes it by renaming binds and parameters, keeping the original
     names where possible
     (proved as @(tsee expr-duplicate-names-of-expr-uniquify-names)).")
   (xdoc::p
    "The uniquification is also the identity on an expression that already
     has the property, provided no binder name is also a free variable name
     of the expression: see
     @(tsee expr-uniquify-names-when-no-duplicate-names)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Duplicate binder-name detection.

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

(defrule bind-name-of-bind-fix
  :parents (bind-name)
  (equal (bind-name (bind-fix b))
         (bind-name b))
  :enable bind-name)

(defrule bind-list-names-of-bind-list-fix
  :parents (bind-list-names)
  (equal (bind-list-names (bind-list-fix binds))
         (bind-list-names binds))
  :induct (len binds)
  :enable (bind-list-names bind-list-fix))

; Fold: collect the names of all binders (bind names as well as parameter
; names of lambdas, unboxes, and function binds) occurring anywhere in an
; AST, so that the uniqueness of all binder names can be checked.

(fty::deffold-reduce binder-names
  :short "Collect the names of all binders occurring in an AST:
          bind names and parameter names."
  :types (exprs/atoms/binds)
  :result string-listp
  :default nil
  :combine append
  :override
  ((expr :let (append (bind-list-names expr.binds)
                      (append (bind-list-binder-names expr.binds)
                              (expr-binder-names expr.body))))
   (expr :unbox (cons expr.var
                      (append (ispace-var-list->name (list expr.ispace))
                              (append (expr-binder-names expr.target)
                                      (expr-binder-names expr.body)))))
   (expr :unboxn (cons expr.var
                       (append (ispace-var-list->name expr.ispaces)
                               (append (expr-binder-names expr.target)
                                       (expr-binder-names expr.body)))))
   (atom :lambda (cons (var+type?->var atom.param)
                       (expr-binder-names atom.body)))
   (atom :lambdan (append (var+type?-list->var atom.params)
                          (expr-binder-names atom.body)))
   (atom :tlambda (cons (type-var->name atom.param)
                        (expr-binder-names atom.body)))
   (atom :tlambdan (append (type-var-list->name atom.params)
                           (expr-binder-names atom.body)))
   (atom :ilambda (cons (ispace-var->name atom.param)
                        (expr-binder-names atom.body)))
   (atom :ilambdan (append (ispace-var-list->name atom.params)
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

(define expr-duplicate-names ((expr exprp))
  :returns (dup-names string-listp)
  :short "List the names bound by more than one binder
          (bind or parameter) in an expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "Returns @('nil') if all binders in the expression bind distinct names;
     otherwise returns the duplicated names (a name bound @('n') times is
     listed @('n - 1') times).
     After @(tsee expr-uniquify-names) this returns @('nil'): see
     @(tsee expr-duplicate-names-of-expr-uniquify-names)."))
  (duplicated-names (expr-binder-names expr))
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

; Binder-name uniquification: rename binds and parameters so that all binder
; names in an expression are distinct, keeping the original names where possible.
; A binder (a bind, or a parameter of a lambda, unbox, or function bind)
; keeps its name unless that name has already been seen (as an earlier
; binder name or a free variable name of the expression); in that case it is
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
     variable names occurring anywhere in the expression (in any namespace and
     any role), fixed throughout the traversal.  Freshly generated bind
     names must avoid it, so that they can never capture (or be captured
     by) an occurrence of an existing name --- in particular one whose
     binder has not been encountered yet, such as a parameter of a lambda
     abstraction later in the expression."))
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

(define fresh-bind-name ((name stringp) (used string-listp) (avoid string-setp))
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
     all names occurring anywhere in the expression (@('avoid')), so that it
     cannot capture, or be captured by, any binder --- including binders not
     yet encountered by the traversal.")
   (xdoc::p
    "@('used') is a plain list, so the membership test is @(tsee member-equal);
     only the collision branch needs a set, for @(tsee fresh-expr-var), and it
     builds one there.  That branch is the rare one --- it runs only when a
     name actually collides."))
  (if (member-equal (str-fix name) (str::string-list-fix used))
      (fresh-expr-var name (set::union (list-to-oset (str::string-list-fix used))
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

; Support lemmas for the no-duplicate-names theorem about PROG-UNIQUIFY-NAMES
; (see the DEFRET-MUTUAL further below for the overall proof plan).
; Everything here is about plain-list membership, subset, disjointness, and
; duplicate-freeness over the USED values that the traversal threads.  USED
; is a plain list grown by CONS, so no oset/list bridge lemmas are needed:
; the CONS decompositions come straight from KESTREL/LISTS-LIGHT and the
; INTERSECTP-EQUAL book.

; Monotonicity of (non-)intersection in a subset, in the three orientations
; used below (which argument of INTERSECTP-EQUAL the known-disjoint bigger
; set occupies in the hypothesis, and which the smaller set occupies in the
; conclusion).
; The free variable BIG is matched against an available disjointness
; hypothesis.  In the traversal proof below, BIG is always a USED value that
; a sub-computation's names are known disjoint from, and SMALL is either an
; earlier USED value or an earlier sub-computation's names (both of which
; the invariant places inside that USED value).

; The corresponding single-element facts -- an element of a set known
; disjoint from L is not in L, and non-membership transports along subsets --
; come from KESTREL/LISTS-LIGHT, as do the INTERSECTP monotonicity rules:
; NOT-MEMBER-EQUAL-WHEN-NOT-INTERSECTP-EQUAL and the two orderings
; NOT-MEMBER-EQUAL-WHEN-SUBSETP-EQUAL-1 (containment hypothesis first, which
; is what the identity proof below needs, since there BIG is an
; (APPEND USED NAMES) that never appears in a non-membership hypothesis)
; and ...-2.

(defrule not-member-equal-of-fresh-bind-name
  :parents (fresh-bind-name)
  :short "@(tsee fresh-bind-name) never returns a name already in @('used')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The freshness of @(tsee fresh-expr-var) is stated with @(tsee set::in)
     over the set it is given; SET::UNION-IN and SET::IN-MERGESORT carry it
     back to @(tsee member-equal) on the list, so no bridge lemma of our own
     is needed."))
  (not (member-equal (fresh-bind-name name used avoid)
                     (str::string-list-fix used)))
  :enable (fresh-bind-name set::union-in)
  :use (:instance fresh-expr-var-is-fresh
                  (prefix name)
                  (used (set::union (list-to-oset (str::string-list-fix used))
                                    (string-sfix avoid)))))

(defrule not-member-equal-of-fresh-bind-name-when-subsetp-equal
  :parents (fresh-bind-name)
  :short "@(tsee fresh-bind-name) never returns a name already in any subset
          of @('used'), such as the names contributed by an earlier
          sub-computation.  Free-variable-free: @('used') is bound by the
          conclusion and the subset hypothesis is relieved by rewriting."
  (implies (subsetp-equal l (str::string-list-fix used))
           (not (member-equal (fresh-bind-name name used avoid) l)))
  :use (:instance acl2::not-member-equal-when-subsetp-equal-2
                  (a (fresh-bind-name name used avoid))
                  (big (str::string-list-fix used))
                  (small l)))

; The dual facts, for the identity proof below: nothing is renamed when no
; binder name has been seen before, i.e. a binder keeps its name, the
; renaming maps stay empty, and applying an empty renaming changes nothing.

(defrule fresh-bind-name-when-not-member
  :parents (fresh-bind-name)
  :short "@(tsee fresh-bind-name) keeps the name it is given
          when that name is not in @('used')."
  (implies (not (member-equal (str-fix name) (str::string-list-fix used)))
           (equal (fresh-bind-name name used avoid) (str-fix name)))
  :enable fresh-bind-name)

; That (OMAP::DELETE key NIL) and (OMAP::DELETE* keys NIL) are NIL is
; supplied by OMAP::DELETE-WHEN-EMPTYP and OMAP::DELETE*-WHEN-RIGHT-EMPTYP
; from STD/OMAPS.

(defrule rename-var-string-when-empty
  :parents (rename-var-string)
  :short "The empty renaming map leaves a variable name unchanged."
  (equal (rename-var-string name nil) (str-fix name))
  :enable rename-var-string)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uniq-expr-params ((params var+type?-listp)
                          (used string-listp)
                          (avoid string-setp)
                          (renam string-string-mapp))
  :returns (mv (new-used string-listp :hyp :guard)
               (new-params var+type?-listp :hyp :guard)
               (new-renam string-string-mapp :hyp :guard))
  :short "Uniquify the names of a list of expression-variable parameters.
          The types in the parameters must have been renamed already."
  (b* (((when (endp params))
        (mv (str::string-list-fix used) nil (string-string-map-fix renam)))
       ((var+type? p) (car params))
       (new-name (fresh-bind-name p.var used avoid))
       (used (cons new-name (str::string-list-fix used)))
       (renam (extend-renaming p.var new-name renam))
       ((mv used new-rest renam)
        (uniq-expr-params (cdr params) used avoid renam)))
    (mv used
        (cons (make-var+type? :var new-name :type? p.type?) new-rest)
        renam)))

(define uniq-type-var-params ((params type-var-listp)
                              (used string-listp)
                              (avoid string-setp)
                              (atom-renam string-string-mapp)
                              (array-renam string-string-mapp))
  :returns (mv (new-used string-listp :hyp :guard)
               (new-params type-var-listp :hyp :guard)
               (new-atom-renam string-string-mapp :hyp :guard)
               (new-array-renam string-string-mapp :hyp :guard))
  :short "Uniquify the names of a list of type-variable parameters."
  (b* (((when (endp params))
        (mv (str::string-list-fix used) nil
            (string-string-map-fix atom-renam)
            (string-string-map-fix array-renam)))
       (var (car params))
       (name (type-var->name var))
       (new-name (fresh-bind-name name used avoid))
       (used (cons new-name (str::string-list-fix used)))
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
                                (used string-listp)
                                (avoid string-setp)
                                (dim-renam string-string-mapp)
                                (shape-renam string-string-mapp))
  :returns (mv (new-used string-listp :hyp :guard)
               (new-params ispace-var-listp :hyp :guard)
               (new-dim-renam string-string-mapp :hyp :guard)
               (new-shape-renam string-string-mapp :hyp :guard))
  :short "Uniquify the names of a list of ispace-variable parameters."
  (b* (((when (endp params))
        (mv (str::string-list-fix used) nil
            (string-string-map-fix dim-renam)
            (string-string-map-fix shape-renam)))
       (var (car params))
       (name (ispace-var->name var))
       (new-name (fresh-bind-name name used avoid))
       (used (cons new-name (str::string-list-fix used)))
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
    (mv used (cons new-var new-rest) dim-renam shape-renam))

  ///

  (defret len-of-uniq-ispace-var-params
    (equal (len new-params) (len params))
    :hints (("Goal" :induct t
                    :in-theory (enable len))))

  (defret true-listp-of-uniq-ispace-var-params
    (true-listp new-params)
    :rule-classes :type-prescription
    :hints (("Goal" :induct t)))

  (defret consp-of-uniq-ispace-var-params
    (implies (consp params)
             (consp new-params)))
  ) ; uniq-ispace-var-params

; All three parameter uniquification functions above freshen their
; parameters' names in exactly the same way: a name is kept if it has not
; been seen and is otherwise replaced by a fresh variant, and it is added to
; USED before the next parameter is processed.  Only the payload differs (an
; expression variable with an optional type, a type variable, an ispace
; variable), and the payload plays no part in the freshness and USED-growth
; reasoning that the traversal proofs below need.
;
; That common behavior is therefore factored into UNIQ-NAME-LIST, which
; freshens a bare list of names.  The facts are proved once about it, and
; each parameter function is connected to it by a bridge rule rewriting the
; function's USED result, and the names of its result list, into the
; corresponding UNIQ-NAME-LIST terms.  Everything the traversal proofs need
; about the three functions then follows from the single set of rules below,
; rather than being restated once per function.

(define uniq-name-list ((names string-listp)
                        (used string-listp)
                        (avoid string-setp))
  :returns (mv (new-used string-listp :hyp :guard)
               (new-names string-listp))
  :short "Freshen a list of binder names,
          threading the set of names seen so far."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is the common core of @(tsee uniq-expr-params),
     @(tsee uniq-type-var-params), and @(tsee uniq-ispace-var-params).
     Each name is kept if it has not been seen and is otherwise replaced by
     a fresh variant, and is added to the set of seen names before the next
     name is processed; so duplicate names within a single list are made
     distinct too."))
  (b* (((when (endp names)) (mv (str::string-list-fix used) nil))
       (new-name (fresh-bind-name (car names) used avoid))
       (used (cons new-name (str::string-list-fix used)))
       ((mv used new-rest) (uniq-name-list (cdr names) used avoid)))
    (mv used (cons new-name new-rest)))

  ///

; The bridges.  Each parameter function returns the same USED as
; UNIQ-NAME-LIST run on its parameters' names, and its result list has those
; names; the renaming maps it also returns are irrelevant here.

  (defrule uniq-expr-params-to-uniq-name-list
    :parents (uniq-expr-params)
    :short "@(tsee uniq-expr-params) freshens names as @(tsee uniq-name-list)."
    (and (equal (mv-nth 0 (uniq-expr-params params used avoid renam))
                (mv-nth 0 (uniq-name-list (var+type?-list->var params)
                                          used avoid)))
         (equal (var+type?-list->var
                  (mv-nth 1 (uniq-expr-params params used avoid renam)))
                (mv-nth 1 (uniq-name-list (var+type?-list->var params)
                                          used avoid))))
    :induct (uniq-expr-params params used avoid renam)
    :enable (uniq-expr-params var+type?-list->var))

  (defrule uniq-type-var-params-to-uniq-name-list
    :parents (uniq-type-var-params)
    :short "@(tsee uniq-type-var-params) freshens names as
          @(tsee uniq-name-list)."
    (and (equal (mv-nth 0 (uniq-type-var-params params used avoid
                                                atom-renam array-renam))
                (mv-nth 0 (uniq-name-list (type-var-list->name params)
                                          used avoid)))
         (equal (type-var-list->name
                  (mv-nth 1 (uniq-type-var-params params used avoid
                                                  atom-renam array-renam)))
                (mv-nth 1 (uniq-name-list (type-var-list->name params)
                                          used avoid))))
    :induct (uniq-type-var-params params used avoid atom-renam array-renam)
    :enable (uniq-type-var-params type-var-list->name type-var->name))

  (defrule uniq-ispace-var-params-to-uniq-name-list
    :parents (uniq-ispace-var-params)
    :short "@(tsee uniq-ispace-var-params) freshens names as
          @(tsee uniq-name-list)."
    (and (equal (mv-nth 0 (uniq-ispace-var-params params used avoid
                                                  dim-renam shape-renam))
                (mv-nth 0 (uniq-name-list (ispace-var-list->name params)
                                          used avoid)))
         (equal (ispace-var-list->name
                  (mv-nth 1 (uniq-ispace-var-params params used avoid
                                                    dim-renam shape-renam)))
                (mv-nth 1 (uniq-name-list (ispace-var-list->name params)
                                          used avoid))))
    :induct (uniq-ispace-var-params params used avoid dim-renam shape-renam)
    :enable (uniq-ispace-var-params ispace-var-list->name ispace-var->name))

; Freshness and USED-growth facts, in the four-conjunct form that the main
; traversal's DEFRET-MUTUAL below uses uniformly: the produced names are
; duplicate-free and disjoint from the incoming USED, they are contained in
; the returned USED, and the incoming USED is contained in the returned
; USED.  Containments are stated with both sides under STRING-SFIX, since
; the return-type theorems of the traversal functions are guard-conditional
; and so the (unconditional) facts here cannot assume set-ness of raw
; values.

  (defret uniq-name-list-facts
    (and (no-duplicatesp-equal new-names)
         (not (intersectp-equal new-names (str::string-list-fix used)))
         (subsetp-equal new-names (str::string-list-fix new-used))
         (subsetp-equal (str::string-list-fix used) (str::string-list-fix new-used)))
    :hints (("Goal" :induct t
                    :in-theory (enable intersectp-equal
                                       not-member-equal-of-fresh-bind-name
                                       acl2::not-member-equal-when-not-intersectp-equal
                                       acl2::not-intersectp-equal-when-subsetp-equal-arg2))))

; The dual upper bound: USED grows only by the names just processed.  This
; needs the names to be strings, since a name that is kept is returned as
; itself; in every use below the list is a projection whose return type
; supplies that.

  (defret uniq-name-list-used-upper-bound
    (implies (and (string-listp names)
                  (no-duplicatesp-equal names)
                  (not (intersectp-equal names (str::string-list-fix used))))
             (subsetp-equal (str::string-list-fix new-used)
                            (append (str::string-list-fix used) names)))
    :hints (("Goal" :induct t
                    :in-theory (enable intersectp-equal
                                       no-duplicatesp-equal
                                       acl2::subsetp-equal-of-append-2-2
                                       acl2::subsetp-equal-of-append-2-1
                                       acl2::subsetp-equal-of-cons-arg2
                                       acl2::subsetp-equal-transitive-alt
                                       acl2::subsetp-equal-transitive-2-alt))))
  ) ; uniq-name-list

; Free-variable-free consequences of the two facts above, phrased so that
; the UNIQ-NAME-LIST call (and hence its USED argument) appears in the
; conclusion, with all remaining hypotheses relievable by rewriting.  These
; are needed because the facts above are rewrite rules rather than
; hypotheses of the main traversal's induction, so the free-variable
; monotonicity rules cannot bind their free variable to them: anything
; inside the incoming USED stays inside the returned USED, and is disjoint
; (in both argument orders) from the freshly chosen names.

(defrule subsetp-equal-through-uniq-name-list
  (implies (subsetp-equal l (str::string-list-fix used))
           (subsetp-equal
             l (str::string-list-fix (mv-nth 0 (uniq-name-list names used avoid)))))
  :use (:instance acl2::subsetp-equal-transitive-alt
                  (x l) (y (str::string-list-fix used))
                  (z (str::string-list-fix
                       (mv-nth 0 (uniq-name-list names used avoid))))))

(defrule not-intersectp-equal-of-uniq-name-list-names-1
  (implies (subsetp-equal l (str::string-list-fix used))
          (not (intersectp-equal
                (mv-nth 1 (uniq-name-list names used avoid))
                l)))
  :use (:instance acl2::not-intersectp-equal-when-subsetp-equal-arg2
                  (x (mv-nth 1 (uniq-name-list names used avoid)))
                  (big (str::string-list-fix used))
                  (small l)))

(defrule not-intersectp-equal-of-uniq-name-list-names-2
  (implies (subsetp-equal l (str::string-list-fix used))
          (not (intersectp-equal
                l
                (mv-nth 1 (uniq-name-list names used avoid)))))
  :use (:instance acl2::not-intersectp-equal-when-subsetp-equal-arg1-alt
                  (x (mv-nth 1 (uniq-name-list names used avoid)))
                  (big (str::string-list-fix used))
                  (small l)))

(defrule not-intersectp-equal-of-uniq-name-list-new-used
  (implies (and (string-listp names)
                (no-duplicatesp-equal names)
                (not (intersectp-equal names (str::string-list-fix used)))
                (not (intersectp-equal l (str::string-list-fix used)))
                (not (intersectp-equal l names)))
           (and (not (intersectp-equal
                      l
                      (str::string-list-fix
                       (mv-nth 0 (uniq-name-list names used avoid)))))
                (not (intersectp-equal
                      (str::string-list-fix
                       (mv-nth 0 (uniq-name-list names used avoid)))
                      l))))
  :use (uniq-name-list-used-upper-bound
        (:instance acl2::not-intersectp-equal-when-subsetp-equal-arg2
                   (x l)
                   (big (append (str::string-list-fix used) names))
                   (small (str::string-list-fix
                           (mv-nth 0 (uniq-name-list names used avoid)))))
        (:instance acl2::not-intersectp-equal-when-subsetp-equal-arg1-alt
                   (x l)
                   (big (append (str::string-list-fix used) names))
                   (small (str::string-list-fix
                           (mv-nth 0 (uniq-name-list names used avoid))))))
  :disable uniq-name-list-used-upper-bound)

(defrule not-member-equal-of-uniq-name-list-new-used
  (implies (and (string-listp names)
                (no-duplicatesp-equal names)
                (not (intersectp-equal names (str::string-list-fix used)))
                (not (member-equal a (str::string-list-fix used)))
                (not (member-equal a names)))
           (not (member-equal
                 a
                 (str::string-list-fix (mv-nth 0 (uniq-name-list names used avoid))))))
  :use (uniq-name-list-used-upper-bound
        (:instance acl2::not-member-equal-when-subsetp-equal-2
                   (big (append (str::string-list-fix used) names))
                   (small (str::string-list-fix
                           (mv-nth 0 (uniq-name-list names used avoid))))))
  :disable uniq-name-list-used-upper-bound)

(defrule subsetp-equal-of-uniq-name-list-new-used
  (implies (and (string-listp names)
                (no-duplicatesp-equal names)
                (not (intersectp-equal names (str::string-list-fix used)))
                (subsetp-equal (str::string-list-fix used) l)
                (subsetp-equal names l))
           (subsetp-equal
            (str::string-list-fix (mv-nth 0 (uniq-name-list names used avoid)))
            l))
  :use (uniq-name-list-used-upper-bound
        (:instance acl2::subsetp-equal-transitive-alt
                   (x (str::string-list-fix
                       (mv-nth 0 (uniq-name-list names used avoid))))
                   (y (append (str::string-list-fix used) names))
                   (z l)))
  :disable uniq-name-list-used-upper-bound)

; Variants of the two pass-through rules above phrased against an arbitrary
; superset BIG of the incoming USED (a free variable, matched against a
; containment hypothesis).  Without these, the corresponding facts about the
; incoming USED would have to be derived by a further level of backchaining
; through the monotonicity rules, which ACL2's ancestors check refuses.
; These are what the :UNBOX and :UNBOXN cases of the identity proof require,
; where the incoming USED is itself the result of traversing the unboxed
; target and so is known only through a containment.

(defrule not-member-equal-of-uniq-name-list-new-used-b
  (implies (and (subsetp-equal (str::string-list-fix used) big)
                (string-listp names)
                (no-duplicatesp-equal names)
                (not (intersectp-equal names big))
                (not (member-equal a big))
                (not (member-equal a names)))
           (not (member-equal
                 a
                 (str::string-list-fix (mv-nth 0 (uniq-name-list names used avoid))))))
  :rule-classes ((:rewrite :match-free :all))
  :use ((:instance acl2::not-intersectp-equal-when-subsetp-equal-arg2
                   (x names) (big big) (small (str::string-list-fix used)))
        (:instance acl2::not-member-equal-when-subsetp-equal-2
                   (a a) (big big) (small (str::string-list-fix used)))
        uniq-name-list-used-upper-bound
        (:instance acl2::not-member-equal-when-subsetp-equal-2
                   (a a)
                   (big (append (str::string-list-fix used) names))
                   (small (str::string-list-fix
                           (mv-nth 0 (uniq-name-list names used avoid))))))
  :disable uniq-name-list-used-upper-bound)

(defrule not-intersectp-equal-of-uniq-name-list-new-used-b
  (implies (and (subsetp-equal (str::string-list-fix used) big)
                (string-listp names)
                (no-duplicatesp-equal names)
                (not (intersectp-equal names big))
                (not (intersectp-equal l big))
                (not (intersectp-equal l names)))
           (and (not (intersectp-equal
                      l
                      (str::string-list-fix
                       (mv-nth 0 (uniq-name-list names used avoid)))))
                (not (intersectp-equal
                      (str::string-list-fix
                       (mv-nth 0 (uniq-name-list names used avoid)))
                      l))))
  :rule-classes ((:rewrite :match-free :all))
  :use ((:instance acl2::not-intersectp-equal-when-subsetp-equal-arg2
                   (x names) (big big) (small (str::string-list-fix used)))
        (:instance acl2::not-intersectp-equal-when-subsetp-equal-arg2
                   (x l) (big big) (small (str::string-list-fix used)))
        uniq-name-list-used-upper-bound
        (:instance acl2::not-intersectp-equal-when-subsetp-equal-arg2
                   (x l)
                   (big (append (str::string-list-fix used) names))
                   (small (str::string-list-fix
                           (mv-nth 0 (uniq-name-list names used avoid)))))
        (:instance acl2::not-intersectp-equal-when-subsetp-equal-arg1-alt
                   (x l)
                   (big (append (str::string-list-fix used) names))
                   (small (str::string-list-fix
                           (mv-nth 0 (uniq-name-list names used avoid))))))
  :disable uniq-name-list-used-upper-bound)


; Identity facts for the three parameter uniquification functions, for the
; identity proof further below: when the incoming renaming map is empty and
; the parameter names are distinct and unseen, every parameter keeps its
; name, so the parameter list and the renaming maps come back unchanged.

(defret uniq-expr-params-identity
  (b* ((names (var+type?-list->var params)))
    (implies (and (equal renam nil)
                  (no-duplicatesp-equal names)
                  (not (intersectp-equal names (str::string-list-fix used))))
             (and (equal new-params (var+type?-list-fix params))
                  (equal new-renam nil))))
  :fn uniq-expr-params
  :hints (("Goal" :induct t
           :in-theory (enable uniq-expr-params
                              var+type?-list->var
                              var+type?-list-fix
                              extend-renaming
                              intersectp-equal
                              no-duplicatesp-equal))))

(defret uniq-type-var-params-identity
  (b* ((names (type-var-list->name params)))
    (implies (and (equal atom-renam nil)
                  (equal array-renam nil)
                  (no-duplicatesp-equal names)
                  (not (intersectp-equal names (str::string-list-fix used))))
             (and (equal new-params (type-var-list-fix params))
                  (equal new-atom-renam nil)
                  (equal new-array-renam nil))))
  :fn uniq-type-var-params
  :hints (("Goal" :induct t
           :in-theory (enable uniq-type-var-params
                              type-var-list->name
                              type-var->name
                              type-var-list-fix
                              extend-renaming
                              intersectp-equal
                              no-duplicatesp-equal))))

(defret uniq-ispace-var-params-identity
  (b* ((names (ispace-var-list->name params)))
    (implies (and (equal dim-renam nil)
                  (equal shape-renam nil)
                  (no-duplicatesp-equal names)
                  (not (intersectp-equal names (str::string-list-fix used))))
             (and (equal new-params (ispace-var-list-fix params))
                  (equal new-dim-renam nil)
                  (equal new-shape-renam nil))))
  :fn uniq-ispace-var-params
  :hints (("Goal" :induct t
           :in-theory (enable uniq-ispace-var-params
                              ispace-var-list->name
                              ispace-var->name
                              ispace-var-list-fix
                              extend-renaming
                              intersectp-equal
                              no-duplicatesp-equal))))

; Under empty renaming maps, all the renaming operations of
; variable-renaming-operations.lisp are the identity.  This is what makes
; the uniquification a no-op on an expression whose binder names are already
; unique: no binder is renamed, so the maps threaded through the traversal
; stay empty, and the maps applied to the type-level components below have
; no effect.  Only the type-level and ispace-level operations are needed:
; the traversal renames expression variables itself rather than through
; EXPR-RENAME-EXPR-VARS.

(defrule dim/shape-rename-remove-bound-when-empty
  (and (equal (mv-nth 2 (dim/shape-rename-remove-bound vars nil nil)) nil)
       (equal (mv-nth 3 (dim/shape-rename-remove-bound vars nil nil)) nil))
  :enable dim/shape-rename-remove-bound)

(defrule atom/array-rename-remove-bound-when-empty
  (and (equal (mv-nth 2 (atom/array-rename-remove-bound vars nil nil)) nil)
       (equal (mv-nth 3 (atom/array-rename-remove-bound vars nil nil)) nil))
  :enable atom/array-rename-remove-bound)

(defret-mutual dim-rename-dim-vars-when-empty
  (defret dim-rename-dim-vars-when-empty
    (implies (equal renam nil)
             (equal result (dim-fix dim)))
    :fn dim-rename-dim-vars)
  (defret dim-list-rename-dim-vars-when-empty
    (implies (equal renam nil)
             (equal result (dim-list-fix dim-list)))
    :fn dim-list-rename-dim-vars)
  :mutual-recursion dims-rename-dim-vars
  :hints (("Goal" :in-theory (enable dim-rename-dim-vars
                                     dim-list-rename-dim-vars))))

(defret-mutual ispace-rename-ispace-vars-when-empty
  (defret shape-rename-ispace-vars-when-empty
    (implies (and (equal dim-renam nil) (equal shape-renam nil))
             (equal result (shape-fix shape)))
    :fn shape-rename-ispace-vars)
  (defret shape-list-rename-ispace-vars-when-empty
    (implies (and (equal dim-renam nil) (equal shape-renam nil))
             (equal result (shape-list-fix shape-list)))
    :fn shape-list-rename-ispace-vars)
  (defret ispace-rename-ispace-vars-when-empty
    (implies (and (equal dim-renam nil) (equal shape-renam nil))
             (equal result (ispace-fix ispace)))
    :fn ispace-rename-ispace-vars)
  (defret ispace-list-rename-ispace-vars-when-empty
    (implies (and (equal dim-renam nil) (equal shape-renam nil))
             (equal result (ispace-list-fix ispace-list)))
    :fn ispace-list-rename-ispace-vars)
  :mutual-recursion shapes/ispaces-rename-ispace-vars
  :hints (("Goal" :in-theory (enable shape-rename-ispace-vars
                                     shape-list-rename-ispace-vars
                                     ispace-rename-ispace-vars
                                     ispace-list-rename-ispace-vars))))

(defret-mutual type-rename-ispace-vars-when-empty
  (defret type-rename-ispace-vars-when-empty
    (implies (and (equal dim-renam nil) (equal shape-renam nil))
             (equal result (type-fix type)))
    :fn type-rename-ispace-vars)
  (defret type-list-rename-ispace-vars-when-empty
    (implies (and (equal dim-renam nil) (equal shape-renam nil))
             (equal result (type-list-fix type-list)))
    :fn type-list-rename-ispace-vars)
  :mutual-recursion types-rename-ispace-vars
  :hints (("Goal" :in-theory (enable type-rename-ispace-vars
                                     type-list-rename-ispace-vars))))

(defret-mutual type-rename-type-vars-when-empty
  (defret type-rename-type-vars-when-empty
    (implies (and (equal atom-renam nil) (equal array-renam nil))
             (equal result (type-fix type)))
    :fn type-rename-type-vars)
  (defret type-list-rename-type-vars-when-empty
    (implies (and (equal atom-renam nil) (equal array-renam nil))
             (equal result (type-list-fix type-list)))
    :fn type-list-rename-type-vars)
  :mutual-recursion types-rename-type-vars
  :hints (("Goal" :in-theory (enable type-rename-type-vars
                                     type-list-rename-type-vars))))

(defrule type-option-rename-ispace-vars-when-empty
  (equal (type-option-rename-ispace-vars type-option nil nil)
         (type-option-fix type-option))
  :enable (type-option-rename-ispace-vars
           type-option-fix type-option-some type-option-some->val))

(defrule type-list-option-rename-ispace-vars-when-empty
  (equal (type-list-option-rename-ispace-vars type-list-option nil nil)
         (type-list-option-fix type-list-option))
  :enable type-list-option-rename-ispace-vars)

(defrule ispace-list-option-rename-ispace-vars-when-empty
  (equal (ispace-list-option-rename-ispace-vars ispace-list-option nil nil)
         (ispace-list-option-fix ispace-list-option))
  :enable ispace-list-option-rename-ispace-vars)

(defrule var+type?-rename-ispace-vars-when-empty
  (equal (var+type?-rename-ispace-vars var+type? nil nil)
         (var+type?-fix var+type?))
  :enable var+type?-rename-ispace-vars)

(defrule var+type?-list-rename-ispace-vars-when-empty
  (equal (var+type?-list-rename-ispace-vars var+type?-list nil nil)
         (var+type?-list-fix var+type?-list))
  :induct t
  :enable (var+type?-list-rename-ispace-vars var+type?-list-fix))

(defrule type-option-rename-type-vars-when-empty
  (equal (type-option-rename-type-vars type-option nil nil)
         (type-option-fix type-option))
  :enable (type-option-rename-type-vars
           type-option-fix type-option-some type-option-some->val))

(defrule type-list-option-rename-type-vars-when-empty
  (equal (type-list-option-rename-type-vars type-list-option nil nil)
         (type-list-option-fix type-list-option))
  :enable type-list-option-rename-type-vars)

(defrule var+type?-rename-type-vars-when-empty
  (equal (var+type?-rename-type-vars var+type? nil nil)
         (var+type?-fix var+type?))
  :enable var+type?-rename-type-vars)

(defrule var+type?-list-rename-type-vars-when-empty
  (equal (var+type?-list-rename-type-vars var+type?-list nil nil)
         (var+type?-list-fix var+type?-list))
  :induct t
  :enable (var+type?-list-rename-type-vars var+type?-list-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
     r.atom r.array))
  ///
  (defret len-of-type-list-rename-all-vars
    (equal (len new-tys)
           (len tys))
    :hints (("Goal" :in-theory (enable len-of-type-list-rename-type-vars
                                       len-of-type-list-rename-ispace-vars)))))

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

; The renaming bundles that occur in the identity proof below are the empty
; ones: no binder is renamed, so no entry is ever added to any of the five
; maps, and all the renamings above are the identity.

(define var-renamings-emptyp ((r var-renamings-p))
  :returns (yes/no booleanp)
  :short "Check that all five renaming maps of a bundle are empty."
  (b* (((var-renamings r) r))
    (and (equal r.dim nil)
         (equal r.shape nil)
         (equal r.atom nil)
         (equal r.array nil)
         (equal r.expr nil)))
  ///

  (defrule type-rename-all-vars-when-empty
    (implies (var-renamings-emptyp r)
             (equal (type-rename-all-vars ty r) (type-fix ty)))
    :enable (type-rename-all-vars))

  (defrule type-option-rename-all-vars-when-empty
    (implies (var-renamings-emptyp r)
             (equal (type-option-rename-all-vars ty? r) (type-option-fix ty?)))
    :enable (type-option-rename-all-vars))

  (defrule type-list-rename-all-vars-when-empty
    (implies (var-renamings-emptyp r)
             (equal (type-list-rename-all-vars tys r) (type-list-fix tys)))
    :enable (type-list-rename-all-vars))

  (defrule type-list-option-rename-all-vars-when-empty
    (implies (var-renamings-emptyp r)
             (equal (type-list-option-rename-all-vars tys? r)
                    (type-list-option-fix tys?)))
    :enable (type-list-option-rename-all-vars))

  (defrule var+type?-list-rename-all-vars-when-empty
    (implies (var-renamings-emptyp r)
             (equal (var+type?-list-rename-all-vars params r)
                    (var+type?-list-fix params)))
    :enable (var+type?-list-rename-all-vars))
  ) ; var-renamings-emptyp

(defruledl list-of-car-when-len-1
  (implies (and (true-listp x)
                (equal (len x) 1))
           (equal (list (car x)) x))
  :enable len)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Main uniquification traversal.
;
; The traversal functions take:
;   x    : AST node          — the node being processed
;   used : string-listp       — all names seen so far (bind names, parameter
;                              names, and the expression's free variable names)
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

; Bridge rule for the :BRACKET case of the traversal facts/identity proofs
; below.  With the non-emptiness invariant on :BRACKET (see EXPR), the
; generated EXPR-BRACKET->EXPRS-of-EXPR-BRACKET accessor rule rewrites to the
; reqfix IF-term rather than the argument, so opening EXPR-BINDER-NAMES on a
; freshly built (EXPR-BRACKET ES) leaves an unresolved IF that blocks the fold.
; This rule rewrites the binder names of a non-empty bracket directly; the
; hypothesis is discharged from CONSP-OF-UNIQ-EXPR-LIST at the use sites.  The
; two-field :FRAME and :ARRAY summands do not need this (their accessor rules
; simplify under the surrounding APPEND normalization).
(defruledl expr-binder-names-of-expr-bracket-when-consp
  (implies (consp exprs)
           (equal (expr-binder-names (expr-bracket exprs))
                  (expr-list-binder-names exprs)))
  :enable (expr-binder-names-of-expr-bracket
           consp-of-expr-list-fix))

(defines uniquify-names-impl
  :verify-guards nil ; done below
  :ruler-extenders :all
  ; The flag function is used by the DEFRET-MUTUAL further below.
  :flag-local nil

  (define uniq-expr ((x exprp) (used string-listp) (r var-renamings-p))
    :short "Uniquify binder names in an expression."
    :returns (mv (new-used string-listp :hyp :guard)
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
                ((mv used new-arg) (uniq-expr x.arg used r)))
             (mv used (expr-app new-fun new-arg)))

      :appn (b* (((mv used new-fun) (uniq-expr x.fun used r))
                 ((mv used new-args) (uniq-expr-list x.args used r)))
              (mv used (expr-appn new-fun new-args)))

      :tapp (b* (((mv used new-fun) (uniq-expr x.fun used r)))
              (mv used (expr-tapp new-fun (type-rename-all-vars x.arg r))))

      :tappn (b* (((mv used new-fun) (uniq-expr x.fun used r)))
               (mv used (expr-tappn new-fun (type-list-rename-all-vars x.args r))))

      :iapp (b* (((var-renamings r-) r)
                 ((mv used new-fun) (uniq-expr x.fun used r)))
              (mv used (expr-iapp new-fun
                                  (ispace-rename-ispace-vars
                                   x.arg r-.dim r-.shape))))

      :iappn (b* (((var-renamings r-) r)
                  ((mv used new-fun) (uniq-expr x.fun used r)))
               (mv used (expr-iappn new-fun
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
                  ;; ispace, so we rename it under the incoming renamings.
                  (new-type? (type-option-rename-all-vars x.type? r))
                  ;; Freshen the single ispace variable via the same helper
                  ;; as :unboxn, on a singleton list, so that the freshness
                  ;; facts of UNIQ-ISPACE-VAR-PARAMS apply directly.
                  ((mv used new-ispaces dim-renam shape-renam)
                   (uniq-ispace-var-params (list x.ispace) used r-.avoid
                                           r-.dim r-.shape))
                  (new-var (fresh-bind-name x.var used r-.avoid))
                  (used (cons new-var (str::string-list-fix used)))
                  (expr-renam (extend-renaming x.var new-var r-.expr))
                  (body-r (change-var-renamings r
                                                :dim dim-renam
                                                :shape shape-renam
                                                :expr expr-renam))
                  ((mv used new-body) (uniq-expr x.body used body-r)))
               (mv used (make-expr-unbox :ispace (car new-ispaces)
                                         :var new-var
                                         :target new-target
                                         :body new-body
                                         :type? new-type?)))

      :unboxn (b* (((var-renamings r-) r)
                   ((mv used new-target) (uniq-expr x.target used r))
                   ;; The result type is outside the scope of the unboxed
                   ;; ispaces, so we rename it under the incoming renamings.
                   (new-type? (type-option-rename-all-vars x.type? r))
                   ((mv used new-ispaces dim-renam shape-renam)
                    (uniq-ispace-var-params x.ispaces used r-.avoid
                                            r-.dim r-.shape))
                   (new-var (fresh-bind-name x.var used r-.avoid))
                   (used (cons new-var (str::string-list-fix used)))
                   (expr-renam (extend-renaming x.var new-var r-.expr))
                   (body-r (change-var-renamings r
                                                 :dim dim-renam
                                                 :shape shape-renam
                                                 :expr expr-renam))
                   ((mv used new-body) (uniq-expr x.body used body-r)))
               (mv used (make-expr-unboxn :ispaces new-ispaces
                                          :var new-var
                                          :target new-target
                                          :body new-body
                                          :type? new-type?)))

      :bracket (b* (((mv used new-es) (uniq-expr-list x.exprs used r)))
                 (mv used (expr-bracket new-es)))

      :let (b* (((mv used new-binds new-r) (uniq-bind-list x.binds used r))
                ((mv used new-body) (uniq-expr x.body used new-r)))
             (mv used (expr-let new-binds new-body)))))

  (define uniq-expr-list ((x expr-listp) (used string-listp) (r var-renamings-p))
    :short "Uniquify binder names in a list of expressions."
    :returns (mv (new-used string-listp :hyp :guard)
                 (new-x expr-listp :hyp :guard))
    :measure (expr-list-count x)
    (if (endp x)
        (mv used nil)
      (b* (((mv used new-e) (uniq-expr (car x) used r))
           ((mv used new-rest) (uniq-expr-list (cdr x) used r)))
        (mv used (cons new-e new-rest))))

    ///

    (defret consp-of-uniq-expr-list
      (equal (consp new-x)
             (consp x))
      :hints (("Goal" :expand ((uniq-expr-list x used r)))))

    (defret len->=-2-of-uniq-expr-list
      (implies (<= 2 (len x))
               (<= 2 (len new-x)))
      :rule-classes :linear
      :hints (("Goal" :expand ((uniq-expr-list x used r))
                      :in-theory (enable len consp-of-uniq-expr-list)))))

  (define uniq-atom ((x atomp) (used string-listp) (r var-renamings-p))
    :short "Uniquify binder names in an atom."
    :returns (mv (new-used string-listp :hyp :guard)
                 (new-x atomp :hyp :guard))
    :measure (atom-count x)
    (atom-case x
      :base (mv used (atom-fix x))

      :lambda (b* (((var-renamings r-) r)
                   (new-type? (type-option-rename-all-vars x.type? r))
                   (new-atype? (type-option-rename-all-vars
                                (var+type?->type? x.param) r))
                   (new-var (fresh-bind-name (var+type?->var x.param)
                                             used r-.avoid))
                   (used (cons new-var (str::string-list-fix used)))
                   (expr-renam (extend-renaming (var+type?->var x.param)
                                                new-var r-.expr))
                   (new-param (make-var+type? :var new-var :type? new-atype?))
                   ((mv used new-body)
                    (uniq-expr x.body used
                               (change-var-renamings r :expr expr-renam))))
                (mv used (make-atom-lambda :param new-param
                                           :body new-body
                                           :type? new-type?)))
      :lambdan (b* (((var-renamings r-) r)
                    (typed-params (var+type?-list-rename-all-vars x.params r))
                    (new-type? (type-option-rename-all-vars x.type? r))
                    ((mv used new-params expr-renam)
                     (uniq-expr-params typed-params used r-.avoid r-.expr))
                    ((mv used new-body)
                     (uniq-expr x.body used
                                (change-var-renamings r :expr expr-renam))))
                 (mv used (make-atom-lambdan :params new-params
                                             :body new-body
                                             :type? new-type?)))

      :tlambda (b* (((var-renamings r-) r)
                    (name (type-var->name x.param))
                    (new-name (fresh-bind-name name used r-.avoid))
                    (used (cons new-name (str::string-list-fix used)))
                    ((mv new-param atom-renam array-renam)
                     (type-var-case x.param
                       :atom (mv (type-var-atom new-name)
                                 (extend-renaming name new-name r-.atom)
                                 r-.array)
                       :array (mv (type-var-array new-name)
                                  r-.atom
                                  (extend-renaming name new-name r-.array))))
                    ((mv used new-body)
                     (uniq-expr x.body used
                                (change-var-renamings r
                                                      :atom atom-renam
                                                      :array array-renam))))
                 (mv used (atom-tlambda new-param new-body)))

      :tlambdan (b* (((var-renamings r-) r)
                     ((mv used new-params atom-renam array-renam)
                      (uniq-type-var-params x.params used r-.avoid
                                            r-.atom r-.array))
                     ((mv used new-body)
                      (uniq-expr x.body used
                                 (change-var-renamings r
                                                       :atom atom-renam
                                                       :array array-renam))))
                  (mv used (atom-tlambdan new-params new-body)))

      :ilambda (b* (((var-renamings r-) r)
                    (name (ispace-var->name x.param))
                    (new-name (fresh-bind-name name used r-.avoid))
                    (used (cons new-name (str::string-list-fix used)))
                    ((mv new-param dim-renam shape-renam)
                     (ispace-var-case x.param
                       :dim (mv (ispace-var-dim new-name)
                                (extend-renaming name new-name r-.dim)
                                r-.shape)
                       :shape (mv (ispace-var-shape new-name)
                                  r-.dim
                                  (extend-renaming name new-name r-.shape))))
                    ((mv used new-body)
                     (uniq-expr x.body used
                                (change-var-renamings r
                                                      :dim dim-renam
                                                      :shape shape-renam))))
                 (mv used (atom-ilambda new-param new-body)))

      :ilambdan (b* (((var-renamings r-) r)
                     ((mv used new-params dim-renam shape-renam)
                      (uniq-ispace-var-params x.params used r-.avoid
                                              r-.dim r-.shape))
                     ((mv used new-body)
                      (uniq-expr x.body used
                                 (change-var-renamings r
                                                       :dim dim-renam
                                                       :shape shape-renam))))
                  (mv used (atom-ilambdan new-params new-body)))

      :box (b* (((var-renamings r-) r)
                ((mv used new-array) (uniq-expr x.array used r)))
             (mv used (atom-box (ispace-rename-ispace-vars
                                 x.ispace r-.dim r-.shape)
                                new-array
                                (type-option-rename-all-vars x.type? r))))
      :boxn (b* (((var-renamings r-) r)
                 ((mv used new-array) (uniq-expr x.array used r)))
              (mv used (atom-boxn (ispace-list-rename-ispace-vars
                                   x.ispaces r-.dim r-.shape)
                                  new-array
                                  (type-rename-all-vars x.type r))))))

  (define uniq-atom-list ((x atom-listp) (used string-listp) (r var-renamings-p))
    :short "Uniquify binder names in a list of atoms."
    :returns (mv (new-used string-listp :hyp :guard)
                 (new-x atom-listp :hyp :guard))
    :measure (atom-list-count x)
    (if (endp x)
        (mv used nil)
      (b* (((mv used new-a) (uniq-atom (car x) used r))
           ((mv used new-rest) (uniq-atom-list (cdr x) used r)))
        (mv used (cons new-a new-rest))))

    ///

    (defret consp-of-uniq-atom-list
      (equal (consp new-x)
             (consp x))
      :hints (("Goal" :expand ((uniq-atom-list x used r))))))

  (define uniq-bind ((x bindp) (used string-listp) (r var-renamings-p))
    :short "Uniquify binder names in a bind, renaming the bind itself
            if its name has been seen before."
    :returns (mv (new-used string-listp :hyp :guard)
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
                   (used (cons new-name (str::string-list-fix used)))
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
                 (used (cons new-name (str::string-list-fix used)))
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
                (used (cons new-name (str::string-list-fix used)))
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
                (used (cons new-name (str::string-list-fix used)))
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
                 (used (cons new-name (str::string-list-fix used)))
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
                 (used (cons new-name (str::string-list-fix used)))
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
                 (used (cons new-name (str::string-list-fix used)))
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

  (define uniq-bind-list ((x bind-listp) (used string-listp) (r var-renamings-p))
    :short "Uniquify binder names in a list of binds, threading the renamings
            through the binds' sequential scopes."
    :returns (mv (new-used string-listp :hyp :guard)
                 (new-x bind-listp :hyp :guard)
                 (new-r var-renamings-p :hyp :guard))
    :measure (bind-list-count x)
    (if (endp x)
        (mv used nil (var-renamings-fix r))
      (b* (((mv used new-bind r) (uniq-bind (car x) used r))
           ((mv used new-rest r) (uniq-bind-list (cdr x) used r)))
        (mv used (cons new-bind new-rest) r))))

  ///

  ; Guard verification is deferred to here (:VERIFY-GUARDS NIL above) so that
  ; CONSP-OF-UNIQ-ATOM-LIST, in UNIQ-ATOM-LIST's ///, is available to it.
  ; The :APPN and :TAPPN cases need the two-or-more-ness of the rebuilt argument
  ; lists; both follow (through LEN->=-2-OF-UNIQ-EXPR-LIST and
  ; LEN-OF-TYPE-LIST-RENAME-ALL-VARS, all enabled) from the respective
  ; EXPR-APPN-REQUIREMENTS / EXPR-TAPPN-REQUIREMENTS, so no hints are needed.
  (verify-guards uniq-expr)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Freshness and USED-growth facts for the main traversal, in the same
; four-conjunct form as the parameter uniquification facts above: the binder
; names of the produced AST are duplicate-free, disjoint from the incoming
; USED, contained in the returned USED, and the incoming USED is contained
; in the returned USED.  For UNIQ-BIND, the "names" are the bind's nested
; binder names together with the bind's own (possibly renamed) name; for
; UNIQ-BIND-LIST, they match the grouping that BIND-LIST-NAMES and
; BIND-LIST-BINDER-NAMES (and hence EXPR-BINDER-NAMES' :LET case) produce.
;
; The invariant is deliberately stated with containments (SUBSETP-EQUAL)
; instead of an exact characterization of the returned USED: the exact
; version creates INSERT/UNION set equalities whose orientation under the
; rewriter's term order blocks their own use, while all the sequencing
; reasoning ("a later sibling's names avoid an earlier sibling's names,
; because the earlier names are inside the USED that the later freshness is
; stated against") needs only the containments, discharged by the
; monotonicity rules above.

  ; Keep the traversal definitions closed inside /// (DEFINES enables them
  ; here); the proof below opens just the top-level call via :EXPAND.
  (local (in-theory (disable uniq-expr uniq-expr-list uniq-atom
                                         uniq-atom-list uniq-bind uniq-bind-list)))

  ; For the unary :UNBOX case, UNIQ-EXPR freshens the single ispace variable
  ; through UNIQ-ISPACE-VAR-PARAMS on a singleton list and rebuilds the atom
  ; with (CAR NEW-ISPACES).  This rewrites (LIST (CAR NEW-ISPACES)) back to
  ; NEW-ISPACES (whose length is 1, via LEN-OF-UNIQ-ISPACE-VAR-PARAMS), so that
  ; the binder names match UNIQ-ISPACE-VAR-PARAMS-FACTS as in the :UNBOXN case.

  (defret-mutual uniquify-names-impl-facts
    (defret uniq-expr-facts
      (b* ((names (expr-binder-names new-x)))
        (and (no-duplicatesp-equal names)
             (not (intersectp-equal names (str::string-list-fix used)))
             (subsetp-equal names (str::string-list-fix new-used))
             (subsetp-equal (str::string-list-fix used) (str::string-list-fix new-used))))
      :fn uniq-expr)
    (defret uniq-expr-list-facts
      (b* ((names (expr-list-binder-names new-x)))
        (and (no-duplicatesp-equal names)
             (not (intersectp-equal names (str::string-list-fix used)))
             (subsetp-equal names (str::string-list-fix new-used))
             (subsetp-equal (str::string-list-fix used) (str::string-list-fix new-used))))
      :fn uniq-expr-list)
    (defret uniq-atom-facts
      (b* ((names (atom-binder-names new-x)))
        (and (no-duplicatesp-equal names)
             (not (intersectp-equal names (str::string-list-fix used)))
             (subsetp-equal names (str::string-list-fix new-used))
             (subsetp-equal (str::string-list-fix used) (str::string-list-fix new-used))))
      :fn uniq-atom)
    (defret uniq-atom-list-facts
      (b* ((names (atom-list-binder-names new-x)))
        (and (no-duplicatesp-equal names)
             (not (intersectp-equal names (str::string-list-fix used)))
             (subsetp-equal names (str::string-list-fix new-used))
             (subsetp-equal (str::string-list-fix used) (str::string-list-fix new-used))))
      :fn uniq-atom-list)
    (defret uniq-bind-facts
      (b* ((names (append (bind-binder-names new-x)
                          (list (bind-name new-x)))))
        (and (no-duplicatesp-equal names)
             (not (intersectp-equal names (str::string-list-fix used)))
             (subsetp-equal names (str::string-list-fix new-used))
             (subsetp-equal (str::string-list-fix used) (str::string-list-fix new-used))))
      :fn uniq-bind)
    (defret uniq-bind-list-facts
      (b* ((names (append (bind-list-names new-x)
                          (bind-list-binder-names new-x))))
        (and (no-duplicatesp-equal names)
             (not (intersectp-equal names (str::string-list-fix used)))
             (subsetp-equal names (str::string-list-fix new-used))
             (subsetp-equal (str::string-list-fix used) (str::string-list-fix new-used))))
      :fn uniq-bind-list)
    :mutual-recursion uniquify-names-impl
    ;; The traversal functions are opened via :EXPAND, on just the top-level
    ;; call of each induction subgoal, instead of enabling their definitions:
    ;; enabled definitions make the rewriter attempt (and almost always fail)
    ;; to open the closed inner calls that the induction hypotheses are about,
    ;; which dominates the proof time.  The (never-applicable, since this
    ;; theorem has no guard hypotheses) guard-conditional STRING-SETP return
    ;; type rules are disabled for the same reason.
    :hints
    (("Goal"
       :expand ((uniq-expr x used r)
                (uniq-expr-list x used r)
                (uniq-atom x used r)
                (uniq-atom-list x used r)
                (uniq-bind x used r)
                (uniq-bind-list x used r))
       :in-theory (e/d (expr-binder-names expr-list-binder-names
                                          atom-binder-names atom-list-binder-names
                                          bind-binder-names bind-list-binder-names
                                          bind-list-names bind-name
                                          expr-binder-names-of-expr-bracket-when-consp
                                          type-var->name ispace-var->name
                                          intersectp-equal
                                          no-duplicatesp-equal
                                          not-member-equal-of-fresh-bind-name
                                          acl2::not-intersectp-equal-when-subsetp-equal-arg2
                                          acl2::not-intersectp-equal-when-subsetp-equal-arg1-alt
                                          acl2::not-intersectp-equal-when-subsetp-equal-arg1
                                          acl2::not-member-equal-when-not-intersectp-equal
                                          acl2::not-member-equal-when-subsetp-equal-2
                                          acl2::subsetp-equal-transitive-alt
                                          acl2::subsetp-equal-transitive-2-alt
                                          acl2::member-equal-when-subsetp-equal-1
                                          len
                                          len-of-uniq-ispace-var-params
                                          list-of-car-when-len-1)
                       (return-type-of-uniq-expr.new-used
                        return-type-of-uniq-expr-list.new-used
                        return-type-of-uniq-atom.new-used
                        return-type-of-uniq-atom-list.new-used
                        return-type-of-uniq-bind.new-used
                        return-type-of-uniq-bind-list.new-used
                        string-listp-of-uniq-expr-params.new-used
                        string-listp-of-uniq-type-var-params.new-used
                        string-listp-of-uniq-ispace-var-params.new-used
                        string-listp-of-uniq-name-list.new-used)))))

  ) ; uniquify-names-impl


;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Conversely, the traversal is the identity when it has nothing to do: if the
; binder names of the AST node are already distinct and none of them has been
; seen (i.e. none is in USED), then every binder keeps its name, the renaming
; maps --- empty on entry --- stay empty, and the node comes back unchanged.
; The extra conjunct is the USED upper bound dual to the containment conjunct
; of UNIQUIFY-NAMES-IMPL-FACTS: USED grows only by the binder names of the
; node just processed.  It is what carries the disjointness hypothesis from
; one sub-computation to the next --- a later sibling's binder names are
; disjoint from the earlier siblings' names and from the incoming USED, hence
; from the USED that the later sibling is processed against.

(defret-mutual uniquify-names-impl-identity
  (defret uniq-expr-identity
    (b* ((names (expr-binder-names x)))
      (implies (and (var-renamings-emptyp r)
                    (no-duplicatesp-equal names)
                    (not (intersectp-equal names (str::string-list-fix used))))
               (and (equal new-x (expr-fix x))
                    (subsetp-equal (str::string-list-fix new-used)
                                   (append (str::string-list-fix used) names)))))
    :fn uniq-expr)
  (defret uniq-expr-list-identity
    (b* ((names (expr-list-binder-names x)))
      (implies (and (var-renamings-emptyp r)
                    (no-duplicatesp-equal names)
                    (not (intersectp-equal names (str::string-list-fix used))))
               (and (equal new-x (expr-list-fix x))
                    (subsetp-equal (str::string-list-fix new-used)
                                   (append (str::string-list-fix used) names)))))
    :fn uniq-expr-list)
  (defret uniq-atom-identity
    (b* ((names (atom-binder-names x)))
      (implies (and (var-renamings-emptyp r)
                    (no-duplicatesp-equal names)
                    (not (intersectp-equal names (str::string-list-fix used))))
               (and (equal new-x (atom-fix x))
                    (subsetp-equal (str::string-list-fix new-used)
                                   (append (str::string-list-fix used) names)))))
    :fn uniq-atom)
  (defret uniq-atom-list-identity
    (b* ((names (atom-list-binder-names x)))
      (implies (and (var-renamings-emptyp r)
                    (no-duplicatesp-equal names)
                    (not (intersectp-equal names (str::string-list-fix used))))
               (and (equal new-x (atom-list-fix x))
                    (subsetp-equal (str::string-list-fix new-used)
                                   (append (str::string-list-fix used) names)))))
    :fn uniq-atom-list)
  (defret uniq-bind-identity
    (b* ((names (append (bind-binder-names x) (list (bind-name x)))))
      (implies (and (var-renamings-emptyp r)
                    (no-duplicatesp-equal names)
                    (not (intersectp-equal names (str::string-list-fix used))))
               (and (equal new-x (bind-fix x))
                    (equal new-r (var-renamings-fix r))
                    (subsetp-equal (str::string-list-fix new-used)
                                   (append (str::string-list-fix used) names)))))
    :fn uniq-bind)
  (defret uniq-bind-list-identity
    (b* ((names (append (bind-list-names x) (bind-list-binder-names x))))
      (implies (and (var-renamings-emptyp r)
                    (no-duplicatesp-equal names)
                    (not (intersectp-equal names (str::string-list-fix used))))
               (and (equal new-x (bind-list-fix x))
                    (equal new-r (var-renamings-fix r))
                    (subsetp-equal (str::string-list-fix new-used)
                                   (append (str::string-list-fix used) names)))))
    :fn uniq-bind-list)
  :mutual-recursion uniquify-names-impl
  :hints
  (("Goal"
     :expand ((uniq-expr x used r)
              (uniq-expr-list x used r)
              (uniq-atom x used r)
              (uniq-atom-list x used r)
              (uniq-bind x used r)
              (uniq-bind-list x used r))
     :in-theory (e/d (expr-binder-names expr-list-binder-names
                                        atom-binder-names atom-list-binder-names
                                        bind-binder-names bind-list-binder-names
                                        bind-list-names bind-name
                                        expr-binder-names-of-expr-bracket-when-consp
                                        expr-list-fix atom-list-fix bind-list-fix
                                        ispace-var-list-fix
                                        type-var->name ispace-var->name
                                        var-renamings-emptyp
                                        extend-renaming
                                        intersectp-equal
                                        no-duplicatesp-equal
                                        acl2::subsetp-equal-of-append-2-2
                                        acl2::subsetp-equal-of-append-2-1
                                        acl2::subsetp-equal-of-cons-arg2
                                        acl2::intersectp-equal-commutative
                                        acl2::not-intersectp-equal-when-subsetp-equal-arg2-subsetp-first
                                        acl2::not-intersectp-equal-when-subsetp-equal-arg1-subsetp-first
                                        acl2::not-member-equal-when-subsetp-equal-1
                                        acl2::not-member-equal-when-not-intersectp-equal
                                        acl2::not-member-equal-when-subsetp-equal-2
                                        acl2::subsetp-equal-transitive-alt
                                        acl2::subsetp-equal-transitive-2-alt
                                        acl2::member-equal-when-subsetp-equal-1
                                        len
                                        len-of-uniq-ispace-var-params
                                        list-of-car-when-len-1)
                     ((:executable-counterpart type-var-list-option-none)
                      (:executable-counterpart ispace-var-list-option-none)
                      return-type-of-uniq-expr.new-used
                      return-type-of-uniq-expr-list.new-used
                      return-type-of-uniq-atom.new-used
                      return-type-of-uniq-atom-list.new-used
                      return-type-of-uniq-bind.new-used
                      return-type-of-uniq-bind-list.new-used
                      string-listp-of-uniq-expr-params.new-used
                      string-listp-of-uniq-type-var-params.new-used
                      string-listp-of-uniq-ispace-var-params.new-used
                      string-listp-of-uniq-name-list.new-used)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-free-var-names ((expr exprp))
  :returns (names string-setp)
  :short "Names of all the free variables of an expression,
          in all five namespaces."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the initial value of the @('used') set of names of
     @(tsee expr-uniquify-names): a binder whose name is one of these
     is renamed, so that no binder shadows a free variable of the
     expression."))
  (b* ((expr (expr-fix expr))
       ((mv free-dim-names free-shape-names)
        (dim/shape-names-of-ispace-vars (expr-free-ispace-vars expr)))
       ((mv free-atom-names free-array-names)
        (atom/array-names-of-type-vars (expr-free-type-vars expr))))
    (set::union (expr-free-expr-vars expr)
                (set::union free-dim-names
                            (set::union free-shape-names
                                        (set::union free-atom-names
                                                    free-array-names))))))

(define expr-all-var-names ((expr exprp))
  :returns (names string-setp)
  :short "Names of all the variables occurring anywhere in an expression,
          in any namespace and any role."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the @('avoid') component of the renamings threaded by
     @(tsee expr-uniquify-names): the generated fresh names avoid all of
     these, so the renamings applied to the binders' scopes are
     capture-free."))
  (b* ((expr (expr-fix expr))
       ((mv all-dim-names all-shape-names)
        (dim/shape-names-of-ispace-vars (expr-all-ispace-vars expr)))
       ((mv all-atom-names all-array-names)
        (atom/array-names-of-type-vars (expr-all-type-vars expr))))
    (set::union (expr-all-expr-vars expr)
                (set::union all-dim-names
                            (set::union all-shape-names
                                        (set::union all-atom-names
                                                    all-array-names))))))

(defrule expr-free-var-names-of-expr-fix-expr
  :parents (expr-free-var-names)
  (equal (expr-free-var-names (expr-fix expr))
         (expr-free-var-names expr))
  :enable expr-free-var-names)

(defrule expr-all-var-names-of-expr-fix-expr
  :parents (expr-all-var-names)
  (equal (expr-all-var-names (expr-fix expr))
         (expr-all-var-names expr))
  :enable expr-all-var-names)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-uniquify-names ((expr exprp))
  :returns (new-expr
            exprp
            :hints (("Goal" :in-theory
                     (enable acl2::string-listp-when-string-setp))))
  :short "Rename binds and parameters so that all binder names in an
          expression are distinct, keeping the original names where possible."
  ;; USED is seeded with the free variable names, which come back as an oset;
  ;; an oset is already a list, so it needs no conversion -- just the (by
  ;; default disabled) rule saying so.
  :guard-hints (("Goal" :in-theory (enable acl2::string-listp-when-string-setp)))
  :long
  (xdoc::topstring
   (xdoc::p
    "Traverses the expression left-to-right, accumulating the set of names seen
     so far, initialized with the names of the expression's free variables in
     all namespaces (so that no binder is renamed to, or left colliding with,
     e.g. a built-in function name).  A binder --- a bind, or a parameter of
     a lambda (of any kind), an unbox, or a function bind --- whose name has
     not been seen keeps it; otherwise the binder is renamed to a fresh
     variant of its name (the name with a numeric suffix), and the renaming
     is applied throughout the binder's scope.")
   (xdoc::p
    "Afterwards @(tsee expr-duplicate-names) returns @('nil'): this is
     proved as @(tsee expr-duplicate-names-of-expr-uniquify-names).
     Also, no binder name coincides with a free variable name of the
     expression (not proved yet).")
   (xdoc::p
    "Conversely, this is the identity on an expression that already has the
     property it establishes and whose binder names do not clash with its
     free variable names: see
     @(tsee expr-uniquify-names-when-no-duplicate-names).")
   (xdoc::p
    "The generated fresh names avoid the names of all the variables
     occurring anywhere in the expression, in any namespace and any role
     (see the @('avoid') component of @(tsee var-renamings)), so the
     renamings applied to the binds' scopes are capture-free."))
  (b* ((expr (expr-fix expr))
       (used (expr-free-var-names expr))
       (avoid (expr-all-var-names expr))
       (r (make-var-renamings :dim nil :shape nil :atom nil :array nil
                              :expr nil :avoid avoid))
       ((mv & new-expr) (uniq-expr expr used r)))
    new-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The promised theorem: after EXPR-UNIQUIFY-NAMES, no binder name is
; duplicated.  This follows from the no-duplicates conjunct of
; UNIQ-EXPR-FACTS (which is hypothesis-free) applied to the traversal that
; EXPR-UNIQUIFY-NAMES performs, plus the observation that DUPLICATED-NAMES
; returns nil exactly on duplicate-free lists.

(defrule duplicated-names-when-no-duplicatesp-equal
  :parents (expr-duplicate-names)
  :short "@('duplicated-names') returns @('nil') on a duplicate-free list."
  (implies (no-duplicatesp-equal names)
           (equal (duplicated-names names) nil))
  :induct t
  :enable (duplicated-names no-duplicatesp-equal))

(defrule expr-duplicate-names-of-expr-uniquify-names
  :parents (expr-uniquify-names expr-duplicate-names)
  :short "After @(tsee expr-uniquify-names), @(tsee expr-duplicate-names)
          returns @('nil'): all binder names in the resulting expression are
          distinct."
  (equal (expr-duplicate-names (expr-uniquify-names expr))
         nil)
  :enable (expr-uniquify-names
           expr-duplicate-names))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The converse: EXPR-UNIQUIFY-NAMES is the identity on an expression that
; already satisfies what it establishes.
;
; The no-duplicate-binder-names hypothesis alone does NOT suffice, because
; the traversal starts with USED initialized to the free variable names of
; the expression (in all five namespaces): a bind whose name also occurs
; free elsewhere in the expression is renamed even though no other binder
; binds that name.  For instance, in
;
;   (app x (let ((x 5)) x))
;
; the only binder is the bind of x, so EXPR-DUPLICATE-NAMES returns nil,
; while EXPR-UNIQUIFY-NAMES renames that bind (to "x0"), because the free
; occurrence of x in the left operand puts "x" in the initial USED.  Hence
; the second hypothesis below, that no binder name is a free variable name.

(defrule no-duplicatesp-equal-when-not-duplicated-names
  :parents (expr-duplicate-names)
  :short "@('duplicated-names') returns @('nil') only on a duplicate-free
          list; converse of @(tsee duplicated-names-when-no-duplicatesp-equal)."
  (implies (not (duplicated-names names))
           (no-duplicatesp-equal names))
  :induct t
  :enable (duplicated-names no-duplicatesp-equal))

(defruledl expr-uniquify-names-is-uniq-expr
  (equal (expr-uniquify-names expr)
         (mv-nth 1 (uniq-expr (expr-fix expr)
                              (expr-free-var-names expr)
                              (make-var-renamings
                               :dim nil :shape nil :atom nil :array nil
                               :expr nil :avoid (expr-all-var-names expr)))))
  :enable expr-uniquify-names)

(defrule expr-uniquify-names-when-no-duplicate-names
  :parents (expr-uniquify-names expr-duplicate-names)
  :short "@(tsee expr-uniquify-names) is the identity on an expression whose
          binder names are already distinct and distinct from its free
          variable names."
  :long
  (xdoc::topstring
   (xdoc::p
    "The second hypothesis cannot be dropped: the traversal starts with the
     set of seen names initialized to the free variable names of the
     expression (see @(tsee expr-free-var-names)), so a binder whose name
     also occurs free elsewhere in the expression is renamed even when no
     other binder binds that name."))
  (implies (and (not (expr-duplicate-names expr))
                (not (intersectp-equal (expr-binder-names expr)
                                       (expr-free-var-names expr))))
           (equal (expr-uniquify-names expr)
                  (expr-fix expr)))
  :enable (expr-uniquify-names-is-uniq-expr
           expr-duplicate-names
           var-renamings-emptyp
           ;; the seed USED is an oset, hence already a list, so its
           ;; STRING-LIST-FIX is the identity
           acl2::string-listp-when-string-setp
           str::string-list-fix-when-string-listp))
