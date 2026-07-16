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
     (proved as @(tsee expr-duplicate-names-of-expr-uniquify-names))."))
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
                      (append (ispace-var-list->name expr.ispaces)
                              (append (expr-binder-names expr.target)
                                      (expr-binder-names expr.body)))))
   (atom :lambda (append (var+type?-list->var atom.params)
                         (expr-binder-names atom.body)))
   (atom :tlambda (append (type-var-list->name atom.params)
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
     all names occurring anywhere in the expression (@('avoid')), so that it
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

; Support lemmas for the no-duplicate-names theorem about PROG-UNIQUIFY-NAMES
; (see the DEFRET-MUTUAL further below for the overall proof plan).
; Everything here is about plain-list membership, subset, disjointness, and
; duplicate-freeness over the (ordered-set) USED values that the traversal
; threads via SET::INSERT; the bridge between the ordered-set membership
; notion (SET::IN) and plain-list membership (MEMBER-EQUAL), on which all
; the remaining lemmas are phrased, is supplied by the included book
; STD/OSETS/TOP via SET::IN-TO-MEMBER.

(defrule member-equal-of-insert-when-string-setp
  (implies (string-setp used)
          (iff (member-equal a (set::insert b used))
               (or (equal a b) (member-equal a used))))
  :use ((:instance set::in-to-member (set::a a) (set::x (set::insert b used)))
       (:instance set::in-to-member (set::a a) (set::x used)))
  :enable (set::in-insert acl2::setp-when-string-setp set::insert-produces-set))

(defrule intersectp-equal-of-insert-when-string-setp
  (implies (string-setp used)
          (iff (intersectp-equal names (set::insert b used))
               (or (member-equal b names)
                   (intersectp-equal names used))))
  :induct (len names)
  :enable intersectp-equal)

; USED only grows (as a plain list, via SUBSETP-EQUAL) under SET::INSERT,
; and disjointness from a bigger set implies disjointness from any of its
; subsets (see the monotonicity rules below).

(defrule subsetp-equal-of-insert
  (implies (string-setp x)
          (subsetp-equal x (set::insert a x)))
  :induct (subsetp-equal x x)
  :enable (subsetp-equal member-equal-of-insert-when-string-setp))

(defruled intersectp-equal-commutative
  :short "Disabled by default: kept as a tool for deriving the mirrored
          orientations of the monotonicity rules below, rather than as a
          blanket rewrite, since an unconditional commutativity rewrite
          tends to fight with the fixed-orientation lemmas."
  (equal (intersectp-equal a b) (intersectp-equal b a))
  :rule-classes ((:rewrite :loop-stopper ((a b))))
  :enable intersectp-equal)

; Monotonicity of (non-)intersection in a subset, in all four orientations
; (which argument of INTERSECTP-EQUAL the known-disjoint bigger set occupies
; in the hypothesis, and which the smaller set occupies in the conclusion).
; The free variable BIG is matched against an available disjointness
; hypothesis.  In the traversal proof below, BIG is always a USED value that
; a sub-computation's names are known disjoint from, and SMALL is either an
; earlier USED value or an earlier sub-computation's names (both of which
; the invariant places inside that USED value).

(defruled not-intersectp-equal-when-subsetp-equal
  (implies (and (not (intersectp-equal l big))
               (subsetp-equal small big))
          (not (intersectp-equal l small)))
  :enable intersectp-equal)

(defruled not-intersectp-equal-when-subsetp-equal-2
  (implies (and (not (intersectp-equal l big))
               (subsetp-equal small big))
          (not (intersectp-equal small l)))
  :use (not-intersectp-equal-when-subsetp-equal
       (:instance intersectp-equal-commutative (a small) (b l))))

(defruled not-intersectp-equal-when-subsetp-equal-3
  (implies (and (not (intersectp-equal big l))
               (subsetp-equal small big))
          (not (intersectp-equal l small)))
  :use (not-intersectp-equal-when-subsetp-equal
       (:instance intersectp-equal-commutative (a big) (b l))))

(defruled not-intersectp-equal-when-subsetp-equal-4
  (implies (and (not (intersectp-equal big l))
               (subsetp-equal small big))
          (not (intersectp-equal small l)))
  :use (not-intersectp-equal-when-subsetp-equal-3
       (:instance intersectp-equal-commutative (a small) (b l))))

; The corresponding single-element facts: an element of a set known disjoint
; from L (in either orientation) is not in L, and membership/non-membership
; transports along subsets.

(defruled not-member-equal-when-not-intersectp-equal
  (implies (and (not (intersectp-equal l s))
               (member-equal a s))
          (not (member-equal a l)))
  :induct (len l)
  :enable intersectp-equal)

(defruled not-member-equal-when-subsetp-equal
  (implies (and (not (member-equal a big))
               (subsetp-equal small big))
          (not (member-equal a small)))
  :induct (len small)
  :enable subsetp-equal)

; Transitivity of SUBSETP-EQUAL and transport of membership along it, with
; both hypothesis orders and :MATCH-FREE :ALL, so that whichever of the two
; facts happens to be present as a hypothesis (typically an induction
; hypothesis) can bind the free intermediate, with the other fact then
; relieved by rewriting.

(defruled subsetp-equal-transitive-1
  (implies (and (subsetp-equal x y)
               (subsetp-equal y z))
          (subsetp-equal x z))
  :rule-classes ((:rewrite :match-free :all))
  :induct (len x)
  :enable (subsetp-equal not-member-equal-when-subsetp-equal))

(defruled subsetp-equal-transitive-2
  (implies (and (subsetp-equal y z)
               (subsetp-equal x y))
          (subsetp-equal x z))
  :rule-classes ((:rewrite :match-free :all))
  :use subsetp-equal-transitive-1)

(defruled member-equal-transport-1
  (implies (and (member-equal a x)
               (subsetp-equal x y))
          (member-equal a y))
  :rule-classes ((:rewrite :match-free :all))
  :use (:instance not-member-equal-when-subsetp-equal (big y) (small x)))

(defruled member-equal-transport-2
  (implies (and (subsetp-equal x y)
               (member-equal a x))
          (member-equal a y))
  :rule-classes ((:rewrite :match-free :all))
  :use member-equal-transport-1)

; Decomposition of NO-DUPLICATESP-EQUAL, INTERSECTP-EQUAL, and
; SUBSETP-EQUAL over the APPEND/CONS structure that the binder-names fold
; computes for a compound AST node, reducing each conjunct of the invariant
; below to facts about the individual sub-computations' names.

(defrule no-duplicatesp-equal-of-append
  (equal (no-duplicatesp-equal (append a b))
        (and (no-duplicatesp-equal a)
             (no-duplicatesp-equal b)
             (not (intersectp-equal a b))))
  :induct (append a b)
  :enable (no-duplicatesp-equal intersectp-equal))

(defrule intersectp-equal-of-append-1
  (equal (intersectp-equal (append a b) c)
        (or (intersectp-equal a c) (intersectp-equal b c)))
  :induct (append a b)
  :enable intersectp-equal)

(defrule intersectp-equal-of-append-2
  (equal (intersectp-equal a (append b c))
        (or (intersectp-equal a b) (intersectp-equal a c)))
  :enable intersectp-equal)

; INTERSECTP-EQUAL's own definition recurses on (and hence directly decomposes
; a CONS in) its FIRST argument; a CONS in the SECOND argument (e.g. a single
; bind's own name prepended to the rest of a bind-list's combined names)
; needs this separate, derived decomposition.

(defrule intersectp-equal-of-cons-2
  (iff (intersectp-equal a (cons x y))
      (or (member-equal x a) (intersectp-equal a y)))
  :induct t
  :enable (intersectp-equal member-equal))

; Decomposition of SUBSETP-EQUAL over APPEND and CONS in the first argument
; (the names of a compound AST node are appends/conses of the names of its
; sub-computations, each of which the invariant places in NEW-USED
; separately).

(defrule subsetp-equal-of-append-left
  (equal (subsetp-equal (append a b) c)
        (and (subsetp-equal a c) (subsetp-equal b c)))
  :induct (append a b)
  :enable subsetp-equal)

(defrule subsetp-equal-of-cons-left
  (equal (subsetp-equal (cons x a) c)
        (and (member-equal x c) (subsetp-equal a c)))
  :enable subsetp-equal)


(defrule not-in-used-of-fresh-bind-name
  :parents (fresh-bind-name)
  :short "@(tsee fresh-bind-name) never returns a name already in @('used')."
  (not (set::in (fresh-bind-name name used avoid) (string-sfix used)))
  :enable (fresh-bind-name set::union-in)
  :use (:instance fresh-expr-var-is-fresh
                  (prefix name)
                  (used (set::union (string-sfix used) (string-sfix avoid)))))

(defrule not-member-equal-of-fresh-bind-name
  :parents (fresh-bind-name)
  :short "@(tsee fresh-bind-name) never returns a name already in @('used'),
          restated in terms of @(tsee member-equal)."
  (not (member-equal (fresh-bind-name name used avoid) (string-sfix used)))
  :use (not-in-used-of-fresh-bind-name
       (:instance set::in-to-member
                  (set::a (fresh-bind-name name used avoid))
                  (set::x (string-sfix used)))))

(defrule not-member-equal-of-fresh-bind-name-when-subsetp-equal
  :parents (fresh-bind-name)
  :short "@(tsee fresh-bind-name) never returns a name already in any subset
          of @('used'), such as the names contributed by an earlier
          sub-computation.  Free-variable-free: @('used') is bound by the
          conclusion and the subset hypothesis is relieved by rewriting."
  (implies (subsetp-equal l (string-sfix used))
          (not (member-equal (fresh-bind-name name used avoid) l)))
  :use (:instance not-member-equal-when-subsetp-equal
                  (a (fresh-bind-name name used avoid))
                  (big (string-sfix used))
                  (small l)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

; Freshness and USED-growth facts for the three parameter uniquification
; functions above, in the four-conjunct form that the main traversal's
; DEFRET-MUTUAL below uses uniformly: the names of the returned parameters
; are duplicate-free and disjoint from the incoming USED, they are contained
; in the returned USED, and the incoming USED is contained in the returned
; USED.  Containments are stated with both sides under STRING-SFIX, since
; the return-type theorems of the traversal functions are guard-conditional
; and so the (unconditional) facts here cannot assume set-ness of raw
; values.

(defret uniq-expr-params-facts
  (b* ((names (var+type?-list->var new-params)))
    (and (no-duplicatesp-equal names)
        (not (intersectp-equal names (string-sfix used)))
        (subsetp-equal names (string-sfix new-used))
        (subsetp-equal (string-sfix used) (string-sfix new-used))))
  :fn uniq-expr-params
  :hints (("Goal" :induct t
          :in-theory (enable uniq-expr-params
                             var+type?-list->var
                             intersectp-equal
                             not-member-equal-of-fresh-bind-name
                             not-member-equal-when-not-intersectp-equal
                             not-intersectp-equal-when-subsetp-equal))))

(defret uniq-type-var-params-facts
  (b* ((names (type-var-list->name new-params)))
    (and (no-duplicatesp-equal names)
        (not (intersectp-equal names (string-sfix used)))
        (subsetp-equal names (string-sfix new-used))
        (subsetp-equal (string-sfix used) (string-sfix new-used))))
  :fn uniq-type-var-params
  :hints (("Goal" :induct t
          :in-theory (enable uniq-type-var-params
                             type-var-list->name
                             type-var->name
                             intersectp-equal
                             not-member-equal-of-fresh-bind-name
                             not-member-equal-when-not-intersectp-equal
                             not-intersectp-equal-when-subsetp-equal))))

(defret uniq-ispace-var-params-facts
  (b* ((names (ispace-var-list->name new-params)))
    (and (no-duplicatesp-equal names)
        (not (intersectp-equal names (string-sfix used)))
        (subsetp-equal names (string-sfix new-used))
        (subsetp-equal (string-sfix used) (string-sfix new-used))))
  :fn uniq-ispace-var-params
  :hints (("Goal" :induct t
          :in-theory (enable uniq-ispace-var-params
                             ispace-var-list->name
                             ispace-var->name
                             intersectp-equal
                             not-member-equal-of-fresh-bind-name
                             not-member-equal-when-not-intersectp-equal
                             not-intersectp-equal-when-subsetp-equal))))

; Free-variable-free consequences of the facts above, phrased so that the
; parameter function's call (and hence its USED argument) appears in the
; conclusion, with all remaining hypotheses relievable by rewriting.  These
; are needed because the facts above are rewrite rules rather than
; hypotheses of the main traversal's induction, so the free-variable
; monotonicity rules cannot bind their free variable to them: anything
; inside the incoming USED stays inside the returned USED, and is disjoint
; (in both argument orders) from the freshly chosen parameter names.

(defrule subsetp-equal-through-uniq-expr-params
  (implies (subsetp-equal l (string-sfix used))
          (subsetp-equal
           l (string-sfix (mv-nth 0 (uniq-expr-params params used avoid renam)))))
  :use (:instance subsetp-equal-transitive-1
                  (x l) (y (string-sfix used))
                  (z (string-sfix
                      (mv-nth 0 (uniq-expr-params params used avoid renam))))))

(defrule not-intersectp-equal-of-uniq-expr-params-names-1
  (implies (subsetp-equal l (string-sfix used))
          (not (intersectp-equal
                (var+type?-list->var
                 (mv-nth 1 (uniq-expr-params params used avoid renam)))
                l)))
  :use (:instance not-intersectp-equal-when-subsetp-equal
                  (l (var+type?-list->var
                      (mv-nth 1 (uniq-expr-params params used avoid renam))))
                  (big (string-sfix used))
                  (small l)))

(defrule not-intersectp-equal-of-uniq-expr-params-names-2
  (implies (subsetp-equal l (string-sfix used))
          (not (intersectp-equal
                l
                (var+type?-list->var
                 (mv-nth 1 (uniq-expr-params params used avoid renam))))))
  :use (:instance not-intersectp-equal-when-subsetp-equal-2
                  (l (var+type?-list->var
                      (mv-nth 1 (uniq-expr-params params used avoid renam))))
                  (big (string-sfix used))
                  (small l)))

(defrule subsetp-equal-through-uniq-type-var-params
  (implies (subsetp-equal l (string-sfix used))
          (subsetp-equal
           l (string-sfix
              (mv-nth 0 (uniq-type-var-params params used avoid
                                              atom-renam array-renam)))))
  :use (:instance subsetp-equal-transitive-1
                  (x l) (y (string-sfix used))
                  (z (string-sfix
                      (mv-nth 0 (uniq-type-var-params params used avoid
                                                      atom-renam array-renam))))))

(defrule not-intersectp-equal-of-uniq-type-var-params-names-1
  (implies (subsetp-equal l (string-sfix used))
          (not (intersectp-equal
                (type-var-list->name
                 (mv-nth 1 (uniq-type-var-params params used avoid
                                                 atom-renam array-renam)))
                l)))
  :use (:instance not-intersectp-equal-when-subsetp-equal
                  (l (type-var-list->name
                      (mv-nth 1 (uniq-type-var-params params used avoid
                                                      atom-renam array-renam))))
                  (big (string-sfix used))
                  (small l)))

(defrule subsetp-equal-through-uniq-ispace-var-params
  (implies (subsetp-equal l (string-sfix used))
          (subsetp-equal
           l (string-sfix
              (mv-nth 0 (uniq-ispace-var-params params used avoid
                                                dim-renam shape-renam)))))
  :use (:instance subsetp-equal-transitive-1
                  (x l) (y (string-sfix used))
                  (z (string-sfix
                      (mv-nth 0 (uniq-ispace-var-params params used avoid
                                                        dim-renam shape-renam))))))

(defrule not-intersectp-equal-of-uniq-ispace-var-params-names-1
  (implies (subsetp-equal l (string-sfix used))
          (not (intersectp-equal
                (ispace-var-list->name
                 (mv-nth 1 (uniq-ispace-var-params params used avoid
                                                   dim-renam shape-renam)))
                l)))
  :use (:instance not-intersectp-equal-when-subsetp-equal
                  (l (ispace-var-list->name
                      (mv-nth 1 (uniq-ispace-var-params params used avoid
                                                        dim-renam shape-renam))))
                  (big (string-sfix used))
                  (small l)))

(defrule not-intersectp-equal-of-uniq-ispace-var-params-names-2
  (implies (subsetp-equal l (string-sfix used))
          (not (intersectp-equal
                l
                (ispace-var-list->name
                 (mv-nth 1 (uniq-ispace-var-params params used avoid
                                                   dim-renam shape-renam))))))
  :use (:instance not-intersectp-equal-when-subsetp-equal-2
                  (l (ispace-var-list->name
                      (mv-nth 1 (uniq-ispace-var-params params used avoid
                                                        dim-renam shape-renam))))
                  (big (string-sfix used))
                  (small l)))


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

(defines uniquify-names-impl
  :verify-guards :after-returns
  :ruler-extenders :all
  ; The flag function is used by the DEFRET-MUTUAL further below.
  :flag-local nil

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
                    (name (ispace-var->name x.param))
                    (new-name (fresh-bind-name name used r-.avoid))
                    (used (set::insert new-name (string-sfix used)))
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

(defret-mutual uniquify-names-impl-facts
  (defret uniq-expr-facts
    (b* ((names (expr-binder-names new-x)))
      (and (no-duplicatesp-equal names)
          (not (intersectp-equal names (string-sfix used)))
          (subsetp-equal names (string-sfix new-used))
          (subsetp-equal (string-sfix used) (string-sfix new-used))))
    :fn uniq-expr)
  (defret uniq-expr-list-facts
    (b* ((names (expr-list-binder-names new-x)))
      (and (no-duplicatesp-equal names)
          (not (intersectp-equal names (string-sfix used)))
          (subsetp-equal names (string-sfix new-used))
          (subsetp-equal (string-sfix used) (string-sfix new-used))))
    :fn uniq-expr-list)
  (defret uniq-atom-facts
    (b* ((names (atom-binder-names new-x)))
      (and (no-duplicatesp-equal names)
          (not (intersectp-equal names (string-sfix used)))
          (subsetp-equal names (string-sfix new-used))
          (subsetp-equal (string-sfix used) (string-sfix new-used))))
    :fn uniq-atom)
  (defret uniq-atom-list-facts
    (b* ((names (atom-list-binder-names new-x)))
      (and (no-duplicatesp-equal names)
          (not (intersectp-equal names (string-sfix used)))
          (subsetp-equal names (string-sfix new-used))
          (subsetp-equal (string-sfix used) (string-sfix new-used))))
    :fn uniq-atom-list)
  (defret uniq-bind-facts
    (b* ((names (append (bind-binder-names new-x)
                        (list (bind-name new-x)))))
      (and (no-duplicatesp-equal names)
          (not (intersectp-equal names (string-sfix used)))
          (subsetp-equal names (string-sfix new-used))
          (subsetp-equal (string-sfix used) (string-sfix new-used))))
    :fn uniq-bind)
  (defret uniq-bind-list-facts
    (b* ((names (append (bind-list-names new-x)
                        (bind-list-binder-names new-x))))
      (and (no-duplicatesp-equal names)
          (not (intersectp-equal names (string-sfix used)))
          (subsetp-equal names (string-sfix new-used))
          (subsetp-equal (string-sfix used) (string-sfix new-used))))
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
                     type-var->name ispace-var->name
                     intersectp-equal
                     no-duplicatesp-equal
                     not-member-equal-of-fresh-bind-name
                     not-intersectp-equal-when-subsetp-equal
                     not-intersectp-equal-when-subsetp-equal-2
                     not-intersectp-equal-when-subsetp-equal-4
                     not-member-equal-when-not-intersectp-equal
                     not-member-equal-when-subsetp-equal
                     subsetp-equal-transitive-1
                     subsetp-equal-transitive-2
                     member-equal-transport-2)
                    (return-type-of-uniq-expr.new-used
                     return-type-of-uniq-expr-list.new-used
                     return-type-of-uniq-atom.new-used
                     return-type-of-uniq-atom-list.new-used
                     return-type-of-uniq-bind.new-used
                     return-type-of-uniq-bind-list.new-used
                     string-setp-of-uniq-expr-params.new-used
                     string-setp-of-uniq-type-var-params.new-used
                     string-setp-of-uniq-ispace-var-params.new-used)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-uniquify-names ((expr exprp))
  :returns (new-expr exprp)
  :short "Rename binds and parameters so that all binder names in an
          expression are distinct, keeping the original names where possible."
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
    "The generated fresh names avoid the names of all the variables
     occurring anywhere in the expression, in any namespace and any role
     (see the @('avoid') component of @(tsee var-renamings)), so the
     renamings applied to the binds' scopes are capture-free."))
  (b* ((expr (expr-fix expr))
       ((mv free-dim-names free-shape-names)
        (dim/shape-names-of-ispace-vars (expr-free-ispace-vars expr)))
       ((mv free-atom-names free-array-names)
        (atom/array-names-of-type-vars (expr-free-type-vars expr)))
       (used (set::union
              (expr-free-expr-vars expr)
              (set::union
               free-dim-names
               (set::union free-shape-names
                           (set::union free-atom-names free-array-names)))))
       ((mv all-dim-names all-shape-names)
        (dim/shape-names-of-ispace-vars (expr-all-ispace-vars expr)))
       ((mv all-atom-names all-array-names)
        (atom/array-names-of-type-vars (expr-all-type-vars expr)))
       (avoid (set::union
               (expr-all-expr-vars expr)
               (set::union
                all-dim-names
                (set::union all-shape-names
                            (set::union all-atom-names all-array-names)))))
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
