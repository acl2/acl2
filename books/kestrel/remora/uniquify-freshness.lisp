; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "free-variables-in-all-variables")
(include-book "renaming-no-capture-when-avoided")
(include-book "uniquify-alpha-relations")

(include-book "omaps")

(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ uniquify-freshness
  :parents (unique-names)
  :short "The freshness bridge: the output of @(tsee expr-uniquify-names)
          satisfies the freshness relation @(tsee expr-alpha-fresh-p)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The alpha bridge (@('uniq-alpha-bridge')) shows, hypothesis-free,
     that the uniquifier's output is alpha-related to its input under the
     traversal's renamings.  The freshness bridge shows that the output
     also satisfies the freshness companion of that relation, whose
     conjuncts are the no-capture and support-set conditions that the
     main induction over the evaluator (see @(see uniquify-evaluation))
     consumes at each binder.")
   (xdoc::p
    "Unlike the alpha bridge, the freshness bridge holds under an
     invariant relating the traversal's list of used names, its renaming
     maps, and the constant set of names to avoid, to the relation's
     renamings and support set: every key and value of the renaming maps
     is a used name, the values avoid the constant set, and the support
     set is within the used and avoided names (see
     @(tsee renamings-invariant-p) and @(tsee support-invariant-p)); the
     traversal preserves it, and under it the fresh name generated for a
     binder satisfies the relation's freshness conditions (the crux
     obligation @(tsee name-fresh-ok-of-fresh-bind-name), proved in the
     relations book).")
   (xdoc::p
    "The book proceeds bottom-up: the invariant and its preservation along
     the traversal; the sequential freshness of the parameter lists the
     uniquifier produces; the no-capture of the fresh binders and parameter
     lists against the renaming image of their scope (which the relation
     states on the free variables of the scope, and the invariant supplies
     through the avoidance of all the variables of the expression); the
     support sets of closure bodies and of the abstraction layers that the
     evaluator builds for a combined function bind; and the bridge
     induction itself, a @('defret-mutual') over the uniquifier in the
     shape of the alpha bridge, whose statements quantify over the support
     set so that one induction covers all of them.  Its top-level
     instance, at the empty renamings, is
     @('expr-alpha-fresh-p-of-expr-uniquify-names'): for every support set
     within the initial used names and the expression's variable names, in
     particular the primitive operations' names used by the main
     induction's top-level instance in @(see unique-names-validation)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Set and omap facts.
;
; The generic ones live in the library extensions --- see @(see osets) and
; @(see omaps) --- where they are disabled, as the house style there has
; it.  The ones this book wants to fire on its own are enabled here.

(local (in-theory (enable subset-of-union
                          subset-values-of-delete
                          subset-values-of-delete*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define renamings-avoid-p ((r var-renamings-p))
  :returns (yes/no booleanp)
  (b* (((var-renamings r) r))
    (and (map-values-avoid-p r.dim r.avoid)
         (map-values-avoid-p r.shape r.avoid)
         (map-values-avoid-p r.atom r.avoid)
         (map-values-avoid-p r.array r.avoid)
         (map-values-avoid-p r.expr r.avoid))))

(defrule type-fresh-ok-when-avoided
  (implies (and (renamings-avoid-p r)
                (set::subset (ispace-var-set-names (type-all-ispace-vars ty))
                             (var-renamings->avoid r))
                (set::subset (type-var-set-names (type-all-type-vars ty))
                             (var-renamings->avoid r)))
           (type-fresh-ok ty r))
  :enable (type-fresh-ok renamings-avoid-p))

(defrule type-option-fresh-ok-when-avoided
  (implies (and (renamings-avoid-p r)
                (set::subset (ispace-var-set-names
                              (type-option-all-ispace-vars ty?))
                             (var-renamings->avoid r))
                (set::subset (type-var-set-names
                              (type-option-all-type-vars ty?))
                             (var-renamings->avoid r)))
           (type-option-fresh-ok ty? r))
  :enable (type-option-fresh-ok
           type-option-all-ispace-vars
           type-option-all-type-vars))

(defrule type-list-fresh-ok-when-avoided
  (implies (and (renamings-avoid-p r)
                (set::subset (ispace-var-set-names
                              (type-list-all-ispace-vars tys))
                             (var-renamings->avoid r))
                (set::subset (type-var-set-names
                              (type-list-all-type-vars tys))
                             (var-renamings->avoid r)))
           (type-list-fresh-ok tys r))
  :induct t
  :enable (type-list-fresh-ok
           type-list-all-ispace-vars
           type-list-all-type-vars))

(defrule type-list-option-fresh-ok-when-avoided
  (implies (and (renamings-avoid-p r)
                (set::subset (ispace-var-set-names
                              (type-list-option-all-ispace-vars tys?))
                             (var-renamings->avoid r))
                (set::subset (type-var-set-names
                              (type-list-option-all-type-vars tys?))
                             (var-renamings->avoid r)))
           (type-list-option-fresh-ok tys? r))
  :enable (type-list-option-fresh-ok
           type-list-option-all-ispace-vars
           type-list-option-all-type-vars))

(defrule var+type?-list-types-fresh-ok-when-avoided
  (implies (and (renamings-avoid-p r)
                (set::subset (ispace-var-set-names
                              (var+type?-list-all-ispace-vars params))
                             (var-renamings->avoid r))
                (set::subset (type-var-set-names
                              (var+type?-list-all-type-vars params))
                             (var-renamings->avoid r)))
           (var+type?-list-types-fresh-ok params r))
  :induct t
  :enable (var+type?-list-types-fresh-ok
           var+type?-list-all-ispace-vars
           var+type?-list-all-type-vars
           var+type?-all-ispace-vars
           var+type?-all-type-vars))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The bridge invariant: map keys and values within the used names, map
; values avoiding the constant name set, support set within used and avoided
; names; and its preservation along the traversal.

(defrule fresh-bind-name-in-avoid-implies-kept
  (implies (set::in (fresh-bind-name name used avoid) (string-sfix avoid))
           (equal (fresh-bind-name name used avoid) (str-fix name)))
  :enable (fresh-bind-name set::union-in)
  :use (:instance fresh-expr-var-is-fresh
                  (prefix name)
                  (used (set::union (list-to-oset (str::string-list-fix used))
                                    (string-sfix avoid)))))

; The invariant is stated with containments of the maps' keys and values,
; so the library rules that carry those through the map operations, and
; the one that sorts a list containment into a set containment, are wanted
; from here on.

(local (in-theory (enable subset-of-mergesort-when-subsetp-equal
                          subset-values-of-delete-when-subset
                          subset-values-of-delete*-when-subset
                          subset-values-of-update)))

(define renaming-invariant-p ((m string-string-mapp)
                              (used string-listp)
                              (avoid string-setp))
  :returns (yes/no booleanp)
  (b* ((m (string-string-map-fix m))
       (u (set::mergesort (str::string-list-fix used))))
    (and (set::subset (omap::keys m) u)
         (set::subset (omap::values m) u)
         (map-values-avoid-p m avoid)))
  ///
  (fty::deffixequiv renaming-invariant-p))

(in-theory (disable renaming-invariant-p))

(define support-invariant-p ((b string-setp)
                             (used string-listp)
                             (avoid string-setp))
  :parents (uniquify-freshness)
  :short "Check that a support set is covered by
          the names in use and the names to avoid."
  :returns (yes/no booleanp)
  (set::subset (string-sfix b)
               (set::union (set::mergesort (str::string-list-fix used))
                           (string-sfix avoid)))
  ///
  (fty::deffixequiv support-invariant-p))

(in-theory (disable support-invariant-p))

(define renamings-invariant-p ((r var-renamings-p) (used string-listp))
  :parents (uniquify-freshness)
  :short "Check that all the renamings satisfy the renaming invariant
          with respect to the names in use."
  :returns (yes/no booleanp)
  (b* (((var-renamings r) r))
    (and (renaming-invariant-p r.dim used r.avoid)
         (renaming-invariant-p r.shape used r.avoid)
         (renaming-invariant-p r.atom used r.avoid)
         (renaming-invariant-p r.array used r.avoid)
         (renaming-invariant-p r.expr used r.avoid)))
  ///
  (fty::deffixequiv renamings-invariant-p))

(defrule renamings-avoid-p-when-renamings-invariant-p
  (implies (renamings-invariant-p r used)
           (renamings-avoid-p r))
  :enable (renamings-invariant-p renamings-avoid-p renaming-invariant-p))

(defrule renaming-invariant-p-when-subsetp-equal
  (implies (and (renaming-invariant-p m used avoid)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used2)))
           (renaming-invariant-p m used2 avoid))
  :enable renaming-invariant-p
  :use ((:instance set::subset-transitive
                   (x (omap::keys (string-string-map-fix m)))
                   (y (set::mergesort (str::string-list-fix used)))
                   (z (set::mergesort (str::string-list-fix used2))))
        (:instance set::subset-transitive
                   (x (omap::values (string-string-map-fix m)))
                   (y (set::mergesort (str::string-list-fix used)))
                   (z (set::mergesort (str::string-list-fix used2))))))

(defrule support-invariant-p-when-subsetp-equal
  (implies (and (support-invariant-p b used avoid)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used2)))
           (support-invariant-p b used2 avoid))
  :enable (support-invariant-p subset-lifting-rules)
  :use ((:instance set::subset-transitive
                   (x (string-sfix b))
                   (y (set::union (set::mergesort (str::string-list-fix used))
                                  (string-sfix avoid)))
                   (z (set::union (set::mergesort (str::string-list-fix used2))
                                  (string-sfix avoid))))))

(defrule name-fresh-ok-when-invariants
  (implies (and (renaming-invariant-p m used avoid)
                (support-invariant-p b used avoid))
           (name-fresh-ok name (fresh-bind-name name used avoid) m b))
  :enable (renaming-invariant-p support-invariant-p))

(defrule support-invariant-p-of-insert
  (implies (and (stringp a)
                (string-setp b))
           (equal (support-invariant-p (set::insert a b) used avoid)
                  (and (or (member-equal a (str::string-list-fix used))
                           (set::in a (string-sfix avoid)))
                       (support-invariant-p b used avoid))))
  :enable (support-invariant-p set::union-in set::in-mergesort))

(defrule support-invariant-p-of-union
  (implies (and (string-setp b1)
                (string-setp b2))
           (equal (support-invariant-p (set::union b1 b2) used avoid)
                  (and (support-invariant-p b1 used avoid)
                       (support-invariant-p b2 used avoid))))
  :enable support-invariant-p)

(defrule support-invariant-p-of-mergesort-when-subsetp-equal
  (implies (subsetp-equal (str::string-list-fix names)
                          (str::string-list-fix used))
           (support-invariant-p (set::mergesort (str::string-list-fix names))
                                used avoid))
  :enable (support-invariant-p subset-lifting-rules))

(defrule support-invariant-p-of-nil
  (support-invariant-p nil used avoid)
  :enable support-invariant-p)

(defrule not-in-avoid-of-fresh-bind-name-when-member
  (implies (member-equal (str-fix name) (str::string-list-fix used))
           (not (set::in (fresh-bind-name name used avoid)
                         (string-sfix avoid))))
  :enable (fresh-bind-name set::union-in)
  :use (:instance fresh-expr-var-is-fresh
                  (prefix name)
                  (used (set::union (list-to-oset (str::string-list-fix used))
                                    (string-sfix avoid)))))

(defrule renaming-invariant-p-of-extend-renaming-of-fresh-bind-name
  (implies (renaming-invariant-p m used avoid)
           (renaming-invariant-p
            (extend-renaming name (fresh-bind-name name used avoid) m)
            (cons (fresh-bind-name name used avoid)
                  (str::string-list-fix used))
            avoid))
  :enable (renaming-invariant-p extend-renaming
           mergesort-of-cons
           subset-lifting-rules
           set::in-mergesort)
  :cases ((member-equal (str-fix name) (str::string-list-fix used)))
  :use ((:instance set::subset-transitive
                   (x (omap::values
                       (omap::update (str-fix name)
                                     (fresh-bind-name name used avoid)
                                     (string-string-map-fix m))))
                   (y (set::insert (fresh-bind-name name used avoid)
                                   (omap::values (string-string-map-fix m))))
                   (z (set::insert (fresh-bind-name name used avoid)
                                   (set::mergesort
                                    (str::string-list-fix used)))))))

(defrule subsetp-equal-through-uniq-expr
  (implies (subsetp-equal l (str::string-list-fix used))
           (subsetp-equal l (str::string-list-fix
                             (mv-nth 0 (uniq-expr x used r)))))
  :use (uniq-expr-facts
        (:instance acl2::subsetp-equal-transitive-alt
                   (x l) (y (str::string-list-fix used))
                   (z (str::string-list-fix (mv-nth 0 (uniq-expr x used r))))))
  :disable uniq-expr-facts)

(defrule subsetp-equal-through-uniq-atom
  (implies (subsetp-equal l (str::string-list-fix used))
           (subsetp-equal l (str::string-list-fix
                             (mv-nth 0 (uniq-atom x used r)))))
  :use (uniq-atom-facts
        (:instance acl2::subsetp-equal-transitive-alt
                   (x l) (y (str::string-list-fix used))
                   (z (str::string-list-fix (mv-nth 0 (uniq-atom x used r))))))
  :disable uniq-atom-facts)

(defrule subsetp-equal-through-uniq-bind
  (implies (subsetp-equal l (str::string-list-fix used))
           (subsetp-equal l (str::string-list-fix
                             (mv-nth 0 (uniq-bind x used r)))))
  :use (uniq-bind-facts
        (:instance acl2::subsetp-equal-transitive-alt
                   (x l) (y (str::string-list-fix used))
                   (z (str::string-list-fix (mv-nth 0 (uniq-bind x used r))))))
  :disable uniq-bind-facts)

(defrule subsetp-equal-through-uniq-bind-list
  (implies (subsetp-equal l (str::string-list-fix used))
           (subsetp-equal l (str::string-list-fix
                             (mv-nth 0 (uniq-bind-list x used r)))))
  :use (uniq-bind-list-facts
        (:instance acl2::subsetp-equal-transitive-alt
                   (x l) (y (str::string-list-fix used))
                   (z (str::string-list-fix
                       (mv-nth 0 (uniq-bind-list x used r))))))
  :disable uniq-bind-list-facts)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Sequential freshness of the parameter lists produced by the uniquifier.
; Each induction mirrors the corresponding uniquifier helper while also
; threading the renaming map and support set as the relation does.

(define uniq-name-list-fresh-induct ((names string-listp)
                                     (used string-listp)
                                     (avoid string-setp)
                                     (m string-string-mapp)
                                     (b string-setp))
  :returns (dummy true-listp)
  (b* (((when (endp names)) (list used m b))
       (new (fresh-bind-name (car names) used avoid)))
    (uniq-name-list-fresh-induct (cdr names)
                                 (cons new (str::string-list-fix used))
                                 avoid
                                 (extend-renaming (car names) new m)
                                 (set::insert new (string-sfix b))))
  :measure (len names)
  :verify-guards nil)

(defrule renaming-invariant-p-of-extend-renaming-of-fresh-bind-name-alt
  (implies (renaming-invariant-p m used avoid)
           (renaming-invariant-p
            (extend-renaming name (fresh-bind-name name used avoid) m)
            (cons (fresh-bind-name name used avoid) used)
            avoid))
  :use renaming-invariant-p-of-extend-renaming-of-fresh-bind-name)

(defrule string-list-fresh-ok-of-uniq-name-list
  (implies (and (renaming-invariant-p m used avoid)
                (support-invariant-p b used avoid))
           (string-list-fresh-ok names
                                 (mv-nth 1 (uniq-name-list names used avoid))
                                 m b))
  :induct (uniq-name-list-fresh-induct names used avoid m b)
  :enable (uniq-name-list-fresh-induct
           string-list-fresh-ok
           uniq-name-list))

(define uniq-type-var-params-fresh-induct ((params type-var-listp)
                                           (used string-listp)
                                           (avoid string-setp)
                                           (atom-renam string-string-mapp)
                                           (array-renam string-string-mapp)
                                           (b string-setp))
  :returns (dummy true-listp)
  (b* (((when (endp params)) (list used atom-renam array-renam b))
       (var (car params))
       (name (type-var->name var))
       (new-name (fresh-bind-name name used avoid))
       (used (cons new-name (str::string-list-fix used)))
       ((mv atom-renam array-renam)
        (type-var-case var
          :atom (mv (extend-renaming name new-name atom-renam)
                    (string-string-map-fix array-renam))
          :array (mv (string-string-map-fix atom-renam)
                     (extend-renaming name new-name array-renam)))))
    (uniq-type-var-params-fresh-induct (cdr params) used avoid
                                       atom-renam array-renam
                                       (set::insert new-name (string-sfix b))))
  :measure (len params)
  :verify-guards nil)

(defrule type-var-list-fresh-ok-of-uniq-type-var-params
  (implies (and (renaming-invariant-p atom-renam used avoid)
                (renaming-invariant-p array-renam used avoid)
                (support-invariant-p b used avoid))
           (type-var-list-fresh-ok
            (mv-nth 1 (uniq-type-var-params params used avoid
                                            atom-renam array-renam))
            params atom-renam array-renam b))
  :induct (uniq-type-var-params-fresh-induct params used avoid
                                             atom-renam array-renam b)
  :enable (uniq-type-var-params-fresh-induct
           type-var-list-fresh-ok
           uniq-type-var-params
           type-var->name))

(define uniq-ispace-var-params-fresh-induct ((params ispace-var-listp)
                                             (used string-listp)
                                             (avoid string-setp)
                                             (dim-renam string-string-mapp)
                                             (shape-renam string-string-mapp)
                                             (b string-setp))
  :returns (dummy true-listp)
  (b* (((when (endp params)) (list used dim-renam shape-renam b))
       (var (car params))
       (name (ispace-var->name var))
       (new-name (fresh-bind-name name used avoid))
       (used (cons new-name (str::string-list-fix used)))
       ((mv dim-renam shape-renam)
        (ispace-var-case var
          :dim (mv (extend-renaming name new-name dim-renam)
                   (string-string-map-fix shape-renam))
          :shape (mv (string-string-map-fix dim-renam)
                     (extend-renaming name new-name shape-renam)))))
    (uniq-ispace-var-params-fresh-induct (cdr params) used avoid
                                         dim-renam shape-renam
                                         (set::insert new-name
                                                      (string-sfix b))))
  :measure (len params)
  :verify-guards nil)

(defrule ispace-var-list-fresh-ok-of-uniq-ispace-var-params
  (implies (and (renaming-invariant-p dim-renam used avoid)
                (renaming-invariant-p shape-renam used avoid)
                (support-invariant-p b used avoid))
           (ispace-var-list-fresh-ok
            (mv-nth 1 (uniq-ispace-var-params params used avoid
                                              dim-renam shape-renam))
            params dim-renam shape-renam b))
  :induct (uniq-ispace-var-params-fresh-induct params used avoid
                                               dim-renam shape-renam b)
  :enable (uniq-ispace-var-params-fresh-induct
           ispace-var-list-fresh-ok
           uniq-ispace-var-params
           ispace-var->name))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Values of the renaming maps under the invariant.

(defrule not-in-values-when-renaming-invariant-p-and-not-member
  (implies (and (renaming-invariant-p m used avoid)
                (not (member-equal y (str::string-list-fix used))))
           (not (set::in y (omap::values (string-string-map-fix m)))))
  :enable (renaming-invariant-p set::in-mergesort)
  :use ((:instance set::subset-in
                   (a y)
                   (x (omap::values (string-string-map-fix m)))
                   (y (set::mergesort (str::string-list-fix used))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; No-capture of a single fresh binder against the image of its scope.

(defrule not-in-rename-image-of-delete-of-fresh-bind-name
  (implies (and (renaming-invariant-p m used avoid)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used1))
                (string-setp f)
                (set::subset f (string-sfix avoid))
                (stringp name))
           (not (set::in (fresh-bind-name name used1 avoid)
                         (rename-var-string-set (set::delete name f) m))))
  :cases ((member-equal name (str::string-list-fix used1)))
  :use ((:instance not-in-rename-var-string-set-when-fresh
                   (names (set::delete name f))
                   (y (fresh-bind-name name used1 avoid))
                   (renam m))
        (:instance set::subset-in
                   (a (fresh-bind-name name used1 avoid))
                   (x f)
                   (y (string-sfix avoid)))))

(defrule not-in-ispace-image-of-delete-of-fresh-bind-name-dim
  (implies (and (renaming-invariant-p dim-renam used avoid)
                (renaming-invariant-p shape-renam used avoid)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used1))
                (ispace-var-setp f)
                (set::subset (ispace-var-set-names f) (string-sfix avoid))
                (ispace-varp v)
                (equal (ispace-var-kind v) :dim))
           (not (set::in (ispace-var-dim
                          (fresh-bind-name (ispace-var-dim->name v)
                                           used1 avoid))
                         (ispace-var-set-rename-ispace-vars
                          (set::delete v f) dim-renam shape-renam))))
  :cases ((member-equal (ispace-var-dim->name v)
                        (str::string-list-fix used1)))
  :use ((:instance not-in-ispace-var-set-rename-ispace-vars-when-fresh
                   (vars (set::delete v f))
                   (y (ispace-var-dim
                       (fresh-bind-name (ispace-var-dim->name v)
                                        used1 avoid))))
        (:instance set::subset-in
                   (a (fresh-bind-name (ispace-var-dim->name v) used1 avoid))
                   (x (ispace-var-set-names f))
                   (y (string-sfix avoid))))
  :enable ispace-var->name)

(defrule not-in-ispace-image-of-delete-of-fresh-bind-name-shape
  (implies (and (renaming-invariant-p dim-renam used avoid)
                (renaming-invariant-p shape-renam used avoid)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used1))
                (ispace-var-setp f)
                (set::subset (ispace-var-set-names f) (string-sfix avoid))
                (ispace-varp v)
                (equal (ispace-var-kind v) :shape))
           (not (set::in (ispace-var-shape
                          (fresh-bind-name (ispace-var-shape->name v)
                                           used1 avoid))
                         (ispace-var-set-rename-ispace-vars
                          (set::delete v f) dim-renam shape-renam))))
  :cases ((member-equal (ispace-var-shape->name v)
                        (str::string-list-fix used1)))
  :use ((:instance not-in-ispace-var-set-rename-ispace-vars-when-fresh
                   (vars (set::delete v f))
                   (y (ispace-var-shape
                       (fresh-bind-name (ispace-var-shape->name v)
                                        used1 avoid))))
        (:instance set::subset-in
                   (a (fresh-bind-name (ispace-var-shape->name v) used1 avoid))
                   (x (ispace-var-set-names f))
                   (y (string-sfix avoid))))
  :enable ispace-var->name)

(defrule not-in-type-image-of-delete-of-fresh-bind-name-atom
  (implies (and (renaming-invariant-p atom-renam used avoid)
                (renaming-invariant-p array-renam used avoid)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used1))
                (type-var-setp f)
                (set::subset (type-var-set-names f) (string-sfix avoid))
                (type-varp v)
                (equal (type-var-kind v) :atom))
           (not (set::in (type-var-atom
                          (fresh-bind-name (type-var-atom->name v)
                                           used1 avoid))
                         (type-var-set-rename-type-vars
                          (set::delete v f) atom-renam array-renam))))
  :cases ((member-equal (type-var-atom->name v)
                        (str::string-list-fix used1)))
  :use ((:instance not-in-type-var-set-rename-type-vars-when-fresh
                   (vars (set::delete v f))
                   (y (type-var-atom
                       (fresh-bind-name (type-var-atom->name v)
                                        used1 avoid))))
        (:instance set::subset-in
                   (a (fresh-bind-name (type-var-atom->name v) used1 avoid))
                   (x (type-var-set-names f))
                   (y (string-sfix avoid))))
  :enable type-var->name)

(defrule not-in-type-image-of-delete-of-fresh-bind-name-array
  (implies (and (renaming-invariant-p atom-renam used avoid)
                (renaming-invariant-p array-renam used avoid)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used1))
                (type-var-setp f)
                (set::subset (type-var-set-names f) (string-sfix avoid))
                (type-varp v)
                (equal (type-var-kind v) :array))
           (not (set::in (type-var-array
                          (fresh-bind-name (type-var-array->name v)
                                           used1 avoid))
                         (type-var-set-rename-type-vars
                          (set::delete v f) atom-renam array-renam))))
  :cases ((member-equal (type-var-array->name v)
                        (str::string-list-fix used1)))
  :use ((:instance not-in-type-var-set-rename-type-vars-when-fresh
                   (vars (set::delete v f))
                   (y (type-var-array
                       (fresh-bind-name (type-var-array->name v)
                                        used1 avoid))))
        (:instance set::subset-in
                   (a (fresh-bind-name (type-var-array->name v) used1 avoid))
                   (x (type-var-set-names f))
                   (y (string-sfix avoid))))
  :enable type-var->name)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; No-capture of the fresh parameter lists against the image of their scope,
; and the typing and no-duplicates facts the relation demands of them.

(define string-list-none-in-p ((l string-listp) (s string-setp))
  :returns (yes/no booleanp)
  (or (endp l)
      (and (not (set::in (str-fix (car l)) (string-sfix s)))
           (string-list-none-in-p (cdr l) s))))

(defrule emptyp-of-intersect-of-mergesort-when-string-list-none-in-p
  (implies (and (string-listp l)
                (string-setp s)
                (string-list-none-in-p l s))
           (set::emptyp (set::intersect (set::mergesort l) s)))
  :induct t
  :enable (string-list-none-in-p mergesort-of-cons mergesort-when-consp set::intersect-insert-x))

(define ispace-var-list-none-in-p ((l ispace-var-listp) (s ispace-var-setp))
  :returns (yes/no booleanp)
  (or (endp l)
      (and (not (set::in (ispace-var-fix (car l)) (ispace-var-set-fix s)))
           (ispace-var-list-none-in-p (cdr l) s))))

(defrule emptyp-of-intersect-of-mergesort-when-ispace-var-list-none-in-p
  (implies (and (ispace-var-listp l)
                (ispace-var-setp s)
                (ispace-var-list-none-in-p l s))
           (set::emptyp (set::intersect (set::mergesort l) s)))
  :induct t
  :enable (ispace-var-list-none-in-p mergesort-of-cons mergesort-when-consp set::intersect-insert-x))

(define type-var-list-none-in-p ((l type-var-listp) (s type-var-setp))
  :returns (yes/no booleanp)
  (or (endp l)
      (and (not (set::in (type-var-fix (car l)) (type-var-set-fix s)))
           (type-var-list-none-in-p (cdr l) s))))

(defrule emptyp-of-intersect-of-mergesort-when-type-var-list-none-in-p
  (implies (and (type-var-listp l)
                (type-var-setp s)
                (type-var-list-none-in-p l s))
           (set::emptyp (set::intersect (set::mergesort l) s)))
  :induct t
  :enable (type-var-list-none-in-p mergesort-of-cons mergesort-when-consp set::intersect-insert-x))

(defrule ispace-var-listp-of-uniq-ispace-var-params-new-params
  (ispace-var-listp (mv-nth 1 (uniq-ispace-var-params params used avoid
                                                      dim-renam shape-renam)))
  :induct (uniq-ispace-var-params params used avoid dim-renam shape-renam)
  :enable uniq-ispace-var-params)

(defrule type-var-listp-of-uniq-type-var-params-new-params
  (type-var-listp (mv-nth 1 (uniq-type-var-params params used avoid
                                                  atom-renam array-renam)))
  :induct (uniq-type-var-params params used avoid atom-renam array-renam)
  :enable uniq-type-var-params)

(defrule no-duplicatesp-equal-of-uniq-ispace-var-params-new-params
  (no-duplicatesp-equal (mv-nth 1 (uniq-ispace-var-params params used avoid
                                                          dim-renam
                                                          shape-renam)))
  :use ((:instance
         no-duplicatesp-equal-when-no-duplicatesp-equal-of-ispace-var-list->name
         (l (mv-nth 1 (uniq-ispace-var-params params used avoid
                                              dim-renam shape-renam))))))

(defrule no-duplicatesp-equal-of-uniq-type-var-params-new-params
  (no-duplicatesp-equal (mv-nth 1 (uniq-type-var-params params used avoid
                                                        atom-renam
                                                        array-renam)))
  :use ((:instance
         no-duplicatesp-equal-when-no-duplicatesp-equal-of-type-var-list->name
         (l (mv-nth 1 (uniq-type-var-params params used avoid
                                            atom-renam array-renam))))))

(defrule string-list-none-in-p-of-uniq-name-list-in-image-of-difference
  (implies (and (renaming-invariant-p m used avoid)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used1))
                (string-setp f)
                (set::subset f (string-sfix avoid))
                (subsetp-equal (str::string-list-fix names)
                               (str::string-list-fix names0)))
           (string-list-none-in-p
            (mv-nth 1 (uniq-name-list names used1 avoid))
            (rename-var-string-set
             (set::difference f (set::mergesort (str::string-list-fix names0)))
             m)))
  :induct (uniq-name-list names used1 avoid)
  :enable (uniq-name-list string-list-none-in-p set::in-mergesort)
  :hints (("Subgoal *1/2"
           :cases ((member-equal (str-fix (car names))
                                 (str::string-list-fix used1)))
           :use ((:instance not-in-rename-var-string-set-when-fresh
                            (names (set::difference
                                    f
                                    (set::mergesort
                                     (str::string-list-fix names0))))
                            (y (fresh-bind-name (car names) used1 avoid))
                            (renam m))
                 (:instance set::subset-in
                            (a (fresh-bind-name (car names) used1 avoid))
                            (x f)
                            (y (string-sfix avoid)))))))

(defrule emptyp-of-intersect-of-uniq-name-list-with-image-of-difference
  (implies (and (renaming-invariant-p m used avoid)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used1))
                (string-setp f)
                (set::subset f (string-sfix avoid))
                (string-listp names))
           (set::emptyp
            (set::intersect
             (set::mergesort (mv-nth 1 (uniq-name-list names used1 avoid)))
             (rename-var-string-set
              (set::difference f (set::mergesort names))
              m))))
  :use ((:instance
         string-list-none-in-p-of-uniq-name-list-in-image-of-difference
         (names0 names))))

(defrule ispace-var-list-none-in-p-of-uniq-ispace-var-params-in-image
  (implies (and (renaming-invariant-p dim-renam used avoid)
                (renaming-invariant-p shape-renam used avoid)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used1))
                (ispace-var-setp f)
                (set::subset (ispace-var-set-names f) (string-sfix avoid))
                (ispace-var-listp params)
                (ispace-var-listp params0)
                (subsetp-equal params params0))
           (ispace-var-list-none-in-p
            (mv-nth 1 (uniq-ispace-var-params params used1 avoid
                                              dim-renam1 shape-renam1))
            (ispace-var-set-rename-ispace-vars
             (set::difference f (set::mergesort params0))
             dim-renam shape-renam)))
  :induct (uniq-ispace-var-params params used1 avoid dim-renam1 shape-renam1)
  :enable (uniq-ispace-var-params ispace-var-list-none-in-p
           set::in-mergesort ispace-var->name)
  :hints (("Subgoal *1/2"
           :cases ((member-equal (ispace-var->name (car params))
                                 (str::string-list-fix used1)))
           :use ((:instance not-in-ispace-var-set-rename-ispace-vars-when-fresh
                            (vars (set::difference f (set::mergesort params0)))
                            (y (ispace-var-dim
                                (fresh-bind-name (ispace-var->name (car params))
                                                 used1 avoid))))
                 (:instance not-in-ispace-var-set-rename-ispace-vars-when-fresh
                            (vars (set::difference f (set::mergesort params0)))
                            (y (ispace-var-shape
                                (fresh-bind-name (ispace-var->name (car params))
                                                 used1 avoid))))
                 (:instance set::subset-in
                            (a (fresh-bind-name (ispace-var->name (car params))
                                                used1 avoid))
                            (x (ispace-var-set-names f))
                            (y (string-sfix avoid)))
                 (:instance ispace-var-dim-of-fields (x (car params)))
                 (:instance ispace-var-shape-of-fields (x (car params))))))
  :disable (not-in-ispace-var-set-rename-ispace-vars-when-fresh
            not-in-type-var-set-rename-type-vars-when-fresh
            not-in-ispace-var-set-when-name-not-in-names
            not-in-type-var-set-when-name-not-in-names
            acl2::member-equal-when-subsetp-equal-1
            string-listp
            in-names-when-in-rename-var-string-set-and-not-value
            acl2::ustring-true-list
            acl2::ustring?
            acl2::cdr-preserves-ustring
            acl2::consp-when-member-equal-of-cons-listp
            (:rewrite acl2::subsetp-member . 2)
            acl2::member-equal-of-cons-non-constant))

(defrule emptyp-of-intersect-of-uniq-ispace-var-params-with-image
  (implies (and (renaming-invariant-p dim-renam used avoid)
                (renaming-invariant-p shape-renam used avoid)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used1))
                (ispace-var-setp f)
                (set::subset (ispace-var-set-names f) (string-sfix avoid))
                (ispace-var-listp params))
           (set::emptyp
            (set::intersect
             (set::mergesort
              (mv-nth 1 (uniq-ispace-var-params params used1 avoid
                                                dim-renam1 shape-renam1)))
             (ispace-var-set-rename-ispace-vars
              (set::difference f (set::mergesort params))
              dim-renam shape-renam))))
  :use ((:instance ispace-var-list-none-in-p-of-uniq-ispace-var-params-in-image
                   (params0 params))))

(defrule type-var-list-none-in-p-of-uniq-type-var-params-in-image
  (implies (and (renaming-invariant-p atom-renam used avoid)
                (renaming-invariant-p array-renam used avoid)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used1))
                (type-var-setp f)
                (set::subset (type-var-set-names f) (string-sfix avoid))
                (type-var-listp params)
                (type-var-listp params0)
                (subsetp-equal params params0))
           (type-var-list-none-in-p
            (mv-nth 1 (uniq-type-var-params params used1 avoid
                                            atom-renam1 array-renam1))
            (type-var-set-rename-type-vars
             (set::difference f (set::mergesort params0))
             atom-renam array-renam)))
  :induct (uniq-type-var-params params used1 avoid atom-renam1 array-renam1)
  :enable (uniq-type-var-params type-var-list-none-in-p
           set::in-mergesort type-var->name)
  :hints (("Subgoal *1/2"
           :cases ((member-equal (type-var->name (car params))
                                 (str::string-list-fix used1)))
           :use ((:instance not-in-type-var-set-rename-type-vars-when-fresh
                            (vars (set::difference f (set::mergesort params0)))
                            (y (type-var-atom
                                (fresh-bind-name (type-var->name (car params))
                                                 used1 avoid))))
                 (:instance not-in-type-var-set-rename-type-vars-when-fresh
                            (vars (set::difference f (set::mergesort params0)))
                            (y (type-var-array
                                (fresh-bind-name (type-var->name (car params))
                                                 used1 avoid))))
                 (:instance set::subset-in
                            (a (fresh-bind-name (type-var->name (car params))
                                                used1 avoid))
                            (x (type-var-set-names f))
                            (y (string-sfix avoid)))
                 (:instance type-var-atom-of-fields (x (car params)))
                 (:instance type-var-array-of-fields (x (car params))))))
  :disable (not-in-ispace-var-set-rename-ispace-vars-when-fresh
            not-in-type-var-set-rename-type-vars-when-fresh
            not-in-ispace-var-set-when-name-not-in-names
            not-in-type-var-set-when-name-not-in-names
            acl2::member-equal-when-subsetp-equal-1
            string-listp
            in-names-when-in-rename-var-string-set-and-not-value
            acl2::ustring-true-list
            acl2::ustring?
            acl2::cdr-preserves-ustring
            acl2::consp-when-member-equal-of-cons-listp
            (:rewrite acl2::subsetp-member . 2)
            acl2::member-equal-of-cons-non-constant))

(defrule emptyp-of-intersect-of-uniq-type-var-params-with-image
  (implies (and (renaming-invariant-p atom-renam used avoid)
                (renaming-invariant-p array-renam used avoid)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used1))
                (type-var-setp f)
                (set::subset (type-var-set-names f) (string-sfix avoid))
                (type-var-listp params))
           (set::emptyp
            (set::intersect
             (set::mergesort
              (mv-nth 1 (uniq-type-var-params params used1 avoid
                                              atom-renam1 array-renam1)))
             (type-var-set-rename-type-vars
              (set::difference f (set::mergesort params))
              atom-renam array-renam))))
  :use ((:instance type-var-list-none-in-p-of-uniq-type-var-params-in-image
                   (params0 params))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Support sets of closure bodies: the names of the renamed free variables
; are map values or names of the free variables themselves, so the support
; invariant holds of them.

(defrule support-invariant-p-when-subset-of-values-and-avoided
  (implies (and (renaming-invariant-p m used avoid)
                (string-setp b)
                (string-setp names)
                (set::subset names (string-sfix avoid))
                (set::subset b (set::union
                                (omap::values (string-string-map-fix m))
                                names)))
           (support-invariant-p b used avoid))
  :enable (support-invariant-p renaming-invariant-p subset-lifting-rules)
  :use ((:instance set::subset-transitive
                   (x b)
                   (y (set::union (omap::values (string-string-map-fix m))
                                  names))
                   (z (set::union (set::mergesort (str::string-list-fix used))
                                  (string-sfix avoid))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Binds: no-capture of a bind name against a scope, and the invariant
; through the renamings extended by a bind and by a list of binds.

(defrule bind-nocapture-ok-of-uniq-bind
  (implies (and (renamings-invariant-p r used)
                (string-setp evars)
                (set::subset evars (var-renamings->avoid r))
                (type-var-setp tvars)
                (set::subset (type-var-set-names tvars)
                             (var-renamings->avoid r))
                (ispace-var-setp ivars)
                (set::subset (ispace-var-set-names ivars)
                             (var-renamings->avoid r)))
           (bind-nocapture-ok (mv-nth 1 (uniq-bind x used r)) x r
                              evars tvars ivars))
  :expand ((uniq-bind x used r))
  :enable (bind-nocapture-ok bind-name renamings-invariant-p
           ispace-var->name type-var->name))

(defrule renamings-invariant-p-of-bind-alpha-extended-renamings-of-uniq-bind
  (implies (renamings-invariant-p r used)
           (renamings-invariant-p
            (bind-alpha-extended-renamings (mv-nth 1 (uniq-bind x used r)) x r)
            (mv-nth 0 (uniq-bind x used r))))
  :expand ((uniq-bind x used r))
  :enable (bind-alpha-extended-renamings bind-name renamings-invariant-p
           ispace-var->name type-var->name))

(define uniq-bind-list-induct ((x bind-listp)
                               (used string-listp)
                               (r var-renamings-p))
  :returns (dummy true-listp)
  (b* (((when (endp x)) (list used r))
       ((mv used & r) (uniq-bind (car x) used r)))
    (uniq-bind-list-induct (cdr x) used r))
  :measure (len x)
  :verify-guards nil)

(defrule renamings-invariant-p-of-bind-list-alpha-extended-renamings-of-uniq-bind-list
  (implies (renamings-invariant-p r used)
           (renamings-invariant-p
            (bind-list-alpha-extended-renamings
             (mv-nth 1 (uniq-bind-list x used r)) x r)
            (mv-nth 0 (uniq-bind-list x used r))))
  :induct (uniq-bind-list-induct x used r)
  :expand ((uniq-bind-list x used r)
           (:free (nb) (bind-list-alpha-extended-renamings nb x r)))
  :enable uniq-bind-list-induct)

(defrule var-renamings->avoid-of-bind-alpha-extended-renamings
  (equal (var-renamings->avoid (bind-alpha-extended-renamings new-b b r))
         (var-renamings->avoid r))
  :enable bind-alpha-extended-renamings)

(defrule var-renamings->avoid-of-bind-list-alpha-extended-renamings
  (equal (var-renamings->avoid
          (bind-list-alpha-extended-renamings new-binds binds r))
         (var-renamings->avoid r))
  :induct (bind-list-alpha-extended-renamings new-binds binds r)
  :enable bind-list-alpha-extended-renamings)

(defrule bind-list-body-scope-fresh-ok-of-uniq-bind-list
  (implies (and (renamings-invariant-p r used)
                (string-setp evars)
                (set::subset evars (var-renamings->avoid r))
                (type-var-setp tvars)
                (set::subset (type-var-set-names tvars)
                             (var-renamings->avoid r))
                (ispace-var-setp ivars)
                (set::subset (ispace-var-set-names ivars)
                             (var-renamings->avoid r)))
           (bind-list-body-scope-fresh-ok
            (mv-nth 1 (uniq-bind-list x used r)) x r
            evars tvars ivars))
  :induct (uniq-bind-list-induct x used r)
  :expand ((uniq-bind-list x used r)
           (:free (nb) (bind-list-body-scope-fresh-ok nb x r evars tvars ivars)))
  :enable uniq-bind-list-induct)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rules for the bridge induction (UNIQ-FRESH-BRIDGE below): the invariant
; through the record and its extensions, in the normal forms the rewriter
; produces.

(defrule renaming-invariant-p-of-var-renamings->dim
  (implies (and (renamings-invariant-p r used)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used2)))
           (renaming-invariant-p (var-renamings->dim r) used2
                                 (var-renamings->avoid r)))
  :enable renamings-invariant-p)

(defrule renaming-invariant-p-of-var-renamings->shape
  (implies (and (renamings-invariant-p r used)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used2)))
           (renaming-invariant-p (var-renamings->shape r) used2
                                 (var-renamings->avoid r)))
  :enable renamings-invariant-p)

(defrule renaming-invariant-p-of-var-renamings->atom
  (implies (and (renamings-invariant-p r used)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used2)))
           (renaming-invariant-p (var-renamings->atom r) used2
                                 (var-renamings->avoid r)))
  :enable renamings-invariant-p)

(defrule renaming-invariant-p-of-var-renamings->array
  (implies (and (renamings-invariant-p r used)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used2)))
           (renaming-invariant-p (var-renamings->array r) used2
                                 (var-renamings->avoid r)))
  :enable renamings-invariant-p)

(defrule renaming-invariant-p-of-var-renamings->expr
  (implies (and (renamings-invariant-p r used)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used2)))
           (renaming-invariant-p (var-renamings->expr r) used2
                                 (var-renamings->avoid r)))
  :enable renamings-invariant-p)

(defrule renamings-invariant-p-of-var-renamings
  (equal (renamings-invariant-p
          (var-renamings dim shape atom array expr avoid) used)
         (and (renaming-invariant-p dim used avoid)
              (renaming-invariant-p shape used avoid)
              (renaming-invariant-p atom used avoid)
              (renaming-invariant-p array used avoid)
              (renaming-invariant-p expr used avoid)))
  :enable renamings-invariant-p)

(defrule renamings-invariant-p-when-subsetp-equal
  (implies (and (renamings-invariant-p r used)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used2)))
           (renamings-invariant-p r used2))
  :enable renamings-invariant-p)

(defrule renamings-avoid-p-of-var-renamings
  (equal (renamings-avoid-p (var-renamings dim shape atom array expr avoid))
         (and (map-values-avoid-p dim avoid)
              (map-values-avoid-p shape avoid)
              (map-values-avoid-p atom avoid)
              (map-values-avoid-p array avoid)
              (map-values-avoid-p expr avoid)))
  :enable renamings-avoid-p)

(defrule map-values-avoid-p-of-var-renamings->dim-when-renamings-invariant-p
  (implies (renamings-invariant-p r used)
           (map-values-avoid-p (var-renamings->dim r) (var-renamings->avoid r)))
  :enable (renamings-invariant-p renaming-invariant-p))

(defrule map-values-avoid-p-of-var-renamings->shape-when-renamings-invariant-p
  (implies (renamings-invariant-p r used)
           (map-values-avoid-p (var-renamings->shape r)
                               (var-renamings->avoid r)))
  :enable (renamings-invariant-p renaming-invariant-p))

(defrule map-values-avoid-p-of-var-renamings->atom-when-renamings-invariant-p
  (implies (renamings-invariant-p r used)
           (map-values-avoid-p (var-renamings->atom r)
                               (var-renamings->avoid r)))
  :enable (renamings-invariant-p renaming-invariant-p))

(defrule map-values-avoid-p-of-var-renamings->array-when-renamings-invariant-p
  (implies (renamings-invariant-p r used)
           (map-values-avoid-p (var-renamings->array r)
                               (var-renamings->avoid r)))
  :enable (renamings-invariant-p renaming-invariant-p))

(defrule map-values-avoid-p-of-var-renamings->expr-when-renamings-invariant-p
  (implies (renamings-invariant-p r used)
           (map-values-avoid-p (var-renamings->expr r)
                               (var-renamings->avoid r)))
  :enable (renamings-invariant-p renaming-invariant-p))

(defrule map-values-avoid-p-when-renaming-invariant-p
  (implies (renaming-invariant-p m used avoid)
           (map-values-avoid-p m avoid))
  :enable renaming-invariant-p)

(defrule renaming-invariant-p-of-extend-renaming-of-fresh-bind-name-gen
  (implies (and (renaming-invariant-p m used1 avoid)
                (subsetp-equal (cons (fresh-bind-name name used1 avoid)
                                     (str::string-list-fix used1))
                               (str::string-list-fix used2)))
           (renaming-invariant-p
            (extend-renaming name (fresh-bind-name name used1 avoid) m)
            used2 avoid))
  :use ((:instance renaming-invariant-p-of-extend-renaming-of-fresh-bind-name
                   (used used1))
        (:instance renaming-invariant-p-when-subsetp-equal
                   (m (extend-renaming name (fresh-bind-name name used1 avoid)
                                       m))
                   (used (cons (fresh-bind-name name used1 avoid)
                               (str::string-list-fix used1)))))
  :disable (renaming-invariant-p-of-extend-renaming-of-fresh-bind-name
            renaming-invariant-p-of-extend-renaming-of-fresh-bind-name-alt
            renaming-invariant-p-when-subsetp-equal))

(defrule renaming-invariant-p-of-extend-renaming-list-of-uniq-name-list-tight
  (implies (renaming-invariant-p m used1 avoid)
           (renaming-invariant-p
            (extend-renaming-list names
                                  (mv-nth 1 (uniq-name-list names used1 avoid))
                                  m)
            (mv-nth 0 (uniq-name-list names used1 avoid))
            avoid))
  :induct (uniq-name-list-fresh-induct names used1 avoid m b)
  :enable (uniq-name-list-fresh-induct uniq-name-list extend-renaming-list))

(defrule renaming-invariant-p-of-extend-renaming-list-of-uniq-name-list
  (implies (and (renaming-invariant-p m used1 avoid)
                (subsetp-equal (str::string-list-fix
                                (mv-nth 0 (uniq-name-list names used1 avoid)))
                               (str::string-list-fix used2)))
           (renaming-invariant-p
            (extend-renaming-list names
                                  (mv-nth 1 (uniq-name-list names used1 avoid))
                                  m)
            used2 avoid))
  :use ((:instance renaming-invariant-p-when-subsetp-equal
                   (m (extend-renaming-list
                       names
                       (mv-nth 1 (uniq-name-list names used1 avoid))
                       m))
                   (used (mv-nth 0 (uniq-name-list names used1 avoid)))))
  :disable renaming-invariant-p-when-subsetp-equal)

(defrule renaming-invariant-p-of-uniq-type-var-params-tight
  (implies (and (renaming-invariant-p atom-renam used1 avoid)
                (renaming-invariant-p array-renam used1 avoid))
           (b* (((mv new-used & new-atom new-array)
                 (uniq-type-var-params params used1 avoid
                                       atom-renam array-renam)))
             (and (renaming-invariant-p new-atom new-used avoid)
                  (renaming-invariant-p new-array new-used avoid))))
  :induct (uniq-type-var-params-fresh-induct params used1 avoid
                                             atom-renam array-renam b)
  :enable (uniq-type-var-params-fresh-induct uniq-type-var-params
           type-var->name)
  :disable uniq-type-var-params-to-uniq-name-list)

(defrule map-values-avoid-p-of-uniq-type-var-params-new-renams
  (implies (and (renaming-invariant-p atom-renam used1 avoid)
                (renaming-invariant-p array-renam used1 avoid))
           (b* (((mv & & new-atom new-array)
                 (uniq-type-var-params params used1 avoid
                                       atom-renam array-renam)))
             (and (map-values-avoid-p new-atom avoid)
                  (map-values-avoid-p new-array avoid))))
  :use (renaming-invariant-p-of-uniq-type-var-params-tight
        (:instance map-values-avoid-p-when-renaming-invariant-p
                   (m (mv-nth 2 (uniq-type-var-params params used1 avoid
                                                      atom-renam array-renam)))
                   (used (mv-nth 0 (uniq-type-var-params params used1 avoid
                                                         atom-renam
                                                         array-renam))))
        (:instance map-values-avoid-p-when-renaming-invariant-p
                   (m (mv-nth 3 (uniq-type-var-params params used1 avoid
                                                      atom-renam array-renam)))
                   (used (mv-nth 0 (uniq-type-var-params params used1 avoid
                                                         atom-renam
                                                         array-renam)))))
  :disable (renaming-invariant-p-of-uniq-type-var-params-tight
            renaming-invariant-p-when-subsetp-equal
            map-values-avoid-p-when-renaming-invariant-p))

(defrule renaming-invariant-p-of-uniq-type-var-params-tight-nf
  (implies (and (renaming-invariant-p atom-renam used1 avoid)
                (renaming-invariant-p array-renam used1 avoid))
           (b* (((mv & & new-atom new-array)
                 (uniq-type-var-params params used1 avoid
                                       atom-renam array-renam))
                (new-used (mv-nth 0 (uniq-name-list (type-var-list->name params)
                                                    used1 avoid))))
             (and (renaming-invariant-p new-atom new-used avoid)
                  (renaming-invariant-p new-array new-used avoid))))
  :use renaming-invariant-p-of-uniq-type-var-params-tight
  :disable renaming-invariant-p-of-uniq-type-var-params-tight)

(defrule renaming-invariant-p-of-uniq-type-var-params-new-atom-renam
  (implies (and (renaming-invariant-p atom-renam used1 avoid)
                (renaming-invariant-p array-renam used1 avoid)
                (subsetp-equal (str::string-list-fix
                                (mv-nth 0 (uniq-name-list
                                           (type-var-list->name params)
                                           used1 avoid)))
                               (str::string-list-fix used2)))
           (renaming-invariant-p
            (mv-nth 2 (uniq-type-var-params params used1 avoid
                                            atom-renam array-renam))
            used2 avoid))
  :use ((:instance renaming-invariant-p-when-subsetp-equal
                   (m (mv-nth 2 (uniq-type-var-params params used1 avoid
                                                      atom-renam array-renam)))
                   (used (mv-nth 0 (uniq-name-list (type-var-list->name params)
                                                   used1 avoid)))))
  :disable renaming-invariant-p-when-subsetp-equal)

(defrule renaming-invariant-p-of-uniq-type-var-params-new-array-renam
  (implies (and (renaming-invariant-p atom-renam used1 avoid)
                (renaming-invariant-p array-renam used1 avoid)
                (subsetp-equal (str::string-list-fix
                                (mv-nth 0 (uniq-name-list
                                           (type-var-list->name params)
                                           used1 avoid)))
                               (str::string-list-fix used2)))
           (renaming-invariant-p
            (mv-nth 3 (uniq-type-var-params params used1 avoid
                                            atom-renam array-renam))
            used2 avoid))
  :use ((:instance renaming-invariant-p-when-subsetp-equal
                   (m (mv-nth 3 (uniq-type-var-params params used1 avoid
                                                      atom-renam array-renam)))
                   (used (mv-nth 0 (uniq-name-list (type-var-list->name params)
                                                   used1 avoid)))))
  :disable renaming-invariant-p-when-subsetp-equal)

(defrule renaming-invariant-p-of-uniq-ispace-var-params-tight
  (implies (and (renaming-invariant-p dim-renam used1 avoid)
                (renaming-invariant-p shape-renam used1 avoid))
           (b* (((mv new-used & new-dim new-shape)
                 (uniq-ispace-var-params params used1 avoid
                                         dim-renam shape-renam)))
             (and (renaming-invariant-p new-dim new-used avoid)
                  (renaming-invariant-p new-shape new-used avoid))))
  :induct (uniq-ispace-var-params-fresh-induct params used1 avoid
                                               dim-renam shape-renam b)
  :enable (uniq-ispace-var-params-fresh-induct uniq-ispace-var-params
           ispace-var->name)
  :disable uniq-ispace-var-params-to-uniq-name-list)

(defrule map-values-avoid-p-of-uniq-ispace-var-params-new-renams
  (implies (and (renaming-invariant-p dim-renam used1 avoid)
                (renaming-invariant-p shape-renam used1 avoid))
           (b* (((mv & & new-dim new-shape)
                 (uniq-ispace-var-params params used1 avoid
                                         dim-renam shape-renam)))
             (and (map-values-avoid-p new-dim avoid)
                  (map-values-avoid-p new-shape avoid))))
  :use (renaming-invariant-p-of-uniq-ispace-var-params-tight
        (:instance map-values-avoid-p-when-renaming-invariant-p
                   (m (mv-nth 2 (uniq-ispace-var-params params used1 avoid
                                                        dim-renam shape-renam)))
                   (used (mv-nth 0 (uniq-ispace-var-params params used1 avoid
                                                           dim-renam
                                                           shape-renam))))
        (:instance map-values-avoid-p-when-renaming-invariant-p
                   (m (mv-nth 3 (uniq-ispace-var-params params used1 avoid
                                                        dim-renam shape-renam)))
                   (used (mv-nth 0 (uniq-ispace-var-params params used1 avoid
                                                           dim-renam
                                                           shape-renam)))))
  :disable (renaming-invariant-p-of-uniq-ispace-var-params-tight
            renaming-invariant-p-when-subsetp-equal
            map-values-avoid-p-when-renaming-invariant-p))

(defrule renaming-invariant-p-of-uniq-ispace-var-params-tight-nf
  (implies (and (renaming-invariant-p dim-renam used1 avoid)
                (renaming-invariant-p shape-renam used1 avoid))
           (b* (((mv & & new-dim new-shape)
                 (uniq-ispace-var-params params used1 avoid
                                         dim-renam shape-renam))
                (new-used (mv-nth 0 (uniq-name-list
                                     (ispace-var-list->name params)
                                     used1 avoid))))
             (and (renaming-invariant-p new-dim new-used avoid)
                  (renaming-invariant-p new-shape new-used avoid))))
  :use renaming-invariant-p-of-uniq-ispace-var-params-tight
  :disable renaming-invariant-p-of-uniq-ispace-var-params-tight)

(defrule renaming-invariant-p-of-uniq-ispace-var-params-new-dim-renam
  (implies (and (renaming-invariant-p dim-renam used1 avoid)
                (renaming-invariant-p shape-renam used1 avoid)
                (subsetp-equal (str::string-list-fix
                                (mv-nth 0 (uniq-name-list
                                           (ispace-var-list->name params)
                                           used1 avoid)))
                               (str::string-list-fix used2)))
           (renaming-invariant-p
            (mv-nth 2 (uniq-ispace-var-params params used1 avoid
                                              dim-renam shape-renam))
            used2 avoid))
  :use ((:instance renaming-invariant-p-when-subsetp-equal
                   (m (mv-nth 2 (uniq-ispace-var-params params used1 avoid
                                                        dim-renam shape-renam)))
                   (used (mv-nth 0 (uniq-name-list (ispace-var-list->name params)
                                                   used1 avoid)))))
  :disable renaming-invariant-p-when-subsetp-equal)

(defrule renaming-invariant-p-of-uniq-ispace-var-params-new-shape-renam
  (implies (and (renaming-invariant-p dim-renam used1 avoid)
                (renaming-invariant-p shape-renam used1 avoid)
                (subsetp-equal (str::string-list-fix
                                (mv-nth 0 (uniq-name-list
                                           (ispace-var-list->name params)
                                           used1 avoid)))
                               (str::string-list-fix used2)))
           (renaming-invariant-p
            (mv-nth 3 (uniq-ispace-var-params params used1 avoid
                                              dim-renam shape-renam))
            used2 avoid))
  :use ((:instance renaming-invariant-p-when-subsetp-equal
                   (m (mv-nth 3 (uniq-ispace-var-params params used1 avoid
                                                        dim-renam shape-renam)))
                   (used (mv-nth 0 (uniq-name-list (ispace-var-list->name params)
                                                   used1 avoid)))))
  :disable renaming-invariant-p-when-subsetp-equal)

(defrule support-invariant-p-of-mergesort-when-subsetp-equal-2
  (implies (and (string-listp names)
                (subsetp-equal names (str::string-list-fix used)))
           (support-invariant-p (set::mergesort names) used avoid))
  :use support-invariant-p-of-mergesort-when-subsetp-equal)

; The traversal's own facts state the two name lists appended; the append
; splits under ACL2::SUBSETP-EQUAL-OF-APPEND.

(defrule bind-name-of-uniq-bind-member-of-new-used
  (member-equal (bind-name (mv-nth 1 (uniq-bind x used r)))
                (str::string-list-fix (mv-nth 0 (uniq-bind x used r))))
  :use uniq-bind-facts
  :disable uniq-bind-facts)

(defrule bind-list-names-of-uniq-bind-list-subsetp-equal-new-used
  (subsetp-equal (bind-list-names (mv-nth 1 (uniq-bind-list x used r)))
                 (str::string-list-fix (mv-nth 0 (uniq-bind-list x used r))))
  :use uniq-bind-list-facts
  :disable uniq-bind-list-facts)

(defrule support-invariant-p-when-subset-of-two-values-and-avoided
  (implies (and (renaming-invariant-p m1 used avoid)
                (renaming-invariant-p m2 used avoid)
                (string-setp b)
                (string-setp names)
                (set::subset names (string-sfix avoid))
                (set::subset b (set::union
                                (omap::values (string-string-map-fix m1))
                                (set::union
                                 (omap::values (string-string-map-fix m2))
                                 names))))
           (support-invariant-p b used avoid))
  :enable (support-invariant-p renaming-invariant-p subset-lifting-rules)
  :use ((:instance set::subset-transitive
                   (x b)
                   (y (set::union
                       (omap::values (string-string-map-fix m1))
                       (set::union
                        (omap::values (string-string-map-fix m2))
                        names)))
                   (z (set::union (set::mergesort (str::string-list-fix used))
                                  (string-sfix avoid))))))

(defrule support-invariant-p-of-expr-body-support-names
  (implies (and (renamings-invariant-p r used)
                (set::subset (ispace-var-set-names (expr-all-ispace-vars body))
                             (var-renamings->avoid r))
                (set::subset (type-var-set-names (expr-all-type-vars body))
                             (var-renamings->avoid r))
                (set::subset (expr-all-expr-vars body)
                             (var-renamings->avoid r)))
           (support-invariant-p (expr-body-support-names body r) used
                                (var-renamings->avoid r)))
  :enable (expr-body-support-names renamings-invariant-p)
  :use ((:instance support-invariant-p-when-subset-of-two-values-and-avoided
                   (m1 (var-renamings->dim r))
                   (m2 (var-renamings->shape r))
                   (avoid (var-renamings->avoid r))
                   (b (ispace-var-set-names
                       (ispace-var-set-rename-ispace-vars
                        (expr-free-ispace-vars body)
                        (var-renamings->dim r)
                        (var-renamings->shape r))))
                   (names (ispace-var-set-names
                           (expr-free-ispace-vars body))))
        (:instance support-invariant-p-when-subset-of-two-values-and-avoided
                   (m1 (var-renamings->atom r))
                   (m2 (var-renamings->array r))
                   (avoid (var-renamings->avoid r))
                   (b (type-var-set-names
                       (type-var-set-rename-type-vars
                        (expr-free-type-vars body)
                        (var-renamings->atom r)
                        (var-renamings->array r))))
                   (names (type-var-set-names
                           (expr-free-type-vars body))))
        (:instance support-invariant-p-when-subset-of-values-and-avoided
                   (m (var-renamings->expr r))
                   (avoid (var-renamings->avoid r))
                   (b (rename-var-string-set
                       (expr-free-expr-vars body)
                       (var-renamings->expr r)))
                   (names (expr-free-expr-vars body)))
        (:instance subset-names-of-ispace-var-set-rename-ispace-vars
                   (vars (expr-free-ispace-vars body))
                   (dim-renam (var-renamings->dim r))
                   (shape-renam (var-renamings->shape r)))
        (:instance subset-names-of-type-var-set-rename-type-vars
                   (vars (expr-free-type-vars body))
                   (atom-renam (var-renamings->atom r))
                   (array-renam (var-renamings->array r)))
        (:instance subset-rename-var-string-set
                   (names (expr-free-expr-vars body))
                   (renam (var-renamings->expr r))))
  :disable (subset-names-of-ispace-var-set-rename-ispace-vars
            subset-names-of-type-var-set-rename-type-vars
            subset-rename-var-string-set
            support-invariant-p-when-subset-of-two-values-and-avoided
            support-invariant-p-when-subset-of-values-and-avoided))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Towards the bridge induction (UNIQ-FRESH-BRIDGE, after the layer lemmas
; for combined function binds below).  The invariant predicates stay closed
; in its proof: the rules above operate on the closed forms and on the
; constructor forms that the traversal builds.  The relation quantifies the
; support set per call, so the induction proves the conclusion for every
; support set at once (a DEFUN-SK per relation function, below) and the
; plain forms follow.

(in-theory (disable renamings-invariant-p renamings-avoid-p))

(defrule ispace-var-list-fresh-ok-of-singleton-dim
  (implies (and (ispace-varp v)
                (equal (ispace-var-kind v) :dim))
           (equal (ispace-var-list-fresh-ok (list (ispace-var-dim new))
                                            (list v)
                                            dim-renam shape-renam b)
                  (name-fresh-ok (ispace-var-dim->name v) new dim-renam b)))
  :enable ispace-var-list-fresh-ok)

(defrule ispace-var-list-fresh-ok-of-singleton-shape
  (implies (and (ispace-varp v)
                (equal (ispace-var-kind v) :shape))
           (equal (ispace-var-list-fresh-ok (list (ispace-var-shape new))
                                            (list v)
                                            dim-renam shape-renam b)
                  (name-fresh-ok (ispace-var-shape->name v) new shape-renam b)))
  :enable ispace-var-list-fresh-ok)

(defrule type-var-list-fresh-ok-of-singleton-atom
  (implies (and (type-varp v)
                (equal (type-var-kind v) :atom))
           (equal (type-var-list-fresh-ok (list (type-var-atom new))
                                          (list v)
                                          atom-renam array-renam b)
                  (name-fresh-ok (type-var-atom->name v) new atom-renam b)))
  :enable type-var-list-fresh-ok)

(defrule type-var-list-fresh-ok-of-singleton-array
  (implies (and (type-varp v)
                (equal (type-var-kind v) :array))
           (equal (type-var-list-fresh-ok (list (type-var-array new))
                                          (list v)
                                          atom-renam array-renam b)
                  (name-fresh-ok (type-var-array->name v) new array-renam b)))
  :enable type-var-list-fresh-ok)

(defrule uniq-name-list-of-singleton
  (equal (uniq-name-list (list name) used avoid)
         (mv (cons (fresh-bind-name name used avoid)
                   (str::string-list-fix used))
             (list (fresh-bind-name name used avoid))))
  :enable uniq-name-list)

(defrule uniq-ispace-var-params-of-singleton
  (equal (uniq-ispace-var-params (list var) used avoid dim-renam shape-renam)
         (b* ((name (ispace-var->name var))
              (new-name (fresh-bind-name name used avoid))
              (new-used (cons new-name (str::string-list-fix used))))
           (ispace-var-case
            var
            :dim (mv new-used
                     (list (ispace-var-dim new-name))
                     (extend-renaming name new-name dim-renam)
                     (string-string-map-fix shape-renam))
            :shape (mv new-used
                       (list (ispace-var-shape new-name))
                       (string-string-map-fix dim-renam)
                       (extend-renaming name new-name shape-renam)))))
  :enable (uniq-ispace-var-params uniq-name-list))

(defrule string-list-fresh-ok-of-nil
  (string-list-fresh-ok nil nil m b)
  :enable string-list-fresh-ok)

(defrule type-var-list-fresh-ok-of-nil
  (type-var-list-fresh-ok nil nil atom-renam array-renam b)
  :enable type-var-list-fresh-ok)

(defrule ispace-var-list-fresh-ok-of-nil
  (ispace-var-list-fresh-ok nil nil dim-renam shape-renam b)
  :enable ispace-var-list-fresh-ok)

(defrule not-in-rename-image-of-delete-of-fresh-bind-name-r
  (implies (and (renamings-invariant-p r used)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used1))
                (string-setp f)
                (set::subset f (var-renamings->avoid r))
                (stringp name))
           (not (set::in (fresh-bind-name name used1 (var-renamings->avoid r))
                         (rename-var-string-set (set::delete name f)
                                                (var-renamings->expr r)))))
  :use ((:instance not-in-rename-image-of-delete-of-fresh-bind-name
                   (m (var-renamings->expr r))
                   (avoid (var-renamings->avoid r))))
  :enable renamings-invariant-p)

(defrule not-in-ispace-image-of-delete-of-fresh-bind-name-dim-r
  (implies (and (renamings-invariant-p r used)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used1))
                (ispace-var-setp f)
                (set::subset (ispace-var-set-names f) (var-renamings->avoid r))
                (ispace-varp v)
                (equal (ispace-var-kind v) :dim))
           (not (set::in (ispace-var-dim
                          (fresh-bind-name (ispace-var-dim->name v)
                                           used1 (var-renamings->avoid r)))
                         (ispace-var-set-rename-ispace-vars
                          (set::delete v f)
                          (var-renamings->dim r)
                          (var-renamings->shape r)))))
  :use ((:instance not-in-ispace-image-of-delete-of-fresh-bind-name-dim
                   (dim-renam (var-renamings->dim r))
                   (shape-renam (var-renamings->shape r))
                   (avoid (var-renamings->avoid r))))
  :enable renamings-invariant-p)

(defrule not-in-ispace-image-of-delete-of-fresh-bind-name-shape-r
  (implies (and (renamings-invariant-p r used)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used1))
                (ispace-var-setp f)
                (set::subset (ispace-var-set-names f) (var-renamings->avoid r))
                (ispace-varp v)
                (equal (ispace-var-kind v) :shape))
           (not (set::in (ispace-var-shape
                          (fresh-bind-name (ispace-var-shape->name v)
                                           used1 (var-renamings->avoid r)))
                         (ispace-var-set-rename-ispace-vars
                          (set::delete v f)
                          (var-renamings->dim r)
                          (var-renamings->shape r)))))
  :use ((:instance not-in-ispace-image-of-delete-of-fresh-bind-name-shape
                   (dim-renam (var-renamings->dim r))
                   (shape-renam (var-renamings->shape r))
                   (avoid (var-renamings->avoid r))))
  :enable renamings-invariant-p)

(defrule not-in-type-image-of-delete-of-fresh-bind-name-atom-r
  (implies (and (renamings-invariant-p r used)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used1))
                (type-var-setp f)
                (set::subset (type-var-set-names f) (var-renamings->avoid r))
                (type-varp v)
                (equal (type-var-kind v) :atom))
           (not (set::in (type-var-atom
                          (fresh-bind-name (type-var-atom->name v)
                                           used1 (var-renamings->avoid r)))
                         (type-var-set-rename-type-vars
                          (set::delete v f)
                          (var-renamings->atom r)
                          (var-renamings->array r)))))
  :use ((:instance not-in-type-image-of-delete-of-fresh-bind-name-atom
                   (atom-renam (var-renamings->atom r))
                   (array-renam (var-renamings->array r))
                   (avoid (var-renamings->avoid r))))
  :enable renamings-invariant-p)

(defrule not-in-type-image-of-delete-of-fresh-bind-name-array-r
  (implies (and (renamings-invariant-p r used)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used1))
                (type-var-setp f)
                (set::subset (type-var-set-names f) (var-renamings->avoid r))
                (type-varp v)
                (equal (type-var-kind v) :array))
           (not (set::in (type-var-array
                          (fresh-bind-name (type-var-array->name v)
                                           used1 (var-renamings->avoid r)))
                         (type-var-set-rename-type-vars
                          (set::delete v f)
                          (var-renamings->atom r)
                          (var-renamings->array r)))))
  :use ((:instance not-in-type-image-of-delete-of-fresh-bind-name-array
                   (atom-renam (var-renamings->atom r))
                   (array-renam (var-renamings->array r))
                   (avoid (var-renamings->avoid r))))
  :enable renamings-invariant-p)

(defrule emptyp-of-intersect-of-uniq-name-list-with-image-of-difference-r
  (implies (and (renamings-invariant-p r used)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used1))
                (string-setp f)
                (set::subset f (var-renamings->avoid r))
                (string-listp names))
           (set::emptyp
            (set::intersect
             (set::mergesort (mv-nth 1 (uniq-name-list
                                        names used1 (var-renamings->avoid r))))
             (rename-var-string-set
              (set::difference f (set::mergesort names))
              (var-renamings->expr r)))))
  :use ((:instance emptyp-of-intersect-of-uniq-name-list-with-image-of-difference
                   (m (var-renamings->expr r))
                   (avoid (var-renamings->avoid r))))
  :enable renamings-invariant-p)

(defrule emptyp-of-intersect-of-uniq-ispace-var-params-with-image-r
  (implies (and (renamings-invariant-p r used)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used1))
                (ispace-var-setp f)
                (set::subset (ispace-var-set-names f) (var-renamings->avoid r))
                (ispace-var-listp params))
           (set::emptyp
            (set::intersect
             (set::mergesort
              (mv-nth 1 (uniq-ispace-var-params params used1
                                                (var-renamings->avoid r)
                                                dim-renam1 shape-renam1)))
             (ispace-var-set-rename-ispace-vars
              (set::difference f (set::mergesort params))
              (var-renamings->dim r)
              (var-renamings->shape r)))))
  :use ((:instance emptyp-of-intersect-of-uniq-ispace-var-params-with-image
                   (dim-renam (var-renamings->dim r))
                   (shape-renam (var-renamings->shape r))
                   (avoid (var-renamings->avoid r))))
  :enable renamings-invariant-p)

(defrule emptyp-of-intersect-of-uniq-type-var-params-with-image-r
  (implies (and (renamings-invariant-p r used)
                (subsetp-equal (str::string-list-fix used)
                               (str::string-list-fix used1))
                (type-var-setp f)
                (set::subset (type-var-set-names f) (var-renamings->avoid r))
                (type-var-listp params))
           (set::emptyp
            (set::intersect
             (set::mergesort
              (mv-nth 1 (uniq-type-var-params params used1
                                              (var-renamings->avoid r)
                                              atom-renam1 array-renam1)))
             (type-var-set-rename-type-vars
              (set::difference f (set::mergesort params))
              (var-renamings->atom r)
              (var-renamings->array r)))))
  :use ((:instance emptyp-of-intersect-of-uniq-type-var-params-with-image
                   (atom-renam (var-renamings->atom r))
                   (array-renam (var-renamings->array r))
                   (avoid (var-renamings->avoid r))))
  :enable renamings-invariant-p)

(defrule ispace-var-kind-of-bind-ispace->var-of-uniq-bind
  (implies (equal (bind-kind x) :ispace)
           (equal (ispace-var-kind (bind-ispace->var (mv-nth 1 (uniq-bind x used r))))
                  (ispace-var-kind (bind-ispace->var x))))
  :expand ((uniq-bind x used r)))

(defrule type-var-kind-of-bind-type->var-of-uniq-bind
  (implies (equal (bind-kind x) :type)
           (equal (type-var-kind (bind-type->var (mv-nth 1 (uniq-bind x used r))))
                  (type-var-kind (bind-type->var x))))
  :expand ((uniq-bind x used r)))

(defrule bind-val->var-of-uniq-bind-member-of-new-used
  (implies (equal (bind-kind x) :val)
           (member-equal (bind-val->var (mv-nth 1 (uniq-bind x used r)))
                         (str::string-list-fix (mv-nth 0 (uniq-bind x used r)))))
  :use bind-name-of-uniq-bind-member-of-new-used
  :enable (bind-name bind-kind-of-uniq-bind))

(defrule bind-fun->var-of-uniq-bind-member-of-new-used
  (implies (equal (bind-kind x) :fun)
           (member-equal (bind-fun->var (mv-nth 1 (uniq-bind x used r)))
                         (str::string-list-fix (mv-nth 0 (uniq-bind x used r)))))
  :use bind-name-of-uniq-bind-member-of-new-used
  :enable (bind-name bind-kind-of-uniq-bind))

(defrule bind-tfun->var-of-uniq-bind-member-of-new-used
  (implies (equal (bind-kind x) :tfun)
           (member-equal (bind-tfun->var (mv-nth 1 (uniq-bind x used r)))
                         (str::string-list-fix (mv-nth 0 (uniq-bind x used r)))))
  :use bind-name-of-uniq-bind-member-of-new-used
  :enable (bind-name bind-kind-of-uniq-bind))

(defrule bind-ifun->var-of-uniq-bind-member-of-new-used
  (implies (equal (bind-kind x) :ifun)
           (member-equal (bind-ifun->var (mv-nth 1 (uniq-bind x used r)))
                         (str::string-list-fix (mv-nth 0 (uniq-bind x used r)))))
  :use bind-name-of-uniq-bind-member-of-new-used
  :enable (bind-name bind-kind-of-uniq-bind))

(defrule bind-cfun->var-of-uniq-bind-member-of-new-used
  (implies (equal (bind-kind x) :cfun)
           (member-equal (bind-cfun->var (mv-nth 1 (uniq-bind x used r)))
                         (str::string-list-fix (mv-nth 0 (uniq-bind x used r)))))
  :use bind-name-of-uniq-bind-member-of-new-used
  :enable (bind-name bind-kind-of-uniq-bind))

(defrule bind-ispace-dim-name-of-uniq-bind-member-of-new-used
  (implies (and (equal (bind-kind x) :ispace)
                (equal (ispace-var-kind (bind-ispace->var x)) :dim))
           (member-equal (ispace-var-dim->name
                          (bind-ispace->var (mv-nth 1 (uniq-bind x used r))))
                         (str::string-list-fix (mv-nth 0 (uniq-bind x used r)))))
  :use bind-name-of-uniq-bind-member-of-new-used
  :enable (bind-name bind-kind-of-uniq-bind ispace-var->name))

(defrule bind-ispace-shape-name-of-uniq-bind-member-of-new-used
  (implies (and (equal (bind-kind x) :ispace)
                (equal (ispace-var-kind (bind-ispace->var x)) :shape))
           (member-equal (ispace-var-shape->name
                          (bind-ispace->var (mv-nth 1 (uniq-bind x used r))))
                         (str::string-list-fix (mv-nth 0 (uniq-bind x used r)))))
  :use bind-name-of-uniq-bind-member-of-new-used
  :enable (bind-name bind-kind-of-uniq-bind ispace-var->name))

(defrule bind-type-atom-name-of-uniq-bind-member-of-new-used
  (implies (and (equal (bind-kind x) :type)
                (equal (type-var-kind (bind-type->var x)) :atom))
           (member-equal (type-var-atom->name
                          (bind-type->var (mv-nth 1 (uniq-bind x used r))))
                         (str::string-list-fix (mv-nth 0 (uniq-bind x used r)))))
  :use bind-name-of-uniq-bind-member-of-new-used
  :enable (bind-name bind-kind-of-uniq-bind type-var->name))

(defrule bind-type-array-name-of-uniq-bind-member-of-new-used
  (implies (and (equal (bind-kind x) :type)
                (equal (type-var-kind (bind-type->var x)) :array))
           (member-equal (type-var-array->name
                          (bind-type->var (mv-nth 1 (uniq-bind x used r))))
                         (str::string-list-fix (mv-nth 0 (uniq-bind x used r)))))
  :use bind-name-of-uniq-bind-member-of-new-used
  :enable (bind-name bind-kind-of-uniq-bind type-var->name))

(defun-sk expr-fresh-all-p (new-x x r used)
  (forall (b)
          (implies (support-invariant-p b used (var-renamings->avoid r))
                   (expr-alpha-fresh-p new-x x r b)))
  :rewrite :direct)

(defun-sk expr-list-fresh-all-p (new-x x r used)
  (forall (b)
          (implies (support-invariant-p b used (var-renamings->avoid r))
                   (expr-list-alpha-fresh-p new-x x r b)))
  :rewrite :direct)

(defun-sk atom-fresh-all-p (new-x x r used)
  (forall (b)
          (implies (support-invariant-p b used (var-renamings->avoid r))
                   (atom-alpha-fresh-p new-x x r b)))
  :rewrite :direct)

(defun-sk atom-list-fresh-all-p (new-x x r used)
  (forall (b)
          (implies (support-invariant-p b used (var-renamings->avoid r))
                   (atom-list-alpha-fresh-p new-x x r b)))
  :rewrite :direct)

(defun-sk bind-fresh-all-p (new-x x r used)
  (forall (b)
          (implies (support-invariant-p b used (var-renamings->avoid r))
                   (bind-alpha-fresh-p new-x x r b)))
  :rewrite :direct)

(defun-sk bind-list-fresh-all-p (new-x x r used)
  (forall (b)
          (implies (support-invariant-p b used (var-renamings->avoid r))
                   (bind-list-alpha-fresh-p new-x x r b)))
  :rewrite :direct)

(in-theory (disable expr-fresh-all-p expr-list-fresh-all-p atom-fresh-all-p
                    atom-list-fresh-all-p bind-fresh-all-p
                    bind-list-fresh-all-p))

(defrule support-invariant-p-of-expr-body-support-names-gen
  (implies (and (renamings-invariant-p r used)
                (set::subset (ispace-var-set-names (expr-all-ispace-vars body))
                             (var-renamings->avoid r))
                (set::subset (type-var-set-names (expr-all-type-vars body))
                             (var-renamings->avoid r))
                (set::subset (expr-all-expr-vars body)
                             (var-renamings->avoid r))
                (equal (string-sfix avoid) (var-renamings->avoid r)))
           (support-invariant-p (expr-body-support-names body r) used avoid))
  :use support-invariant-p-of-expr-body-support-names
  :disable support-invariant-p-of-expr-body-support-names)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The support sets of the layers of a combined function bind (see
; CFUN-LAYER-SUPPORT) satisfy the support invariant when the incoming one
; does, the new parameter names are used, and the renamed free variables
; of the layer's body are (by the invariant of the renamings and the
; avoidance of all the body's variables): these are the facts that the
; abstraction atom cases establish for their support sets, so the layer
; conditions of the bind reduce to the atom cases' obligations.  The all-
; variable sets of the desugared layers are those of their components.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; All variables of the desugaring layers.

(defruled expr-all-ispace-vars-of-cfun-ilambda-expr
  (implies (ispace-var-listp iparams)
           (equal (expr-all-ispace-vars (cfun-ilambda-expr iparams expr))
                  (set::union (set::mergesort iparams) (expr-all-ispace-vars expr))))
  :expand ((:free (d a) (expr-all-ispace-vars (expr-array d a)))
           (:free (a l) (atom-list-all-ispace-vars (cons a l)))
           (atom-list-all-ispace-vars nil)
           (dim-list-all-ispace-vars nil)
           (:free (ps b) (atom-all-ispace-vars (atom-ilambdan ps b)))
           (:free (p b) (atom-all-ispace-vars (atom-ilambda p b)))
           (len iparams)
           (len (cdr iparams)))
  :enable (cfun-ilambda-expr
           make-atom-ilambda/ilambdan
           mergesort-of-cons
           len))

(defruled expr-all-ispace-vars-of-cfun-lambda-expr
  (implies (typep type)
           (equal (expr-all-ispace-vars (cfun-lambda-expr params expr type))
                  (if (consp params)
                      (set::union (var+type?-list-all-ispace-vars params)
                                  (set::union (expr-all-ispace-vars expr)
                                              (type-all-ispace-vars type)))
                    (expr-all-ispace-vars expr))))
  :expand ((:free (d a) (expr-all-ispace-vars (expr-array d a)))
           (:free (a l) (atom-list-all-ispace-vars (cons a l)))
           (atom-list-all-ispace-vars nil)
           (dim-list-all-ispace-vars nil)
           (:free (ps b t?) (atom-all-ispace-vars (atom-lambdan ps b t?)))
           (:free (p b t?) (atom-all-ispace-vars (atom-lambda p b t?)))
           (len params)
           (len (cdr params))
           (var+type?-list-all-ispace-vars params)
           (var+type?-list-all-ispace-vars (cdr params))
           (:free (x) (type-option-all-ispace-vars x)))
  :enable (cfun-lambda-expr
           make-atom-lambda/lambdan
           type-option-some->val-when-typep
           len))

(defrule expr-all-type-vars-of-cfun-ilambda-expr
  (equal (expr-all-type-vars (cfun-ilambda-expr iparams expr))
         (expr-all-type-vars expr))
  :expand ((:free (d a) (expr-all-type-vars (expr-array d a)))
           (:free (a l) (atom-list-all-type-vars (cons a l)))
           (atom-list-all-type-vars nil)
           (:free (ps b) (atom-all-type-vars (atom-ilambdan ps b)))
           (:free (p b) (atom-all-type-vars (atom-ilambda p b)))
           (len iparams)
           (len (cdr iparams)))
  :enable (cfun-ilambda-expr
           make-atom-ilambda/ilambdan
           len))

(defruled expr-all-type-vars-of-cfun-lambda-expr
  (implies (typep type)
           (equal (expr-all-type-vars (cfun-lambda-expr params expr type))
                  (if (consp params)
                      (set::union (var+type?-list-all-type-vars params)
                                  (set::union (expr-all-type-vars expr)
                                              (type-all-type-vars type)))
                    (expr-all-type-vars expr))))
  :expand ((:free (d a) (expr-all-type-vars (expr-array d a)))
           (:free (a l) (atom-list-all-type-vars (cons a l)))
           (atom-list-all-type-vars nil)
           (:free (ps b t?) (atom-all-type-vars (atom-lambdan ps b t?)))
           (:free (p b t?) (atom-all-type-vars (atom-lambda p b t?)))
           (len params)
           (len (cdr params))
           (var+type?-list-all-type-vars params)
           (var+type?-list-all-type-vars (cdr params))
           (:free (x) (type-option-all-type-vars x)))
  :enable (cfun-lambda-expr
           make-atom-lambda/lambdan
           type-option-some->val-when-typep
           len))

(defrule expr-all-expr-vars-of-cfun-ilambda-expr
  (equal (expr-all-expr-vars (cfun-ilambda-expr iparams expr))
         (expr-all-expr-vars expr))
  :expand ((:free (d a) (expr-all-expr-vars (expr-array d a)))
           (:free (a l) (atom-list-all-expr-vars (cons a l)))
           (atom-list-all-expr-vars nil)
           (:free (ps b) (atom-all-expr-vars (atom-ilambdan ps b)))
           (:free (p b) (atom-all-expr-vars (atom-ilambda p b)))
           (len iparams)
           (len (cdr iparams)))
  :enable (cfun-ilambda-expr
           make-atom-ilambda/ilambdan
           len))

(defruled expr-all-expr-vars-of-cfun-lambda-expr
  (implies (var+type?-listp params)
           (equal (expr-all-expr-vars (cfun-lambda-expr params expr type))
                  (set::union (set::mergesort (var+type?-list->var params))
                              (expr-all-expr-vars expr))))
  :expand ((:free (d a) (expr-all-expr-vars (expr-array d a)))
           (:free (a l) (atom-list-all-expr-vars (cons a l)))
           (atom-list-all-expr-vars nil)
           (:free (ps b t?) (atom-all-expr-vars (atom-lambdan ps b t?)))
           (:free (p b t?) (atom-all-expr-vars (atom-lambda p b t?)))
           (len params)
           (len (cdr params))
           (var+type?-list->var params)
           (var+type?-list->var (cdr params)))
  :enable (cfun-lambda-expr
           make-atom-lambda/lambdan
           mergesort-of-cons
           len))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The avoidance of all the variables of the inner layers, from that of
; their components, in the form in which the support invariant lemma
; consumes it (the exact all-variable sets of the term abstraction layer
; depend on whether there are parameters, which the bridge does not split
; on).

(defrule subset-names-of-expr-all-ispace-vars-of-cfun-lambda-expr
  (implies (and (typep type)
                (set::subset (ispace-var-set-names
                              (var+type?-list-all-ispace-vars params))
                             avoid)
                (set::subset (ispace-var-set-names (expr-all-ispace-vars expr))
                             avoid)
                (set::subset (ispace-var-set-names (type-all-ispace-vars type))
                             avoid))
           (set::subset (ispace-var-set-names
                         (expr-all-ispace-vars (cfun-lambda-expr params expr type)))
                        avoid))
  :enable (expr-all-ispace-vars-of-cfun-lambda-expr
           ispace-var-set-names-of-union
           set::union-subset-x))

(defrule subset-names-of-expr-all-type-vars-of-cfun-lambda-expr
  (implies (and (typep type)
                (set::subset (type-var-set-names
                              (var+type?-list-all-type-vars params))
                             avoid)
                (set::subset (type-var-set-names (expr-all-type-vars expr))
                             avoid)
                (set::subset (type-var-set-names (type-all-type-vars type))
                             avoid))
           (set::subset (type-var-set-names
                         (expr-all-type-vars (cfun-lambda-expr params expr type)))
                        avoid))
  :enable (expr-all-type-vars-of-cfun-lambda-expr
           type-var-set-names-of-union
           set::union-subset-x))

(defrule subset-expr-all-expr-vars-of-cfun-lambda-expr
  (implies (and (var+type?-listp params)
                (set::subset (set::mergesort (var+type?-list->var params)) avoid)
                (set::subset (expr-all-expr-vars expr) avoid))
           (set::subset (expr-all-expr-vars (cfun-lambda-expr params expr type))
                        avoid))
  :enable (expr-all-expr-vars-of-cfun-lambda-expr
           set::union-subset-x))

(defrule subset-names-of-expr-all-ispace-vars-of-cfun-ilambda-expr
  (implies (and (ispace-var-listp iparams)
                (set::subset (ispace-var-set-names (set::mergesort iparams))
                             avoid)
                (set::subset (ispace-var-set-names (expr-all-ispace-vars expr))
                             avoid))
           (set::subset (ispace-var-set-names
                         (expr-all-ispace-vars (cfun-ilambda-expr iparams expr)))
                        avoid))
  :enable (expr-all-ispace-vars-of-cfun-ilambda-expr
           ispace-var-set-names-of-union
           set::union-subset-x))

(defrule support-invariant-p-of-cfun-layer-support
  (implies (and (support-invariant-p bset used avoid)
                (support-invariant-p (set::mergesort
                                      (str::string-list-fix new-names))
                                     used avoid)
                (support-invariant-p (expr-body-support-names body r)
                                     used avoid))
           (support-invariant-p (cfun-layer-support params new-names body r bset)
                                used avoid))
  :enable cfun-layer-support)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The bridge induction: under the invariant of the renamings, and with all
; the variables of the subterm among the avoided names, the uniquifier's
; output satisfies the freshness relation at every support set that
; satisfies the support invariant (the quantified forms).

(defret-mutual uniq-fresh-bridge
  (defret expr-fresh-all-p-of-uniq-expr
    (implies (and (renamings-invariant-p r used)
                  (set::subset (ispace-var-set-names (expr-all-ispace-vars x))
                               (var-renamings->avoid r))
                  (set::subset (type-var-set-names (expr-all-type-vars x))
                               (var-renamings->avoid r))
                  (set::subset (expr-all-expr-vars x)
                               (var-renamings->avoid r)))
             (expr-fresh-all-p new-x x r used))
    :fn uniq-expr)
  (defret expr-list-fresh-all-p-of-uniq-expr-list
    (implies (and (renamings-invariant-p r used)
                  (set::subset (ispace-var-set-names (expr-list-all-ispace-vars x))
                               (var-renamings->avoid r))
                  (set::subset (type-var-set-names (expr-list-all-type-vars x))
                               (var-renamings->avoid r))
                  (set::subset (expr-list-all-expr-vars x)
                               (var-renamings->avoid r)))
             (expr-list-fresh-all-p new-x x r used))
    :fn uniq-expr-list)
  (defret atom-fresh-all-p-of-uniq-atom
    (implies (and (renamings-invariant-p r used)
                  (set::subset (ispace-var-set-names (atom-all-ispace-vars x))
                               (var-renamings->avoid r))
                  (set::subset (type-var-set-names (atom-all-type-vars x))
                               (var-renamings->avoid r))
                  (set::subset (atom-all-expr-vars x)
                               (var-renamings->avoid r)))
             (atom-fresh-all-p new-x x r used))
    :fn uniq-atom)
  (defret atom-list-fresh-all-p-of-uniq-atom-list
    (implies (and (renamings-invariant-p r used)
                  (set::subset (ispace-var-set-names (atom-list-all-ispace-vars x))
                               (var-renamings->avoid r))
                  (set::subset (type-var-set-names (atom-list-all-type-vars x))
                               (var-renamings->avoid r))
                  (set::subset (atom-list-all-expr-vars x)
                               (var-renamings->avoid r)))
             (atom-list-fresh-all-p new-x x r used))
    :fn uniq-atom-list)
  (defret bind-fresh-all-p-of-uniq-bind
    (implies (and (renamings-invariant-p r used)
                  (set::subset (ispace-var-set-names (bind-all-ispace-vars x))
                               (var-renamings->avoid r))
                  (set::subset (type-var-set-names (bind-all-type-vars x))
                               (var-renamings->avoid r))
                  (set::subset (bind-all-expr-vars x)
                               (var-renamings->avoid r)))
             (bind-fresh-all-p new-x x r used))
    :fn uniq-bind)
  (defret bind-list-fresh-all-p-of-uniq-bind-list
    (implies (and (renamings-invariant-p r used)
                  (set::subset (ispace-var-set-names (bind-list-all-ispace-vars x))
                               (var-renamings->avoid r))
                  (set::subset (type-var-set-names (bind-list-all-type-vars x))
                               (var-renamings->avoid r))
                  (set::subset (bind-list-all-expr-vars x)
                               (var-renamings->avoid r)))
             (bind-list-fresh-all-p new-x x r used))
    :fn uniq-bind-list)
  :mutual-recursion uniquify-names-impl
  :hints
  (("Goal"
    :expand (
             (uniq-expr x used r)
             (uniq-expr-list x used r)
             (uniq-atom x used r)
             (uniq-atom-list x used r)
             (uniq-bind x used r)
             (uniq-bind-list x used r)
             (:free (new-x) (expr-fresh-all-p new-x x r used))
             (:free (new-x) (expr-list-fresh-all-p new-x x r used))
             (:free (new-x) (atom-fresh-all-p new-x x r used))
             (:free (new-x) (atom-list-fresh-all-p new-x x r used))
             (:free (new-x) (bind-fresh-all-p new-x x r used))
             (:free (new-x) (bind-list-fresh-all-p new-x x r used))
             (:free (new-x b) (expr-alpha-fresh-p new-x x r b))
             (:free (new-x b) (expr-list-alpha-fresh-p new-x x r b))
             (:free (new-x b) (atom-alpha-fresh-p new-x x r b))
             (:free (new-x b) (atom-list-alpha-fresh-p new-x x r b))
             (:free (new-x b) (bind-alpha-fresh-p new-x x r b))
             (:free (new-x b) (bind-list-alpha-fresh-p new-x x r b))
             (expr-all-ispace-vars x)
             (expr-all-type-vars x)
             (expr-all-expr-vars x)
             (expr-list-all-ispace-vars x)
             (expr-list-all-type-vars x)
             (expr-list-all-expr-vars x)
             (atom-all-ispace-vars x)
             (atom-all-type-vars x)
             (atom-all-expr-vars x)
             (atom-list-all-ispace-vars x)
             (atom-list-all-type-vars x)
             (atom-list-all-expr-vars x)
             (bind-all-ispace-vars x)
             (bind-all-type-vars x)
             (bind-all-expr-vars x)
             (bind-list-all-ispace-vars x)
             (bind-list-all-type-vars x)
             (bind-list-all-expr-vars x))
    :in-theory (e/d (bind-kind-of-uniq-bind
                     bind-name
                     type-var->name
                     ispace-var->name
                     type-var-list-alpha-extend
                     ispace-var-list-alpha-extend
                     uniq-expr-params-new-renam-to-extend-renaming-list
                     type-var-list-alpha-extend-of-uniq-type-var-params
                     ispace-var-list-alpha-extend-of-uniq-ispace-var-params
                     uniq-ispace-var-params-when-endp
                     uniq-type-var-params-when-endp
                     uniq-name-list-when-endp
                     var+type?-list->var-of-var+type?-list-rename-all-vars
                     var+type?-all-ispace-vars
                     var+type?-all-type-vars
                     len-of-uniq-name-list-new-names
                     len-of-uniq-expr-params-new-params
                     list-of-car-when-len-1
                     len
                     len-of-uniq-ispace-var-params)
                    (uniq-expr uniq-expr-list uniq-atom
                     uniq-atom-list uniq-bind uniq-bind-list
                     expr-alpha-fresh-p expr-list-alpha-fresh-p
                     atom-alpha-fresh-p atom-list-alpha-fresh-p
                     bind-alpha-fresh-p bind-list-alpha-fresh-p
                     bind-alpha-extended-renamings
                     bind-list-alpha-extended-renamings
                     renamings-invariant-p
                     renamings-avoid-p
                     expr-body-support-names
                     type-fresh-ok type-option-fresh-ok type-list-fresh-ok
                     type-list-option-fresh-ok var+type?-list-types-fresh-ok
                     name-fresh-ok
                     string-list-fresh-ok type-var-list-fresh-ok
                     ispace-var-list-fresh-ok
                     bind-nocapture-ok bind-list-body-scope-fresh-ok
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

; The plain form, at any support set satisfying the support invariant.

(defrule expr-alpha-fresh-p-of-uniq-expr
  (implies (and (renamings-invariant-p r used)
                (support-invariant-p b used (var-renamings->avoid r))
                (set::subset (ispace-var-set-names (expr-all-ispace-vars x))
                             (var-renamings->avoid r))
                (set::subset (type-var-set-names (expr-all-type-vars x))
                             (var-renamings->avoid r))
                (set::subset (expr-all-expr-vars x)
                             (var-renamings->avoid r)))
           (expr-alpha-fresh-p (mv-nth 1 (uniq-expr x used r)) x r b))
  :use expr-fresh-all-p-of-uniq-expr
  :disable expr-fresh-all-p-of-uniq-expr)

; The top-level theorem: the output of EXPR-UNIQUIFY-NAMES is fresh at
; the empty renamings (avoiding all the variable names of the expression)
; for every support set within the initial used names --- the free
; variables and the primitive operations' names --- and the avoided names;
; the main induction's top-level instance (UNIQUE-NAMES-VALIDATION) takes
; the primitive operations' names as its support set.

(defrule renaming-invariant-p-of-nil
  (renaming-invariant-p nil used avoid)
  :enable (renaming-invariant-p map-values-avoid-p))

(defrule expr-alpha-fresh-p-of-expr-uniquify-names
  (implies (support-invariant-p b
                                (set::union (expr-free-var-names expr)
                                            (primop-names))
                                (expr-all-var-names expr))
           (expr-alpha-fresh-p (expr-uniquify-names expr)
                               expr
                               (make-var-renamings :dim nil
                                                   :shape nil
                                                   :atom nil
                                                   :array nil
                                                   :expr nil
                                                   :avoid (expr-all-var-names expr))
                               b))
  :enable (expr-uniquify-names subset-lifting-rules)
  :use ((:instance expr-alpha-fresh-p-of-uniq-expr
                   (x (expr-fix expr))
                   (used (set::union (expr-free-var-names expr) (primop-names)))
                   (r (make-var-renamings :dim nil
                                          :shape nil
                                          :atom nil
                                          :array nil
                                          :expr nil
                                          :avoid (expr-all-var-names expr))))
        (:instance subset-ispace-var-set-names-when-dim-and-shape-names-subset
                   (vars (expr-all-ispace-vars expr))
                   (a (expr-all-var-names expr)))
        (:instance subset-type-var-set-names-when-atom-and-array-names-subset
                   (vars (expr-all-type-vars expr))
                   (a (expr-all-var-names expr))))
  :disable expr-alpha-fresh-p-of-uniq-expr
  :hints (("Goal" :expand ((expr-all-var-names expr)))))

