; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Stephen Westfold (westfold@kestrel.edu)
;          Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-structurals")

(local (include-book "osets"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ variable-name-sets
  :parents (abstract-syntax-variable-operations)
  :short "Name strings of tagged variables, and of sets and lists of them."
  :long
  (xdoc::topstring
   (xdoc::p
    "Ispace variables are tagged with a sort and type variables with a
     kind (see @(tsee ispace-var) and @(tsee type-var)), so a set of them
     splits into two sets of name strings, one per namespace: see
     @(tsee dim/shape-names-of-ispace-vars) and
     @(tsee atom/array-names-of-type-vars).  Some purposes instead want
     the names of both namespaces together, which is what
     @(tsee ispace-var-set-names) and @(tsee type-var-set-names) yield.")
   (xdoc::p
    "This book collects the theory of these operations: membership and
     the distribution over the set operations, the containments between
     the split and joint forms, and the fact that a tagged variable is
     determined by its tag and its name."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Names of a set of variables, one namespace at a time.

(defrule in-of-dim-names-of-ispace-vars
  (implies (ispace-var-setp vars)
           (equal (set::in name
                           (mv-nth 0 (dim/shape-names-of-ispace-vars vars)))
                  (and (stringp name)
                       (set::in (ispace-var-dim name) vars))))
  :induct t
  :enable (dim/shape-names-of-ispace-vars
           equal-of-ispace-var-dim
           set::in))

(defrule in-of-shape-names-of-ispace-vars
  (implies (ispace-var-setp vars)
           (equal (set::in name
                           (mv-nth 1 (dim/shape-names-of-ispace-vars vars)))
                  (and (stringp name)
                       (set::in (ispace-var-shape name) vars))))
  :induct t
  :enable (dim/shape-names-of-ispace-vars
           equal-of-ispace-var-shape
           set::in))

(defrulel setp-of-dim-names-of-ispace-vars
  (set::setp (mv-nth 0 (dim/shape-names-of-ispace-vars vars)))
  :use string-setp-of-dim/shape-names-of-ispace-vars.dim-names
  :disable string-setp-of-dim/shape-names-of-ispace-vars.dim-names)

(defrulel setp-of-shape-names-of-ispace-vars
  (set::setp (mv-nth 1 (dim/shape-names-of-ispace-vars vars)))
  :use string-setp-of-dim/shape-names-of-ispace-vars.shape-names
  :disable string-setp-of-dim/shape-names-of-ispace-vars.shape-names)

(defrule shape-names-of-ispace-vars-of-union
  (implies (and (ispace-var-setp vars1)
                (ispace-var-setp vars2))
           (equal (mv-nth 1 (dim/shape-names-of-ispace-vars
                             (set::union vars1 vars2)))
                  (set::union
                   (mv-nth 1 (dim/shape-names-of-ispace-vars vars1))
                   (mv-nth 1 (dim/shape-names-of-ispace-vars vars2)))))
  :enable (set::double-containment set::pick-a-point-subset-strategy))

(defrule dim-names-of-ispace-vars-of-insert
  (implies (and (ispace-varp var)
                (ispace-var-setp vars))
           (equal (mv-nth 0 (dim/shape-names-of-ispace-vars
                             (set::insert var vars)))
                  (if (ispace-var-case var :dim)
                      (set::insert (ispace-var-dim->name var)
                                   (mv-nth 0 (dim/shape-names-of-ispace-vars
                                              vars)))
                    (mv-nth 0 (dim/shape-names-of-ispace-vars vars)))))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy
           equal-of-ispace-var-dim))

(defrule shape-names-of-ispace-vars-of-insert
  (implies (and (ispace-varp var)
                (ispace-var-setp vars))
           (equal (mv-nth 1 (dim/shape-names-of-ispace-vars
                             (set::insert var vars)))
                  (if (ispace-var-case var :shape)
                      (set::insert (ispace-var-shape->name var)
                                   (mv-nth 1 (dim/shape-names-of-ispace-vars
                                              vars)))
                    (mv-nth 1 (dim/shape-names-of-ispace-vars vars)))))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy
           equal-of-ispace-var-shape))

;;;;;;;;;;;;;;;;;;;;

(defrule in-of-atom-names-of-type-vars
  (implies (type-var-setp vars)
           (equal (set::in name
                           (mv-nth 0 (atom/array-names-of-type-vars vars)))
                  (and (stringp name)
                       (set::in (type-var-atom name) vars))))
  :induct t
  :enable (atom/array-names-of-type-vars
           equal-of-type-var-atom
           set::in))

(defrule in-of-array-names-of-type-vars
  (implies (type-var-setp vars)
           (equal (set::in name
                           (mv-nth 1 (atom/array-names-of-type-vars vars)))
                  (and (stringp name)
                       (set::in (type-var-array name) vars))))
  :induct t
  :enable (atom/array-names-of-type-vars
           equal-of-type-var-array
           set::in))

(local
 (defrule setp-of-atom-names-of-type-vars
   (set::setp (mv-nth 0 (atom/array-names-of-type-vars vars)))
   :use string-setp-of-atom/array-names-of-type-vars.atom-names
   :disable string-setp-of-atom/array-names-of-type-vars.atom-names))

(local
 (defrule setp-of-array-names-of-type-vars
   (set::setp (mv-nth 1 (atom/array-names-of-type-vars vars)))
   :use string-setp-of-atom/array-names-of-type-vars.array-names
   :disable string-setp-of-atom/array-names-of-type-vars.array-names))

(defrule atom-names-of-type-vars-of-insert
  (implies (and (type-varp var)
                (type-var-setp vars))
           (equal (mv-nth 0 (atom/array-names-of-type-vars
                             (set::insert var vars)))
                  (if (type-var-case var :atom)
                      (set::insert (type-var-atom->name var)
                                   (mv-nth 0 (atom/array-names-of-type-vars
                                              vars)))
                    (mv-nth 0 (atom/array-names-of-type-vars vars)))))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy
           equal-of-type-var-atom))

(defrule array-names-of-type-vars-of-insert
  (implies (and (type-varp var)
                (type-var-setp vars))
           (equal (mv-nth 1 (atom/array-names-of-type-vars
                             (set::insert var vars)))
                  (if (type-var-case var :array)
                      (set::insert (type-var-array->name var)
                                   (mv-nth 1 (atom/array-names-of-type-vars
                                              vars)))
                    (mv-nth 1 (atom/array-names-of-type-vars vars)))))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy
           equal-of-type-var-array))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Names of a set of variables, both namespaces together.

(define ispace-var-set-names ((vars ispace-var-setp))
  :returns (names string-setp)
  :short "Name strings of a set of ispace variables."
  (b* (((when (set::emptyp (ispace-var-set-fix vars))) nil))
    (set::insert (ispace-var->name (set::head vars))
                 (ispace-var-set-names (set::tail vars))))
  :prepwork ((local (in-theory (enable emptyp-of-ispace-var-set-fix))))
  :verify-guards :after-returns)

(defrulel setp-of-ispace-var-set-names
  (set::setp (ispace-var-set-names vars))
  :use string-setp-of-ispace-var-set-names
  :disable string-setp-of-ispace-var-set-names)

(defrule in-of-ispace-var-set-names
  (implies (ispace-var-setp vars)
           (equal (set::in name (ispace-var-set-names vars))
                  (and (stringp name)
                       (or (set::in (ispace-var-dim name) vars)
                           (set::in (ispace-var-shape name) vars)))))
  :induct t
  :enable (ispace-var-set-names
           ispace-var->name
           equal-of-ispace-var-dim
           equal-of-ispace-var-shape
           set::in))

(defrule in-ispace-var-set-names-when-in
  (implies (and (ispace-var-setp vars)
                (set::in var vars))
           (set::in (ispace-var->name var) (ispace-var-set-names vars)))
  :induct t
  :enable (ispace-var-set-names set::in))

(defrule subset-dim-names-of-ispace-var-set-names
  (implies (ispace-var-setp vars)
           (set::subset (mv-nth 0 (dim/shape-names-of-ispace-vars vars))
                        (ispace-var-set-names vars)))
  :enable set::pick-a-point-subset-strategy)

(defrule subset-shape-names-of-ispace-var-set-names
  (implies (ispace-var-setp vars)
           (set::subset (mv-nth 1 (dim/shape-names-of-ispace-vars vars))
                        (ispace-var-set-names vars)))
  :enable set::pick-a-point-subset-strategy)

(defrule ispace-var-set-names-of-insert
  (implies (and (ispace-varp var)
                (ispace-var-setp vars))
           (equal (ispace-var-set-names (set::insert var vars))
                  (set::insert (ispace-var->name var)
                               (ispace-var-set-names vars))))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy
           ispace-var->name
           equal-of-ispace-var-dim
           equal-of-ispace-var-shape))

(defrule ispace-var-set-names-of-union
  (implies (and (ispace-var-setp vars1)
                (ispace-var-setp vars2))
           (equal (ispace-var-set-names (set::union vars1 vars2))
                  (set::union (ispace-var-set-names vars1)
                              (ispace-var-set-names vars2))))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy))

(defrule subset-dim-names-when-subset-ispace-var-set-names
  (implies (and (ispace-var-setp vars)
                (set::subset (ispace-var-set-names vars) a))
           (set::subset (mv-nth 0 (dim/shape-names-of-ispace-vars vars)) a))
  :use ((:instance set::subset-transitive
                   (x (mv-nth 0 (dim/shape-names-of-ispace-vars vars)))
                   (y (ispace-var-set-names vars))
                   (z a))))

(defrule subset-shape-names-when-subset-ispace-var-set-names
  (implies (and (ispace-var-setp vars)
                (set::subset (ispace-var-set-names vars) a))
           (set::subset (mv-nth 1 (dim/shape-names-of-ispace-vars vars)) a))
  :use ((:instance set::subset-transitive
                   (x (mv-nth 1 (dim/shape-names-of-ispace-vars vars)))
                   (y (ispace-var-set-names vars))
                   (z a))))

(defrule subset-ispace-var-set-names-when-subset
  (implies (and (ispace-var-setp vars)
                (ispace-var-setp vars2)
                (set::subset vars vars2)
                (set::subset (ispace-var-set-names vars2) a))
           (set::subset (ispace-var-set-names vars) a))
  :enable (set::pick-a-point-subset-strategy set::subset-in))

(defrule subset-ispace-var-set-names-when-dim-and-shape-names-subset
  (implies (and (ispace-var-setp vars)
                (set::subset (mv-nth 0 (dim/shape-names-of-ispace-vars vars)) a)
                (set::subset (mv-nth 1 (dim/shape-names-of-ispace-vars vars)) a))
           (set::subset (ispace-var-set-names vars) a))
  :enable (set::pick-a-point-subset-strategy set::subset-in))

(defrule not-in-ispace-var-set-when-name-not-in-names
  (implies (and (ispace-var-setp vars)
                (not (set::in (ispace-var->name y) (ispace-var-set-names vars))))
           (not (set::in y vars))))

;;;;;;;;;;;;;;;;;;;;

(define type-var-set-names ((vars type-var-setp))
  :returns (names string-setp)
  :short "Name strings of a set of type variables."
  (b* (((when (set::emptyp (type-var-set-fix vars))) nil))
    (set::insert (type-var->name (set::head vars))
                 (type-var-set-names (set::tail vars))))
  :prepwork ((local (in-theory (enable emptyp-of-type-var-set-fix))))
  :verify-guards :after-returns)

(defrulel setp-of-type-var-set-names
  (set::setp (type-var-set-names vars))
  :use string-setp-of-type-var-set-names
  :disable string-setp-of-type-var-set-names)

(defrule in-of-type-var-set-names
  (implies (type-var-setp vars)
           (equal (set::in name (type-var-set-names vars))
                  (and (stringp name)
                       (or (set::in (type-var-atom name) vars)
                           (set::in (type-var-array name) vars)))))
  :induct t
  :enable (type-var-set-names
           type-var->name
           equal-of-type-var-atom
           equal-of-type-var-array
           set::in))

(defrule in-type-var-set-names-when-in
  (implies (and (type-var-setp vars)
                (set::in var vars))
           (set::in (type-var->name var) (type-var-set-names vars)))
  :induct t
  :enable (type-var-set-names set::in))

(defrule subset-atom-names-of-type-var-set-names
  (implies (type-var-setp vars)
           (set::subset (mv-nth 0 (atom/array-names-of-type-vars vars))
                        (type-var-set-names vars)))
  :enable set::pick-a-point-subset-strategy)

(defrule subset-array-names-of-type-var-set-names
  (implies (type-var-setp vars)
           (set::subset (mv-nth 1 (atom/array-names-of-type-vars vars))
                        (type-var-set-names vars)))
  :enable set::pick-a-point-subset-strategy)

(defrule type-var-set-names-of-insert
  (implies (and (type-varp var)
                (type-var-setp vars))
           (equal (type-var-set-names (set::insert var vars))
                  (set::insert (type-var->name var)
                               (type-var-set-names vars))))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy
           type-var->name
           equal-of-type-var-atom
           equal-of-type-var-array))

(defrule type-var-set-names-of-union
  (implies (and (type-var-setp vars1)
                (type-var-setp vars2))
           (equal (type-var-set-names (set::union vars1 vars2))
                  (set::union (type-var-set-names vars1)
                              (type-var-set-names vars2))))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy))

(defrule subset-atom-names-when-subset-type-var-set-names
  (implies (and (type-var-setp vars)
                (set::subset (type-var-set-names vars) a))
           (set::subset (mv-nth 0 (atom/array-names-of-type-vars vars)) a))
  :use ((:instance set::subset-transitive
                   (x (mv-nth 0 (atom/array-names-of-type-vars vars)))
                   (y (type-var-set-names vars))
                   (z a))))

(defrule subset-array-names-when-subset-type-var-set-names
  (implies (and (type-var-setp vars)
                (set::subset (type-var-set-names vars) a))
           (set::subset (mv-nth 1 (atom/array-names-of-type-vars vars)) a))
  :use ((:instance set::subset-transitive
                   (x (mv-nth 1 (atom/array-names-of-type-vars vars)))
                   (y (type-var-set-names vars))
                   (z a))))

(defrule subset-type-var-set-names-when-subset
  (implies (and (type-var-setp vars)
                (type-var-setp vars2)
                (set::subset vars vars2)
                (set::subset (type-var-set-names vars2) a))
           (set::subset (type-var-set-names vars) a))
  :enable (set::pick-a-point-subset-strategy set::subset-in))

(defrule subset-type-var-set-names-when-atom-and-array-names-subset
  (implies (and (type-var-setp vars)
                (set::subset (mv-nth 0 (atom/array-names-of-type-vars vars)) a)
                (set::subset (mv-nth 1 (atom/array-names-of-type-vars vars)) a))
           (set::subset (type-var-set-names vars) a))
  :enable (set::pick-a-point-subset-strategy set::subset-in))

(defrule not-in-type-var-set-when-name-not-in-names
  (implies (and (type-var-setp vars)
                (not (set::in (type-var->name y) (type-var-set-names vars))))
           (not (set::in y vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A tagged variable is determined by its tag and its name.  The rules that
; decompose a constructor application are disabled in these two proofs, so
; that the two sides stay in constructor form long enough to be identified.

(defrule ispace-var-equal-when-same-kind-and-name
  (implies (and (ispace-varp a)
                (ispace-varp b)
                (equal (ispace-var-kind a) (ispace-var-kind b))
                (equal (ispace-var->name a) (ispace-var->name b)))
           (equal a b))
  :rule-classes nil
  :use ((:instance ispace-var-dim-of-fields (x a))
        (:instance ispace-var-dim-of-fields (x b))
        (:instance ispace-var-shape-of-fields (x a))
        (:instance ispace-var-shape-of-fields (x b)))
  :disable (equal-of-ispace-var-dim
            equal-of-ispace-var-shape
            ispace-var-dim-of-fields
            ispace-var-shape-of-fields)
  :enable ispace-var->name)

(defrule type-var-equal-when-same-kind-and-name
  (implies (and (type-varp a)
                (type-varp b)
                (equal (type-var-kind a) (type-var-kind b))
                (equal (type-var->name a) (type-var->name b)))
           (equal a b))
  :rule-classes nil
  :use ((:instance type-var-atom-of-fields (x a))
        (:instance type-var-atom-of-fields (x b))
        (:instance type-var-array-of-fields (x a))
        (:instance type-var-array-of-fields (x b)))
  :disable (equal-of-type-var-atom
            equal-of-type-var-array
            type-var-atom-of-fields
            type-var-array-of-fields)
  :enable type-var->name)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Names of a list of variables.

(defrule member-equal-of-ispace-var-list->name-when-member-equal
  (implies (member-equal v l)
           (member-equal (ispace-var->name v) (ispace-var-list->name l)))
  :induct t
  :enable ispace-var-list->name)

(defrule member-equal-of-type-var-list->name-when-member-equal
  (implies (member-equal v l)
           (member-equal (type-var->name v) (type-var-list->name l)))
  :induct t
  :enable type-var-list->name)

(defrule no-duplicatesp-equal-when-no-duplicatesp-equal-of-ispace-var-list->name
  (implies (no-duplicatesp-equal (ispace-var-list->name l))
           (no-duplicatesp-equal l))
  :induct t
  :enable (ispace-var-list->name no-duplicatesp-equal))

(defrule no-duplicatesp-equal-when-no-duplicatesp-equal-of-type-var-list->name
  (implies (no-duplicatesp-equal (type-var-list->name l))
           (no-duplicatesp-equal l))
  :induct t
  :enable (type-var-list->name no-duplicatesp-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identifying a tagged variable by its tag and its name.
;
; These are the working forms of the extensionality above, in the shapes the
; proofs meet: an equality of the variables themselves from the equality of
; their names under a known tag, and membership of a reconstructed variable
; in a set.  Each is supplied by :USE rather than
; left to the rewriter, since the fixtype rules that decompose a constructor
; application would otherwise undo the reconstruction.

(defruled ispace-var-equal-by-dim-name
  (implies (and (ispace-varp x)
                (ispace-varp y)
                (equal (ispace-var-kind x) :dim)
                (equal (ispace-var-kind y) :dim)
                (equal (ispace-var-dim->name x)
                       (ispace-var-dim->name y)))
           (equal (equal x y) t))
  :use ((:instance ispace-var-fix-when-dim (x x))
        (:instance ispace-var-fix-when-dim (x y))))

(defruled ispace-var-equal-by-shape-name
  (implies (and (ispace-varp x)
                (ispace-varp y)
                (equal (ispace-var-kind x) :shape)
                (equal (ispace-var-kind y) :shape)
                (equal (ispace-var-shape->name x)
                       (ispace-var-shape->name y)))
           (equal (equal x y) t))
  :use ((:instance ispace-var-fix-when-shape (x x))
        (:instance ispace-var-fix-when-shape (x y))))

(defruled type-var-equal-by-atom-name
  (implies (and (type-varp x)
                (type-varp y)
                (equal (type-var-kind x) :atom)
                (equal (type-var-kind y) :atom)
                (equal (type-var-atom->name x)
                       (type-var-atom->name y)))
           (equal (equal x y) t))
  :use ((:instance type-var-fix-when-atom (x x))
        (:instance type-var-fix-when-atom (x y))))

(defruled type-var-equal-by-array-name
  (implies (and (type-varp x)
                (type-varp y)
                (equal (type-var-kind x) :array)
                (equal (type-var-kind y) :array)
                (equal (type-var-array->name x)
                       (type-var-array->name y)))
           (equal (equal x y) t))
  :use ((:instance type-var-fix-when-array (x x))
        (:instance type-var-fix-when-array (x y))))

(defruled in-of-ispace-var-dim-by-kind-name
  (implies (and (ispace-varp v)
                (equal (ispace-var-kind v) :dim)
                (equal (ispace-var-dim->name v) n)
                (set::in v s))
           (set::in (ispace-var-dim n) s))
  :use ((:instance ispace-var-fix-when-dim (x v))))

(defruled in-of-ispace-var-shape-by-kind-name
  (implies (and (ispace-varp v)
                (equal (ispace-var-kind v) :shape)
                (equal (ispace-var-shape->name v) n)
                (set::in v s))
           (set::in (ispace-var-shape n) s))
  :use ((:instance ispace-var-fix-when-shape (x v))))

(defruled in-of-type-var-atom-by-kind-name
  (implies (and (type-varp v)
                (equal (type-var-kind v) :atom)
                (equal (type-var-atom->name v) n)
                (set::in v s))
           (set::in (type-var-atom n) s))
  :use ((:instance type-var-fix-when-atom (x v))))

(defruled in-of-type-var-array-by-kind-name
  (implies (and (type-varp v)
                (equal (type-var-kind v) :array)
                (equal (type-var-array->name v) n)
                (set::in v s))
           (set::in (type-var-array n) s))
  :use ((:instance type-var-fix-when-array (x v))))
