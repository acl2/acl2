(in-package "OMAP")

(include-book "core")
(include-book "assoc")
(include-book "extensionality")
(include-book "compatiblep")
(include-book "submap")
(include-book "update")

(include-book "std/osets/cardinality" :dir :system)
(include-book "std/osets/intersect" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compose ((x mapp) (y mapp))
  :returns (map1 mapp)
  (if (emptyp y)
      nil
      (mv-let (key val) (head y)
        (let ((pair (assoc val x)))
          (if (consp pair)
              (update key (cdr pair) (compose x (tail y)))
              (compose x (tail y))))))
  :verify-guards :after-returns

  ///

  (defcong mequiv equal (compose x y) 1)

  (defcong mequiv equal (compose x y) 2)

  (defrule assoc-of-compose
      (equal (assoc key (compose x y))
             (and (assoc key y)
                  (assoc (cdr (assoc key y)) x)
                  (cons key
                        (cdr (assoc (cdr (assoc key y)) x))))))

  (defrule assoc-of-compose-associativity
      (equal (assoc key (compose (compose x y) z))
             (assoc key (compose x (compose y z)))))

  (defrule compose-associativity
      (equal (compose (compose x y) z)
             (compose x (compose y z)))
    :enable extensionality))

#|
Skip these for now

; Size/cardinality properties
(defrule cardinality-values-compose-1
    (implies (and (mapp x) (mapp y))
             (<= (set::cardinality (values (compose x y)))
                 (set::cardinality (values x)))))

(defrule cardinality-values-compose-2
    (implies (and (mapp x) (mapp y))
             (<= (set::cardinality (values (compose x y)))
                 (set::cardinality (values y)))))
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identityp ((x mapp))
  :returns (yes/no booleanp)
  (and (mapp x)
       (or (emptyp x)
           (mv-let (key val) (head x)
             (and (equal key val)
                  (identityp (tail x))))))
  
  ///
  
  (defrule identityp-implies-mapp
      (implies (identityp x)
               (mapp x))
    :rule-classes :forward-chaining)

  (defruled identityp-implies-equal-keys-values
      (implies (identityp map)
               (equal (values map)
                      (keys map)))
    :enable (values keys)
    :rule-classes :forward-chaining)

  (defrule assoc-of-identityp
      (implies (identityp x)
               (equal (assoc key x)
                      (and (set::in key (keys x))
                           (cons key key)))))

  (defruled identityp-equal-when-equal-keys
      (implies (and (identityp x)
                    (identityp y)
                    (equal (keys x)
                           (keys y)))
               (equal x y))
    :enable extensionality
    :rule-classes :forward-chaining)

  (defrule assoc-of-compose-restrict-when-identityp
      (implies (and (mapp map) (identityp idmap))
               (equal (assoc key (compose map idmap))
                      (assoc key (restrict (keys idmap)
                                           map))))
    :enable (assoc-of-restrict assoc))

  (defruled compose-is-restrict-when-identityp
      (implies (and (mapp map) (identityp idmap))
               (equal (compose map idmap)
                      (restrict (keys idmap) map)))
    :enable extensionality)

  (defrule assoc-of-self-compose-when-identityp
      (implies (identityp map)
               (equal (assoc key (compose map map))
                      (assoc key map)))
    :disable assoc-of-compose-restrict-when-identityp)

  (defrule self-compose-is-equal-when-identityp
      (implies (identityp map)
               (equal (compose map map)
                      map))
    :enable extensionality))

; Copied from Alessandro
(define injectivep ((map mapp))
  :returns (yes/no booleanp)
  :short "Check if an omap is injective."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, different keys are mapped to different values.
     We express this via a recursion:
     the empty map is injective;
     a non-empty map if injective iff
     the value of its first key is not among the values of the tail of the map,
     and the tail of the map is itself injective."))
  (and (mapp map)
       (or (emptyp map)
           (b* (((mv & val) (head map)))
             (and (not (set::in val (values (tail map))))
                  (injectivep (tail map))))))
  ///

  (defrule injectivep-implies-mapp
      (implies (injectivep x)
               (mapp x))
    :rule-classes :forward-chaining)

  (defrule injectivep-implies-injectivep-tail
      (implies (and (not (emptyp x))
                    (injectivep x))
               (injectivep (tail x)))
    :rule-classes :forward-chaining)

  (defrule injectivep-implies-equal-cardinality-keys-values
      (implies (injectivep x)
               (equal (set::cardinality (keys x))
                      (set::cardinality (values x))))
    :enable (keys values set::insert-cardinality)
    :rule-classes :forward-chaining)

  (defrule equal-cardinality-keys-values-implies-injectivep
      (implies (and (mapp x)
                    (equal (set::cardinality (keys x))
                           (set::cardinality (values x))))
               (injectivep x))
    :enable (keys values set::insert-cardinality)
    :rule-classes :forward-chaining
    :prep-lemmas
    ((defrule cardinality-values-<=-keys
         (<= (set::cardinality (values x))
             (set::cardinality (keys x)))
       :enable (keys values set::insert-cardinality)
       :rule-classes :linear)))

  (defruled injectivep-is-equal-cardinality-keys-values
      (implies (mapp x)
               (equal (injectivep x)
                      (equal (set::cardinality (keys x))
                             (set::cardinality (values x))))))
  (defrule identityp-implies-injectivep
      (implies (identityp x)
               (injectivep x))
    :prep-lemmas
    ((defrule identityp-implies-equal-cardinality-keys-values
         (implies (identityp x)
                  (equal (set::cardinality (keys x))
                         (set::cardinality (values x))))
       :enable identityp-implies-equal-keys-values
       :rule-classes :forward-chaining))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule compatiblep-implies-equal-assoc-restrict-intersect-keys
    (implies (compatiblep map0 map1)
             (equal (assoc k (restrict (set::intersect (keys map0) (keys map1))
                                       map0))
                    (assoc k (restrict (set::intersect (keys map0) (keys map1))
                                       map1))))
  :enable assoc-of-restrict)

; The -> direction
(defrule compatiblep-implies-equal-restrict-intersect-keys
    (implies (compatiblep map0 map1)
             (equal (restrict (set::intersect (keys map0) (keys map1)) map0)
                    (restrict (set::intersect (keys map0) (keys map1)) map1)))
  :enable extensionality
  :rule-classes :forward-chaining)

; The <- direction
(skip-proofs
 (defrule equal-restrict-intersect-keys-implies-compatiblep
     (implies (equal (restrict (set::intersect (keys map0) (keys map1)) map0)
                     (restrict (set::intersect (keys map0) (keys map1)) map1))
              (compatiblep map0 map1))
   :enable (restrict compatiblep keys set::intersect-insert-X)))

(defrule compatiblep-is-equal-restrict-intersect-keys
    (equal (compatiblep map0 map1)
           (equal (restrict (set::intersect (keys map0) (keys map1)) map0)
                  (restrict (set::intersect (keys map0) (keys map1)) map1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-values ((values set::setp) (map mapp))
  :returns (map1 mapp)
  (cond ((emptyp map) nil)
        (t (mv-let (key val)
               (head map)
             (if (set::in val values)
                 (update key val (restrict-values values
                                                   (tail map)))
               (restrict-values values (tail map))))))
  :verify-guards :after-returns

  ///
  
  (defcong mequiv equal (restrict-values keys map) 2
    :hints (("Goal" :in-theory (disable mequiv))))

  (defrule restrict-values-when-left-emptyp
    (implies (set::emptyp vals)
             (equal (restrict-values vals map) nil))
    :rule-classes (:rewrite :type-prescription)
    :enable set::emptyp)

  (defrule restrict-values-when-right-emptyp
    (implies (emptyp map)
             (equal (restrict-values vals map) nil))
    :rule-classes (:rewrite :type-prescription))

  (defruled assoc-of-restrict-values
    (equal (assoc key (restrict-values vals map))
           (and (set::in (cdr (assoc key map)) vals)
                (assoc key map))))

  (defruled assoc-of-restrict-values-when-in-keys
    (implies (set::in (cdr (assoc key map)) vals)
             (equal (assoc key (restrict-values vals map))
                    (assoc key map)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define inverse ((x mapp))
  :returns (map1 mapp)
  (if (emptyp x)
      nil
      (mv-let (key val)
          (head x)
        (update val key (inverse (tail x)))))
  :verify-guards :after-returns

  ///

  (defcong mequiv equal (inverse x) 1))

(skip-proofs
 (defrule assoc-of-inverse
     (equal (assoc key (inverse x))
            (and (set::in key (values x))
                 (cons key (car (rlookup key x)))))
   :enable values))

(skip-proofs
 (defrule assoc-of-inverse-inverse-when-injectivep
     (implies (injectivep x)
              (equal (assoc key (inverse (inverse x)))
                     (assoc key x)))))

(defrule inverse-inverse
    (implies (injectivep x)
             (equal (inverse (inverse x))
                    x))
  :enable extensionality)

(skip-proofs
 (defrule identityp-compose-inverse
     (implies (injectivep map)
              (identityp (compose map (inverse map))))
   :enable (inverse compose)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define closedp ((x mapp))
  :returns (yes/no booleanp)
  (and (mapp x)
       (or (emptyp x)
           (set::subset (values x) (keys x))))
  ///

  (defrule identityp-implies-closedp
      (implies (identityp map)
               (closedp map))
    :enable identityp-implies-equal-keys-values))
