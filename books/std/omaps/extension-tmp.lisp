(in-package "OMAP")

(include-book "core")
(include-book "assoc")
(include-book "extensionality")
(include-book "compatiblep")
(include-book "submap")
(include-book "update")
(include-book "delete")

(include-book "std/osets/cardinality" :dir :system)
(include-book "std/osets/intersect" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; move to core
(defrule assoc-implies-in-keys
    (implies (assoc k x)
             (set::in k (keys x)))
  :enable assoc
  :rule-classes :forward-chaining)

; move to core
(defrule not-assoc-implies-not-in-keys
    (implies (not (assoc k x))
             (not (set::in k (keys x))))
  :enable assoc
  :rule-classes :forward-chaining)

; consider editing values-of-update-when-not-assoc
(defrule values-of-update-when-not-in
; Similar to values-of-update-when-not-assoc in "core"
    (implies (not (set::in k (keys x)))
             (equal (values (update k v x))
                    (set::insert v (values x)))))

(defrule assoc-implies-cdr-assoc-in-values
; Similar to in-values-when-assoc in "core"
    (implies (assoc k x)
             (set::in (cdr (assoc k x))
                      (values x)))
  :enable (assoc values)
  :rule-classes :forward-chaining)

(defrule not-empty-implies-in-car
    (implies (not (set::emptyp x))
             (set::in (car x) x))
  :enable (set::emptyp set::in set::head)
  :rule-classes :forward-chaining)

; move to core
(defrule cardinality-values-<=-keys
    (<= (set::cardinality (values x))
        (set::cardinality (keys x)))
  :enable (keys values set::insert-cardinality)
  :rule-classes :linear)

(defrule intersect-insert-when-in
    (implies (set::in a y)
             (equal (set::intersect (set::insert a x) y)
                    (set::insert a (set::intersect x y))))
  :enable set::expensive-rules)

(defrule not-in-intersect-when-not-in
    (implies (not (set::in a x))
             (not (set::in a (set::intersect x y)))))

(defrule in-keys-tail-implies-not-head-key
    (implies (set::in k (keys (tail x)))
             (not (equal k (mv-nth 0 (head x)))))
  :rule-classes :forward-chaining)

(defrule head-key-not-in-keys-tail
    (implies (not (emptyp x))
             (not (set::in (mv-nth 0 (head x))
                           (keys (tail x))))))

(defrule rlookup-nil-when-not-in-values
    (implies (not (set::in v (values x)))
             (not (rlookup v x)))
  :enable (rlookup values))

(defrule in-values-implies-rlookup
    (implies (set::in v (values x))
             (rlookup v x))
  :enable (values rlookup)
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compose ((x mapp) (y mapp))
  :returns (map mapp)
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

  (defcong mequiv equal (compose x y) 2))

(defrule assoc-of-compose
    (equal (assoc key (compose x y))
           (and (assoc key y)
                (assoc (cdr (assoc key y)) x)
                (cons key
                      (cdr (assoc (cdr (assoc key y)) x)))))
  :enable compose)

(defruledl assoc-of-compose-associativity
    (equal (assoc key (compose (compose x y) z))
           (assoc key (compose x (compose y z)))))

(defrule compose-associativity
    (equal (compose (compose x y) z)
           (compose x (compose y z)))
  :enable (assoc-of-compose-associativity
           extensionality))

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


; remove mapp
(define identityp ((x mapp))
  :returns (yes/no booleanp)
  (or (emptyp x)
      (mv-let (key val) (head x)
        (and (equal key val)
             (identityp (tail x)))))
  
  ///

  (defcong mequiv equal (identityp x) 1))

(defruled values-is-keys-when-identityp
    (implies (identityp x)
             (equal (values x)
                    (keys x)))
  :enable (identityp values keys)
  :rule-classes (:rewrite :forward-chaining))

(defrule assoc-of-identityp
    (implies (and (identityp x)
                  (assoc key x))
             (equal (assoc key x)
                    (cons key key)))
  :enable identityp)

(defrule equal-keys-and-not-assoc-X-implies-not-assoc-Y
    (implies (and (equal (keys x) (keys y))
                  (not (assoc key x)))
             (not (assoc key y)))
  :enable assoc-to-in-of-keys
  :rule-classes :forward-chaining) 

(defruled equal-assoc-when-identityp-and-equal-keys
    (implies (and (identityp x)
                  (identityp y)
                  (equal (keys x)
                         (keys y)))
             (equal (assoc key x)
                    (assoc key y)))
  :enable (assoc-to-in-of-keys)
  :cases ((assoc key x)))

(defruled equal-when-identityp-and-equal-keys
    (implies (and (identityp x)
                  (identityp y)
                  (mapp x)
                  (mapp y)
                  (equal (keys x)
                         (keys y)))
             (equal x y))
  :enable extensionality
  :use (:instance equal-assoc-when-identityp-and-equal-keys
                  (key (ext-equal-witness x y)))
  :rule-classes :forward-chaining)

(defruledl assoc-of-compose-is-restrict-when-args2-identityp
    (implies (identityp id-y)
             (equal (assoc key (compose x id-y))
                    (assoc key (restrict (keys id-y) x))))
  :enable (assoc-of-restrict assoc))

(defruled compose-is-restrict-when-args2-identityp
    (implies (identityp id-y)
             (equal (compose x id-y)
                    (restrict (keys id-y) x)))
  :enable (assoc-of-compose-is-restrict-when-args2-identityp
           extensionality))

(defruledl assoc-of-self-compose-is-self-when-identityp
    (implies (identityp x)
             (equal (assoc key (compose x x))
                    (assoc key x))))

(defrule self-compose-is-self-when-identityp
    (implies (and (identityp x)
                  (mapp x))
             (equal (compose x x)
                    x))
  :enable (extensionality
           assoc-of-self-compose-is-self-when-identityp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk identityp-sk ((x mapp))
  (forall (key)
          (implies (assoc key x)
                   (equal (assoc key x)
                          (cons key key))))
  :skolem-name identityp-witness)

(defruledl identityp-sk-of-tail-when-identityp-sk
    (implies (identityp-sk x)
             (identityp-sk (tail x)))
  :expand (identityp-sk (tail x))
  :use (:instance identityp-sk-necc
                  (key (identityp-witness (tail x)))))

(defruled identityp-sk-when-identityp
    (implies (identityp x)
             (identityp-sk x))
  :enable identityp-sk)

(defruled identityp-when-identityp-sk
    (implies (and (identityp-sk x)
                  (mapp x))
             (identityp x))
  :hints ('(:use (:instance identityp-sk-necc
                            (key (mv-nth 0 (head x))))))
  :enable (identityp
           identityp-sk-of-tail-when-identityp-sk))

(defruled identityp-to-identityp-sk
    (implies (mapp x)
             (equal (identityp x)
                    (identityp-sk x)))
  :use (identityp-sk-when-identityp
        identityp-when-identityp-sk))

(defthy pick-a-point-identityp
    '(identityp-to-identityp-sk
      identityp-sk))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Copied from Alessandro
(define injectivep ((x mapp))
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
  (mbe :logic
       (or (emptyp x)
           (b* (((mv & val) (head x)))
             (and (not (set::in val (values (tail x))))
                  (injectivep (tail x)))))
       :exec (equal (set::cardinality (keys x))
                    (set::cardinality (values x))))
  :verify-guards nil

  ///

  (defcong mequiv equal (injectivep x) 1))

(defrule injectivep-implies-injectivep-tail
    (implies (and (injectivep x)
                  (not (emptyp x)))
             (injectivep (tail x)))
  :enable injectivep
  :rule-classes :forward-chaining)

(defrule injectivep-implies-unique-head-value
    (implies (injectivep x)
             (not (set::in (mv-nth 1 (head x))
                           (values (tail x)))))
  :enable injectivep
  :rule-classes :forward-chaining)

(defrule head-val-is-not-assoc-tail-when-injectivep
    (implies (and (injectivep x)
                  (assoc k (tail x)))
             (not (equal (mv-nth 1 (head x))
                         (cdr (assoc k (tail x))))))
  :enable injectivep)

(defrule equal-val-implies-equal-key-when-injectivep
    (implies (and (injectivep x)
                  (assoc k1 x)
                  (assoc k2 x)
                  (equal (cdr (assoc k1 x))
                         (cdr (assoc k2 x))))
             (equal k1 k2))
  :enable (injectivep assoc)
  :rule-classes :forward-chaining)

(defrule injectivep-implies-equal-cardinality-keys-values
    (implies (injectivep x)
             (equal (set::cardinality (keys x))
                    (set::cardinality (values x))))
  :enable (injectivep keys values set::insert-cardinality)
  :rule-classes :forward-chaining)

(defrule equal-cardinality-keys-values-implies-injectivep
    (implies (equal (set::cardinality (keys x))
                    (set::cardinality (values x)))
             (injectivep x))
  :enable (injectivep keys values set::insert-cardinality)
  :rule-classes :forward-chaining)

(defruled injectivep-is-equal-cardinality-keys-values
    (equal (injectivep x)
           (equal (set::cardinality (keys x))
                  (set::cardinality (values x)))))

(defruled cardinality-keys-values-is-equal-injectivep
    (equal (equal (set::cardinality (keys x))
                  (set::cardinality (values x)))
           (injectivep x)))

(verify-guards injectivep
    :hints (("goal" 
             :in-theory 
             (enable injectivep
                     cardinality-keys-values-is-equal-injectivep))))

(defruled identityp-implies-equal-cardinality-keys-values
    (implies (identityp x)
             (equal (set::cardinality (keys x))
                    (set::cardinality (values x))))
  :enable values-is-keys-when-identityp
  :rule-classes :forward-chaining)

(defrule identityp-implies-injectivep
    (implies (identityp x)
             (injectivep x))
  :enable injectivep-is-equal-cardinality-keys-values
  :use values-is-keys-when-identityp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule compatiblep-implies-equal-assoc-restrict-intersect-keys
    (implies (compatiblep map0 map1)
             (equal (assoc k (restrict (set::intersect (keys map0) (keys map1))
                                       map0))
                    (assoc k (restrict (set::intersect (keys map0) (keys map1))
                                       map1))))
  :enable assoc-of-restrict)

(defrule compatiblep-implies-equal-restrict-intersect-keys
    (implies (compatiblep map0 map1)
             (equal (restrict (set::intersect (keys map0) (keys map1)) map0)
                    (restrict (set::intersect (keys map0) (keys map1)) map1)))
  :enable extensionality
  :rule-classes :forward-chaining)

(defrule restrict-of-insert
    (equal (restrict (set::insert k ks) x)
           (if (assoc k x)
               (update k (cdr (assoc k x))
                       (restrict ks x))
             (restrict ks x)))
  :enable restrict)

(defrule equal-update-not-in-keys-and-not-equal-K-implies-equal-assoc
    (implies (and (equal (update k v x)
                         (update k v y))
                  (not (set::in k (keys x)))
                  (not (set::in k (keys y)))
                  (not (equal key k)))
             (equal (assoc key x)
                    (assoc key y)))
  :use ((:instance assoc-of-update
                   (key1 key) (key k) 
                   (val v) (map y)))
  :rule-classes :forward-chaining)

(defrule equal-update-not-in-keys-and-equal-K-implies-equal-assoc
    (implies (and (equal (update k v x)
                         (update k v y))
                  (not (set::in k (keys x)))
                  (not (set::in k (keys y)))
                  (equal key k))
             (equal (assoc key x)
                    (assoc key y)))
  :rule-classes :forward-chaining)

(defruled equal-update-not-in-keys-implies-equal-assoc
    (implies (and (equal (update k v x)
                         (update k v y))
                  (not (set::in k (keys x)))
                  (not (set::in k (keys y))))
             (equal (assoc key x)
                    (assoc key y)))
  :use equal-update-not-in-keys-and-equal-K-implies-equal-assoc)

(defrule equal-update-not-in-keys-implies-equal
    (implies (and (mapp x)
                  (mapp y)
                  (equal (update k v x)
                         (update k v y))
                  (not (set::in k (keys x)))
                  (not (set::in k (keys y))))
             (equal x y))
  :enable extensionality
  :use (:instance equal-update-not-in-keys-implies-equal-assoc
                  (key (ext-equal-witness x y)))
  :rule-classes :forward-chaining)

(defrule equal-update-restrict-implies-equal-restrict
    (implies (and (equal (update k v (restrict ks x))
                         (update k v (restrict ks y)))
                  (not (set::in k ks)))
             (equal (restrict ks x)
                    (restrict ks y)))
  :use (:instance equal-update-not-in-keys-implies-equal
                  (x (restrict ks x)) (y (restrict ks y)))
  :rule-classes :forward-chaining)

(defrule equal-update-K-implies-equal-assoc-update-K
    (implies (equal (update k v1 x)
                    (update k v2 y))
             (equal (assoc k (update k v1 x))
                    (assoc k (update k v2 y))))
  :rule-classes :forward-chaining)

(defrule equal-update-implies-equal-val
    (implies (equal (update k v1 x)
                    (update k v2 y))
             (equal v1 v2))
  :use ((:instance assoc-of-update
                   (key1 k) (key k)
                   (val v1) (map x))
        (:instance assoc-of-update
                   (key1 k) (key k)
                   (val v2) (map y)))
  :rule-classes :forward-chaining)

(defrule not-equal-update-when-not-equal-val
    (implies (not (equal v1 v2))
             (not (equal (update k v1 x)
                         (update k v2 y)))))

(defruled lemma0
  (implies (equal (update key val x)
                  y)
           (and (mapp y)
                (assoc key y)
                (equal (cdr (assoc key y)) val)
                (equal (delete key x)
                       (delete key y))))
  :use ((:instance extensionality
                   (x (delete key x))
                   (y (delete key y)))))

(defrule cons-of-key-and-cdr-assoc
  (equal (cons key (cdr (assoc key map)))
         (if (assoc key map)
             (assoc key map)
           (cons key nil)))
  :induct t
  :enable assoc)

(defruled lemma1
  (implies (and (mapp y)
                (assoc key1 y)
                (equal (cdr (assoc key1 y)) val)
                (equal (delete key1 x)
                       (delete key1 y)))
           (equal (assoc key2 (update key1 val x))
                  (assoc key2 y)))
  :use ((:instance assoc-of-delete
                   (x key2)
                   (y key1)
                   (map x))
        (:instance assoc-of-delete
                   (x key2)
                   (y key1)
                   (map y)))
  :disable assoc-of-delete)

(defruled lemma2
  (implies (and (mapp y)
                (assoc key y)
                (equal (cdr (assoc key y)) val)
                (equal (delete key x)
                       (delete key y)))
           (equal (update key val x) y))
  :enable lemma1
  :use ((:instance extensionality
                   (x (update key val x)))))

(defrule equal-of-update-becomes-equal-of-delete
  (equal (equal (update key val x) y)
         (and (mapp y)
              (assoc key y)
              (equal (cdr (assoc key y)) val)
              (equal (delete key x)
                     (delete key y))))
  :use (lemma1 lemma2))

(defrule equal-restrict-intersect-keys-implies-compatiblep
    (implies (equal (restrict (set::intersect (keys x) (keys y)) x)
                    (restrict (set::intersect (keys x) (keys y)) y))
             (compatiblep x y))
  :enable (restrict
           compatiblep
           set::intersect-insert-X
           assoc-of-restrict)
  :rule-classes :forward-chaining)

(defruled compatiblep-is-equal-restrict-intersect-keys
    (equal (compatiblep x y)
           (equal (restrict (set::intersect (keys x) (keys y)) x)
                  (restrict (set::intersect (keys x) (keys y)) y))))

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
           :hints (("Goal" :in-theory (disable mequiv)))))

(defrule restrict-values-when-left-emptyp
    (implies (set::emptyp vals)
             (not (restrict-values vals map)))
  :enable (restrict-values set::emptyp)
  :rule-classes (:rewrite :type-prescription))

(defrule restrict-values-when-right-emptyp
    (implies (emptyp map)
             (equal (restrict-values vals map) nil))
  :enable restrict-values
  :rule-classes (:rewrite :type-prescription))

(defruled assoc-of-restrict-values
    (equal (assoc key (restrict-values vals map))
           (and (set::in (cdr (assoc key map)) vals)
                (assoc key map)))
  :enable restrict-values)

(defruled assoc-of-restrict-values-when-in-keys
    (implies (set::in (cdr (assoc key map)) vals)
             (equal (assoc key (restrict-values vals map))
                    (assoc key map)))
  :enable restrict-values)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define inverse ((x mapp))
  :returns (map mapp)
  (if (emptyp x)
      nil
      (mv-let (key val)
          (head x)
        (update val key (inverse (tail x)))))
  :verify-guards :after-returns

  ///

  (defcong mequiv equal (inverse x) 1))

(defrule keys-of-inverse-is-values
    (equal (keys (inverse x))
           (values x))
  :enable (inverse values))

(defrule values-of-inverse-is-subset-keys
    (set::subset (values (inverse x))
                 (keys x))
  :enable inverse)

(defrule values-of-inverse-is-keys
    (implies (injectivep x)
             (equal (values (inverse x))
                    (keys x)))
  :enable inverse)

(defrule injectivep-implies-injectivep-update
    (implies (and (injectivep x)
                  (not (set::in k (keys x)))
                  (not (set::in v (values x))))
             (injectivep (update k v x)))
  :enable (injectivep values))

(defrule inverse-implies-injectivep
    (injectivep (inverse x))
  :enable (injectivep inverse)
  :rule-classes :type-prescription)

(defrule assoc-of-inverse-nil-when-not-in-values
    (implies (and (injectivep x)
                  (not (set::in val (values x))))
             (not (assoc val (inverse x))))
  :enable assoc-to-in-of-keys)

(defrule assoc-of-inverse-when-assoc
    (implies (and (injectivep x)
                  (assoc val x)
                  (equal (cdr (assoc val x)) key))
             (equal (assoc key (inverse x))
                    (cons key val)))
  :enable (inverse values)
  :use equal-val-implies-equal-key-when-injectivep)

(defrule injectivep-implies-rlookup-first-val-tail-nil
    (implies (injectivep x)
             (not (rlookup (mv-nth 1 (head x))
                           (tail x))))
  :enable (injectivep rlookup)
  :rule-classes :forward-chaining)

(defrule assoc-of-inverse
    (implies (injectivep x)
             (equal (assoc key (inverse x))
                    (and (set::in key (values x))
                         (cons key (car (rlookup key x)))))) ; switch car to set::head
  :enable (inverse rlookup values set::insert))

(defrule rlookup-update-when-not-in-keys
    (implies (not (set::in k (keys x)))
             (equal (rlookup val (update k v x))
                    (if (equal val v)
                        (set::insert k (rlookup val x))
                      (rlookup val x))))
  :enable rlookup
  :expand (rlookup val (update k v x)))

(defrule assoc-of-inverse-inverse
    (implies (injectivep x)
             (equal (assoc key (inverse (inverse x)))
                    (assoc key x)))
  :enable (injectivep inverse set::insert))

(defrule inverse-inverse
    (implies (injectivep x)
             (equal (inverse (inverse x))
                    x))
  :enable extensionality)

(defrule identityp-compose-with-inverse-prop
    (implies (and (injectivep map)
                  (assoc key (compose map (inverse map))))
             (equal (assoc key (compose map (inverse map)))
                    (cons key key)))
  :enable set::emptyp
  :use ((:instance set-in-of-rlookup
                   (key (car (rlookup key map)))
                   (val key))
        (:instance not-empty-implies-in-car
                   (x (rlookup key map)))))

(defrule identityp-compose-with-inverse
    (implies (injectivep map)
             (identityp (compose map (inverse map))))
  :enable pick-a-point-identityp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define closedp ((x mapp))
  :returns (yes/no booleanp)
  (and (mapp x)
       (or (emptyp x)
           (set::subset (values x) (keys x))))
  ///)

(defrule identityp-implies-closedp
    (implies (identityp map)
             (closedp map))
  :enable (closedp identityp-implies-equal-keys-values))
