(in-package "OMAP")

(include-book "core")

(local (include-book "assoc"))
(local (include-book "extensionality"))
(local (include-book "compatiblep"))
(local (include-book "update"))
(local (include-book "delete"))

(include-book "std/osets/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; move to assoc
(defrule in-of-cdr-assoc-when-assoc
    (implies (assoc k x)
             (set::in (cdr (assoc k x))
                      (values x)))
  :enable (assoc values))

; move to core
(defrule cardinality-of-values-<=-cardinality-of-keys
    (<= (cardinality (values x))
        (cardinality (keys x)))
  :enable (keys values set::expensive-rules)
  :rule-classes :linear)

; move to osets
; NOTE: make general, without implies
(defruledl intersect-of-insert-when-in
    (implies (set::in a y)
             (equal (intersect (insert a x) y)
                    (insert a (intersect x y))))
  :enable set::expensive-rules)

; move to core?
(defrule not-head-key-when-assoc-of-tail
    (implies (assoc k (tail x))
             (not (equal k (mv-nth 0 (head x))))))

; move to core with the next theorem
(defruled rlookup-to-in-of-values
    (equal (set::emptyp (rlookup v x))
           (not (set::in v (values x))))
  :enable (rlookup values set::expensive-rules))

(defruled in-of-values-to-rlookup
    (equal (set::in v (values x))
           (not (set::emptyp (rlookup v x))))
  :enable (rlookup values))

(theory-invariant (incompatible (:rewrite rlookup-to-in-of-values)
                                (:rewrite in-of-values-to-rlookup)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compose ((x mapp) (y mapp))
  :returns (map mapp)
  :parents (omaps)
  :short "Compose two omaps as functions."
  :long
  (xdoc::topstring-p
   "Maps key @('k') to @('w') when @('y') maps @('k') to @('v')
    and @('x') maps @('v') to @('w').
    Keys of @('y') with no matching entry in @('x') are dropped.")
  (if (emptyp y)
      nil
      (mv-let (k v) (head y)
        (let ((pair (assoc v x)))
          (if pair
              (update k (cdr pair) (compose x (tail y)))
              (compose x (tail y))))))
  :verify-guards :after-returns

  ///

  (defcong mequiv equal (compose x y) 1)

  (defcong mequiv equal (compose x y) 2)

  (defrule assoc-of-compose
      (equal (assoc k (compose x y))
             (and (assoc k y)
                  (assoc (cdr (assoc k y)) x)
                  (cons k
                        (cdr (assoc (cdr (assoc k y)) x))))))

  (defrule compose-associativity
      (equal (compose (compose x y) z)
             (compose x (compose y z)))
    :enable extensionality))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identityp ((x mapp))
  :returns (yes/no booleanp)
  :parents (omaps)
  :short "Check if an omap is an identity map."
  :long
  (xdoc::topstring-p
   "An omap where every key maps to itself.
    Defined recursively: the empty map is an identity map,
    and a non-empty map is an identity map iff its head key equals its head value
    and its tail is also an identity map.")
  (or (emptyp x)
      (mv-let (k v) (head x)
        (and (equal k v)
             (identityp (tail x)))))
  
  ///

  (defcong mequiv equal (identityp x) 1)

  (defrule values-is-keys-when-identityp
    (implies (identityp x)
             (equal (values x)
                    (keys x)))
  :enable (values keys)
  :rule-classes (:rewrite :forward-chaining))

  (defrule assoc-of-identityp
      (implies (and (identityp x)
                    (assoc k x))
               (equal (assoc k x)
                      (cons k k))))

; NOTE: check this
  (defrulel equal-keys-and-not-assoc-X-implies-not-assoc-Y
      (implies (and (equal (keys x) (keys y))
                    (not (assoc k x)))
               (not (assoc k y)))
    :enable assoc-to-in-of-keys
    :rule-classes :forward-chaining)

  (defruledl equal-assoc-when-identityp-and-equal-keys
      (implies (and (identityp x)
                    (identityp y)
                    (equal (keys x)
                           (keys y)))
               (equal (assoc k x)
                      (assoc k y)))
    :enable assoc-to-in-of-keys
    :cases ((assoc k x)))

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
                    (k (ext-equal-witness x y)))
    :rule-classes :forward-chaining)

  (defruledl compose-is-restrict-when-Y-identityp-helper
      (implies (identityp y)
               (equal (assoc k (compose x y))
                      (assoc k (restrict (keys y) x))))
    :enable (assoc assoc-of-restrict in-of-keys-to-assoc))

  (defruled compose-is-restrict-when-Y-identityp
      (implies (identityp y)
               (equal (compose x y)
                      (restrict (keys y) x)))
    :enable (compose-is-restrict-when-Y-identityp-helper
             extensionality))

  (defrule self-compose-is-self-when-identityp
      (implies (and (identityp x)
                    (mapp x))
               (equal (compose x x) x))
    :enable extensionality))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk identityp-sk ((x mapp))
  (forall (k)
          (implies (assoc k x)
                   (equal (assoc k x)
                          (cons k k))))
  :skolem-name identityp-witness)

(defruledl identityp-sk-of-tail-when-identityp-sk
    (implies (identityp-sk x)
             (identityp-sk (tail x)))
  :expand (identityp-sk (tail x))
  :use (:instance identityp-sk-necc
                  (k (identityp-witness (tail x)))))

(defruled identityp-sk-when-identityp
    (implies (identityp x)
             (identityp-sk x))
  :enable identityp-sk)

(defruled identityp-when-identityp-sk
    (implies (and (identityp-sk x)
                  (mapp x))
             (identityp x))
  :hints ('(:use (:instance identityp-sk-necc
                            (k (mv-nth 0 (head x))))))
  :enable (identityp
           identityp-sk-of-tail-when-identityp-sk))

(defsection pick-a-point-identityp
  :parents (identityp)
  :short "A theory to enable pick-a-point reasoning for @(tsee identityp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Analogous to the @(see pick-a-point) theory for @(tsee submap).
     Rewrites @(tsee identityp) to the skolem-equivalent @(tsee identityp-sk)
     to expose the arbitrary element for point-wise reasoning."))

  (defruled identityp-to-identityp-sk
      (implies (mapp x)
               (equal (identityp x)
                      (identityp-sk x)))
    :use (identityp-sk-when-identityp
          identityp-when-identityp-sk))

  (defthy pick-a-point-identityp
    '(identityp-to-identityp-sk
      identityp-sk)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Copied from Alessandro
(define injectivep ((x mapp))
  :parents (omaps)
  :returns (yes/no booleanp)
  :short "Check if an omap is injective."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, different keys are mapped to different values.
     We express this via a recursion:
     the empty map is injective;
     a non-empty map is injective iff
     the value of its first key is not among the values of the tail of the map,
     and the tail of the map is itself injective.")
   (xdoc::p
    "The @(':exec') version checks injectivity by comparing cardinalities:
     an omap is injective iff it has the same number of distinct keys
     as distinct values.
     This is more efficient for execution than the recursive membership checks
     in the @(':logic') version."))
  (mbe :logic
       (or (emptyp x)
           (b* (((mv & v) (head x)))
             (and (not (set::in v (values (tail x))))
                  (injectivep (tail x)))))
       :exec (equal (cardinality (keys x))
                    (cardinality (values x))))
  :verify-guards nil

  ///

  (defcong mequiv equal (injectivep x) 1)

  (defrule injectivep-implies-injectivep-tail
      (implies (and (injectivep x)
                    (not (emptyp x)))
               (injectivep (tail x)))
    :rule-classes :type-prescription)

  (defrule injectivep-implies-unique-head-value
      (implies (injectivep x)
               (not (set::in (mv-nth 1 (head x))
                             (values (tail x))))))

  (defrule head-val-is-not-assoc-tail-when-injectivep
      (implies (and (injectivep x)
                    (assoc k (tail x)))
               (not (equal (mv-nth 1 (head x))
                           (cdr (assoc k (tail x)))))))

  (defruled equal-val-implies-equal-key-when-injectivep
      (implies (and (injectivep x)
                    (assoc k1 x)
                    (assoc k2 x)
                    (equal (cdr (assoc k1 x))
                           (cdr (assoc k2 x))))
               (equal k1 k2))
    :enable assoc
    :rule-classes :forward-chaining)

  (defrulel injectivep-implies-equal-cardinality-keys-values
      (implies (injectivep x)
               (equal (cardinality (keys x))
                      (cardinality (values x))))
    :enable (keys values set::expensive-rules)
    :rule-classes :forward-chaining)

  (defrulel equal-cardinality-keys-values-implies-injectivep
      (implies (equal (cardinality (keys x))
                      (cardinality (values x)))
               (injectivep x))
    :enable (keys values set::expensive-rules)
    :rule-classes :type-prescription)

  (defruled injectivep-to-cardinality-of-keys-and-values
      (equal (injectivep x)
             (equal (cardinality (keys x))
                    (cardinality (values x)))))

  (defruled cardinality-of-keys-and-values-to-injectivep
      (equal (equal (cardinality (keys x))
                    (cardinality (values x)))
             (injectivep x)))

  (theory-invariant (incompatible (:rewrite injectivep-to-cardinality-of-keys-and-values)
                                  (:rewrite cardinality-of-keys-and-values-to-injectivep)))

  (verify-guards injectivep
      :hints (("Goal" :in-theory
                      (enable cardinality-of-keys-and-values-to-injectivep))))

  (defrule identityp-implies-injectivep
      (implies (identityp x)
               (injectivep x))
    :enable injectivep-to-cardinality-of-keys-and-values
    :use values-is-keys-when-identityp
    :rule-classes :forward-chaining)

  (defrule rlookup-of-cdr-assoc-when-injectivep
      (implies (and (injectivep x)
                    (assoc k x))
               (equal (rlookup (cdr (assoc k x)) x)
                      (insert k nil)))
    :enable (rlookup
             in-of-values-to-rlookup))

  (defruledl cardinality-of-keys-and-values-when-not-in-keys-and-values
      (implies (and (injectivep x)
                    (not (set::in k (keys x)))
                    (not (set::in v (values x))))
               (equal (cardinality (keys (update k v x)))
                      (cardinality (values (update k v x)))))
    :enable (injectivep-to-cardinality-of-keys-and-values
             assoc-to-in-of-keys
             set::expensive-rules))

  (defrule injectivep-of-update-when-not-in-keys-and-values
      (implies (and (injectivep x)
                    (not (set::in k (keys x)))
                    (not (set::in v (values x))))
               (injectivep (update k v x)))
    :use (cardinality-of-keys-and-values-when-not-in-keys-and-values
          (:instance cardinality-of-keys-and-values-to-injectivep
                     (x (update k v x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel compatiblep-implies-equal-restrict-intersect-keys
    (implies (compatiblep x y)
             (equal (restrict (intersect (keys x) (keys y)) x)
                    (restrict (intersect (keys x) (keys y)) y)))
  :enable (assoc-of-restrict extensionality)
  :rule-classes :forward-chaining)

; move to core
(defrule restrict-of-insert
    (equal (restrict (insert k ks) x)
           (if (assoc k x)
               (update k (cdr (assoc k x))
                       (restrict ks x))
             (restrict ks x)))
  :enable restrict)

; move to assoc
(defrule cons-of-key-and-cdr-assoc
  (equal (cons k (cdr (assoc k x)))
         (if (assoc k x)
             (assoc k x)
           (cons k nil)))
  :enable assoc)

(defruledl equal-of-delete-implies-equal-of-assoc-update
  (implies (and (mapp y)
                (assoc k1 y)
                (equal (cdr (assoc k1 y)) v)
                (equal (delete k1 x)
                       (delete k1 y)))
           (equal (assoc k2 (update k1 v x))
                  (assoc k2 y)))
  :use (:instance assoc-of-delete
                   (x k2)
                   (y k1)
                   (map y)))

(defruled equal-of-delete-implies-equal-of-update
  (implies (and (mapp y)
                (assoc k y)
                (equal (cdr (assoc k y)) v)
                (equal (delete k x)
                       (delete k y)))
           (equal (update k v x) y))
  :enable (equal-of-delete-implies-equal-of-assoc-update
           extensionality))

(defrule equal-of-update-is-equal-of-delete
  (equal (equal (update k v x) y)
         (and (mapp y)
              (assoc k y)
              (equal (cdr (assoc k y)) v)
              (equal (delete k x)
                     (delete k y))))
  :use equal-of-delete-implies-equal-of-update)

(defrulel equal-restrict-intersect-keys-implies-compatiblep
    (implies (equal (restrict (intersect (keys x) (keys y)) x)
                    (restrict (intersect (keys x) (keys y)) y))
             (compatiblep x y))
  :enable (restrict
           compatiblep
           set::expensive-rules
           intersect-of-insert-when-in
           assoc-of-restrict
           in-of-keys-to-assoc)
  :rule-classes :forward-chaining)

(defruled compatiblep-is-equal-restrict-intersect-keys
    (equal (compatiblep x y)
           (equal (restrict (intersect (keys x) (keys y)) x)
                  (restrict (intersect (keys x) (keys y)) y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-values ((values set::setp) (x mapp))
  :parents (omaps)
  :returns (map mapp)
  :short "Restrict an omap to entries whose value is in a given set."
  :long
  (xdoc::topstring-p
   "Retains only the key-value pairs of @('x')
    whose associated value belongs to @('values').
    All other pairs are dropped.")
  (cond ((emptyp x) nil)
        (t (mv-let (k v)
               (head x)
             (if (set::in v values)
                 (update k v
                         (restrict-values values (tail x)))
               (restrict-values values (tail x))))))
  :verify-guards :after-returns

  ///

  (defcong mequiv equal (restrict-values keys map) 2
           :hints (("Goal" :in-theory (disable mequiv))))

  (defrule restrict-values-when-left-emptyp
      (implies (set::emptyp vs)
               (not (restrict-values vs x)))
    :enable (restrict-values set::emptyp)
    :rule-classes (:rewrite :type-prescription))

  (defrule restrict-values-when-right-emptyp
      (implies (emptyp x)
               (equal (restrict-values vs x) nil))
    :enable restrict-values
    :rule-classes (:rewrite :type-prescription))

  (defrule assoc-of-restrict-values
      (equal (assoc k (restrict-values vs x))
             (and (set::in (cdr (assoc k x)) vs)
                  (assoc k x)))
    :enable restrict-values)

  (defruled assoc-of-restrict-values-when-in-keys
      (implies (set::in (cdr (assoc k x)) vs)
               (equal (assoc k (restrict-values vs x))
                      (assoc k x)))
    :enable restrict-values)

  (defruledl compose-is-restrict-values-when-X-identityp-helper
      (implies (identityp x)
               (equal (assoc k (compose x y))
                      (assoc k (restrict-values (keys x) y))))
    :enable (assoc assoc-of-restrict in-of-keys-to-assoc))

  (defruled compose-is-restrict-values-when-X-identityp
      (implies (identityp x)
               (equal (compose x y)
                      (restrict-values (keys x) y)))
    :enable (extensionality
             compose-is-restrict-values-when-X-identityp-helper)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define inverse ((x mapp))
  :parents (omaps)
  :returns (map mapp)
  :short "Compute the inverse of an omap."
  :long
  (xdoc::topstring-p
   "Maps each value @('v') of @('x') back to its corresponding key @('k').
    The result is well-behaved when @('x') is injective;
    see @(tsee injectivep).")
  (if (emptyp x)
      nil
    (mv-let (k v)
        (head x)
      (update v k (inverse (tail x)))))
  :verify-guards :after-returns

  ///

  (defcong mequiv equal (inverse x) 1)

  (defrule keys-of-inverse-is-values
      (equal (keys (inverse x))
             (values x))
    :enable values)

  (defrule values-of-inverse-is-keys-when-injectivep
      (implies (injectivep x)
               (equal (values (inverse x))
                      (keys x)))
    :enable assoc-to-in-of-keys)

  (defrule inverse-implies-injectivep
      (implies (injectivep x)
               (injectivep (inverse x)))
    :enable (injectivep
             in-of-keys-to-assoc)
    :rule-classes :type-prescription)

  (defrule not-assoc-of-inverse-when-not-in-values
      (implies (and (injectivep x)
                    (not (set::in v (values x))))
               (not (assoc v (inverse x))))
    :enable assoc-to-in-of-keys)

  (defrulel assoc-of-inverse-when-assoc
      (implies (and (injectivep x)
                    (assoc v x)
                    (equal (cdr (assoc v x)) k))
               (equal (assoc k (inverse x))
                      (cons k v)))
    :enable values
    :use equal-val-implies-equal-key-when-injectivep)

  (defrule injectivep-implies-not-rlookup-head-val-tail
      (implies (injectivep x)
               (set::emptyp (rlookup (mv-nth 1 (head x))
                                     (tail x))))
    :enable rlookup-to-in-of-values)

  (defrule assoc-of-inverse
      (implies (injectivep x)
               (equal (assoc k (inverse x))
                      (and (set::in k (values x))
                           (cons k (set::head (rlookup k x))))))
    :enable (rlookup values set::expensive-rules))

  (defrule rlookup-of-update-when-not-assoc
      (implies (not (assoc k x))
               (equal (rlookup v2 (update k v1 x))
                      (if (equal v2 v1)
                          (insert k (rlookup v2 x))
                        (rlookup v2 x))))
    :enable rlookup
    :expand (rlookup v2 (update k v1 x)))

  (defruledl assoc-of-inverse-inverse
      (implies (injectivep x)
               (equal (assoc k (inverse (inverse x)))
                      (assoc k x)))
    :enable (injectivep
             set::expensive-rules
             rlookup-to-in-of-values
             in-of-keys-to-assoc))

  (defrule inverse-inverse-when-injectivep
      (implies (and (injectivep x)
                    (mapp x))
               (equal (inverse (inverse x)) x))
    :enable (assoc-of-inverse-inverse
             extensionality))

  (defruledl assoc-of-compose-inverse
      (implies (and (injectivep x)
                    (assoc k (compose (inverse x) x)))
               (equal (assoc k (compose (inverse x) x))
                      (cons k k))))

  (defrule identityp-compose-with-inverse
      (implies (injectivep x)
               (identityp (compose (inverse x) x)))
    :enable (assoc-of-compose-inverse
             pick-a-point-identityp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define closedp ((x mapp))
  :returns (yes/no booleanp)
  :short "Check if an omap is closed under its domain."
  :long
  (xdoc::topstring-p
   "An omap is closed if it is empty or
    its set of values is a subset of its set of keys.")
  (or (emptyp x)
      (set::subset (values x) (keys x)))
  ///

  (defcong mequiv equal (closedp x) 1)

  (defrule identityp-implies-closedp
      (implies (identityp x)
               (closedp x))
    :enable values-is-keys-when-identityp
    :rule-classes :forward-chaining))
