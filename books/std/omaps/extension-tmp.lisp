(include-book "std/omaps/core" :dir :system)

(in-package "OMAP")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compose ((x mapp) (y mapp))
  :returns (map1 mapp)
  (if (or (emptyp x) (emptyp y))
      nil
      (mv-let (k0 v0) (head y)
        (let ((pair (assoc v0 x)))
          (if (endp pair)
              (compose x (tail y))
              (cons (cons k0 (cdr pair))
                    (compose x (tail y))))))))

; Algebraic properties
(defrule compose-associativity
    (implies (and (mapp x) (mapp y) (mapp z))
             (mequiv (compose (compose x y) z)
                     (compose x (compose y z)))))

; Size/cardinality properties
(defrule cardinality-values-compose-1
    (implies (and (mapp x) (mapp y))
             (<= (set::cardinality (values (compose x y)))
                 (set::cardinality (values x)))))

(defrule cardinality-values-compose-2
    (implies (and (mapp x) (mapp y))
             (<= (set::cardinality (values (compose x y)))
                 (set::cardinality (values y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identityp ((x mapp))
  :returns (yes/no booleanp)
  (if (emptyp x)
      t
      (mv-let (k0 v0) (head x)
        (and (equal k0 v0)
             (idmapp (tail x))))))

; Value of key is key
(defrule identityp-value-is-key
    (implies (and (identityp map) (assoc key map))
             (equal (cdr (assoc key map))
                    key)))

; Value set == key set
(defrule identityp-values-is-keys
    (implies (identityp map)
             (equal (values map)
                    (keys map))))

; Uniqueness of key set
(defrule identityp-mequiv-is-equal-keys
    (implies (and (identityp map0) (identityp map1))
             (equal (mequiv map0 map1)
                    (equal (keys map0)
                           (keys map1)))))

; Composition with id map produce restriction
(defrule identityp-compose-restrict
    (implies (and (mapp map) (identityp idmap))
             (mequiv (compose map identityp)
                     (restrict (keys identityp) map)))

; Id map iff map is equal to its self-composition
(defrule identityp-iff-equal-compose
    (iff (identityp map)
         (equal (compose map map)
                map)))

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
  (or (emptyp map)
      (b* (((mv & val) (head map)))
        (and (not (set::in val (values (tail map))))
             (injectivep (tail map))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Compatiblep is mequiv on key set intersection
(defrule compatiblep-mequiv-intersect-keys
    (implies (and (mapp map0) (mapp map1))
             (equal (compatiblep map0 map1)
                    (mequiv (restrict (set::intersect (keys map0) (keys map1))
                                      map0)
                            (restrict (set::intersect (keys map0) (keys map1))
                                      map1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-values ((values set::setp) (map mapp))
  :returns (map1 mapp)
  (cond ((empty p) nil)
        (t (mv-let (key val)
               (head map)
             (if (set::in val values)
                 (cons (head map) (restrict-values values
                                                   (tail map)))
                 (restrict-values values (tail map)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define inverse ((x injectivep))
  :returns (map1 injectivep)
  (if (emptyp x)
      nil
      (mv-let (key val)
          (head map)
        (update val key (inverse (tail map))))))

(defrule inverse-inverse
    (implies (injectivep map)
             (equal (inverse (inverse x))
                    x)))

(defrule identityp-compose-inverse
    (implies (injectivep map)
             (identityp (compose map (inverse map)))))

; Partial inverse
; TODO

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define closedp ((x mapp))
  :returns (yes/no booleanp)
  (if (emptyp x)
      t
      (set::subset (values x) (keys x))))


(defrule identityp-implies-closedp
    (implies (identityp map)
             (closedp map)))



