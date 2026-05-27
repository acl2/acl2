;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OMAP")

(include-book "core")

(local (include-book "assoc"))
(local (include-book "extensionality"))
(local (include-book "update"))
(local (include-book "delete"))
(local (include-book "compatiblep"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule restrict-of-insert
    (equal (restrict (insert k ks) x)
           (if (assoc k x)
               (update k (cdr (assoc k x))
                       (restrict ks x))
             (restrict ks x)))
  :enable (restrict
           not-head-key-when-assoc-of-tail))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; move
(defruledl intersect-of-insert-when-in
    (implies (set::in a y)
             (equal (intersect (insert a x) y)
                    (insert a (intersect x y))))
  :enable set::expensive-rules)

(defrulel compatiblep-implies-equal-restrict-intersect-keys
    (implies (compatiblep x y)
             (equal (restrict (intersect (keys x) (keys y)) x)
                    (restrict (intersect (keys x) (keys y)) y)))
  :enable (assoc-of-restrict extensionality)
  :rule-classes :forward-chaining)

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
