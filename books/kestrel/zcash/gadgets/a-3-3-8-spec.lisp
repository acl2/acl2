; Specification of the gadget in [ZPS:A.3.3.8].

(in-package "ZCASH")

(include-book "a-3-3-1-spec")

(include-book "kestrel/prime-fields/fe-listp" :dir :system)

(define variable-edwards-mul-precond (u v ks)
  :guard (and (fep u (jubjub-q))
              (fep v (jubjub-q))
              (fe-listp ks (jubjub-q)))
  (and (affine-edwards-spec u v)
       (bit-listp ks)))

(define variable-edwards-mul-spec (u v ks u3 v3)
  :guard (and (fep u (jubjub-q))
              (fep v (jubjub-q))
              (fe-listp ks (jubjub-q))
              (fep u3 (jubjub-q))
              (fep v3 (jubjub-q))
              (variable-edwards-mul-precond u v ks))
  (equal (ecurve::twisted-edwards-mul (acl2::lebits=>nat ks)
                                      (ecurve::point-finite u v)
                                      (jubjub-curve))
         (ecurve::point-finite u3 v3))
  :guard-hints (("Goal" :in-theory (enable variable-edwards-mul-precond
                                           affine-edwards-spec
                                           point-on-jubjub-p))))
