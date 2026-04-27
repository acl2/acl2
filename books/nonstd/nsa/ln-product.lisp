(in-package "ACL2")

(include-book "nonstd/nsa/ln" :dir :system)
(local (include-book "workshops/2018/gamboa-cowles/complex-polynomials" :dir :system))

(defthm ln-product-complex
  (implies (and (acl2-numberp x)
                (acl2-numberp y)
                (not (equal (* x y) 0)))
           (equal (acl2-ln (* x y))
                  (if (< (+ (anglepart x)
                            (anglepart y))
                         (* 2 (acl2-pi)))
                      (+ (acl2-ln x)
                         (acl2-ln y))
                    (- (+ (acl2-ln x)
                          (acl2-ln y))
                       (complex 0 (* 2 (acl2-pi)))))))
  :hints (("Goal"
           :by ln-product)))

(defthm ln-product-real
    (implies (and (realp x)
                  (realp y)
                  (< 0 x)
                  (< 0 y))
           (equal (acl2-ln (* x y))
                  (+ (acl2-ln x)
                     (acl2-ln y))))
  :hints (("Goal"
           :use ((:instance ln-product)))))
