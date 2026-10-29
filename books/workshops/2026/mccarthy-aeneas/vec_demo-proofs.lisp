; Properties of the extracted Vec demo (unmodified compiler output).
(in-package "ACL2")
(include-book "vec_demo")
(include-book "arithmetic/top-with-meta" :dir :system)

;; build_pair produces the 2-element vector [a, b].
(defthm build-pair-correct
  (equal (vec-demo-build-pair a b) (ok (list a b))))

;; len_of counts elements; on a built pair it is 2.
(defthm len-of-build-pair
  (equal (b* (((ok v) (vec-demo-build-pair a b))) (vec-demo-len-of v))
         (ok 2)))

;; get0 reads the first element.
(defthm get0-of-build-pair
  (equal (b* (((ok v) (vec-demo-build-pair a b))) (vec-demo-get0 v))
         (ok a)))
