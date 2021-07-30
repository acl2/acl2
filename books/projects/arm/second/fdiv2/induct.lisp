;; Cuong Chau <cuong.chau@arm.com>

;; January 2021

;; The goal is to prove rmd(j) = 2^-55 * (si(rs57(j), 57) + si(rc57(j), 57)),
;; and -d <= rmd(j) < d.

(in-package "RTL")

(include-book "first")

(local (arith-5-for-rtl))

;; ======================================================================

(local
 (defthm logxor-bvecp-inst-1
   (bvecp (logxor (* 2 (bits x 55 0))
                  (* 2 (bits y 55 0)))
          57)
   :hints (("Goal"
            :use (:instance logxor-bvecp
                            (x (* 2 (bits x 55 0)))
                            (y (* 2 (bits y 55 0)))
                            (n 57))
            :in-theory (e/d (bvecp) (logxor-bvecp))))))

(local
 (defthm logxor-bvecp-inst-2
   (implies (and (bvecp x 57)
                 (bvecp y 57))
            (bvecp (logxor x y) 57))
   :hints (("Goal" :in-theory (enable bvecp)))))

(defthm bvecp57-rs57&rc57
  (and (bvecp (rs57 i) 57)
       (bvecp (rc57 i) 57))
  :hints (("Goal"
           :induct (induct-on-index i)
           :expand ((rs57 i) (rc57 i))
           :in-theory (enable nextrem rs-0 rc-0)))
  :rule-classes ((:rewrite :corollary (and (bvecp (rs57 i) 57)
                                           (bvecp (rc57 i) 57)))
                 (:type-prescription :corollary (natp (rs57 i)))
                 (:type-prescription :corollary (natp (rc57 i)))
                 (:linear :corollary (and (< (rs57 i) *2^57*)
                                          (< (rc57 i) *2^57*)))))

;; rs57(j)[53 - p : 0] = rc57(j)[53 - p : 0] = 0

(local
 (def-gl-rule bits-rs57&rc57-0-hp
   :hyp (and (equal (bits sum0 42 0) 0)
             (equal (bits car0 42 0) 0)
             (equal (bits d57 44 0) 0)
             (bvecp sum0 57)
             (bvecp car0 57)
             (bvecp d57 56)
             (integerp q)
             (<= -1 q)
             (<= q 1))
   :concl (and (equal (bits (mv-nth 0 (nextrem sum0 car0 d57 q 1))
                            42 0)
                      0)
               (equal (bits (mv-nth 1 (nextrem sum0 car0 d57 q 1))
                            42 0)
                      0))
   :disabledp t
   :g-bindings (gl::auto-bindings
                (:mix (:nat sum0 57)
                      (:nat car0 57)
                      (:seq (:nat d57 56) (:skip 1)))
                (:int q 2))))

(local
 (def-gl-rule bits-rs57&rc57-0-sp
   :hyp (and (equal (bits sum0 29 0) 0)
             (equal (bits car0 29 0) 0)
             (equal (bits d57 31 0) 0)
             (bvecp sum0 57)
             (bvecp car0 57)
             (bvecp d57 56)
             (integerp q)
             (<= -1 q)
             (<= q 1))
   :concl (and (equal (bits (mv-nth 0 (nextrem sum0 car0 d57 q 2))
                            29 0)
                      0)
               (equal (bits (mv-nth 1 (nextrem sum0 car0 d57 q 2))
                            29 0)
                      0))
   :disabledp t
   :g-bindings (gl::auto-bindings
                (:mix (:nat sum0 57)
                      (:nat car0 57)
                      (:seq (:nat d57 56) (:skip 1)))
                (:int q 2))))

(local
 (defthm bits-rs-0&rc-0-inst-hp
   (implies (equal (fmtrem) 1)
            (and (equal (bits (rs-0) 42 0) 0)
                 (equal (bits (rc-0) 42 0) 0)))
   :hints (("Goal"
            :use ((:instance bitn-plus-bits
                             (x (rs-0))
                             (m 0)
                             (n 43))
                  (:instance bitn-plus-bits
                             (x (rc-0))
                             (m 0)
                             (n 43)))
            :in-theory (enable bits-rs-0-0 bits-rc-0-0)))))

(local
 (defthm bits-rs-0&rc-0-inst-sp
   (implies (equal (fmtrem) 2)
            (and (equal (bits (rs-0) 29 0) 0)
                 (equal (bits (rc-0) 29 0) 0)))
   :hints (("Goal"
            :use ((:instance bitn-plus-bits
                             (x (rs-0))
                             (m 0)
                             (n 30))
                  (:instance bitn-plus-bits
                             (x (rc-0))
                             (m 0)
                             (n 30)))
            :in-theory (enable bits-rs-0-0 bits-rc-0-0)))))

(defthmd bits-rs57&rc57-0
  (implies (and (equal n (- 53 (prec (f))))
                (not (equal (fmtrem) 3)))
           (and (equal (bits (rs57 j) n 0) 0)
                (equal (bits (rc57 j) n 0) 0)))
  :hints (("Goal"
           :induct (induct-on-index j)
           :in-theory (enable rs57
                              rc57
                              f
                              fmtrem
                              bits-rs57&rc57-0-hp
                              bits-rs57&rc57-0-sp
                              bits-d57-0))))

(defthmd q-rewrite
  (implies (and (natp i) (< 1 i))
           (equal (q i)
                  (if (< (approx (1- i)) -1)
                      -1
                    (if (equal (approx (1- i)) -1)
                        0
                      1))))
  :hints (("Goal"
           :use (:instance si-bits
                           (x (approx (1- i)))
                           (n 4))
           :in-theory (enable q approx nextdigit si-bounds))))

(defthm bits-fnum-1->0-is-itself
  (equal (bits (fnum) 1 0) (fnum))
  :hints (("Goal" :in-theory (enable bvecp))))

(encapsulate
  ()

  (local
   (def-gl-rule rmd-rewrite-aux-1
     :hyp (and (bvecp sum0 57)
               (bvecp car0 57)
               (bvecp d57 56)
               (integerp q)
               (<= -1 q)
               (<= q 1)
               (posp fmt)
               (<= fmt 3)
               (<= (- d57)
                   (+ (si sum0 57) (si car0 57)))
               (< (+ (si sum0 57) (si car0 57))
                  d57)
               (or (and (equal q 0)
                        (equal (+ (si (bits sum0 56 54) 3)
                                  (si (bits car0 56 54) 3))
                               -1))
                   (and (equal q -1)
                        (< (+ (si (bits sum0 56 54) 3)
                              (si (bits car0 56 54) 3))
                           -1))
                   (and (equal q 1)
                        (> (+ (si (bits sum0 56 54) 3)
                              (si (bits car0 56 54) 3))
                           -1)))
               (or (equal fmt 3)
                   (and (equal fmt 2)
                        (equal (bits sum0 29 0) 0)
                        (equal (bits d57 31 0) 0))
                   (and (equal fmt 1)
                        (equal (bits sum0 42 0) 0)
                        (equal (bits d57 44 0) 0))))
     :concl (equal (+ (si (mv-nth 0 (nextrem sum0 car0 d57 q fmt))
                          57)
                      (si (mv-nth 1 (nextrem sum0 car0 d57 q fmt))
                          57))
                   (- (* 2 (+ (si sum0 57) (si car0 57)))
                      (* q d57)))
     :disabledp t
     :g-bindings (gl::auto-bindings
                  (:mix (:nat sum0 57)
                        (:nat car0 57)
                        (:seq (:nat d57 56) (:skip 1)))
                  (:int q 2)
                  (:nat fmt 2))))

  (local
   (def-gl-rule rmd-bounds-aux-1
     :hyp (and (bvecp sum0 57)
               (bvecp car0 57)
               (bvecp d57 56)
               (<= *2^55* d57)
               (integerp q)
               (<= -1 q)
               (<= q 1)
               (posp fmt)
               (<= fmt 3)
               (<= (- d57)
                   (+ (si sum0 57) (si car0 57)))
               (< (+ (si sum0 57) (si car0 57))
                  d57)
               (or (and (equal q 0)
                        (equal (+ (si (bits sum0 56 54) 3)
                                  (si (bits car0 56 54) 3))
                               -1))
                   (and (equal q -1)
                        (< (+ (si (bits sum0 56 54) 3)
                              (si (bits car0 56 54) 3))
                           -1))
                   (and (equal q 1)
                        (> (+ (si (bits sum0 56 54) 3)
                              (si (bits car0 56 54) 3))
                           -1)))
               (or (equal fmt 3)
                   (and (equal fmt 2)
                        (equal (bits sum0 29 0) 0)
                        (equal (bits d57 31 0) 0))
                   (and (equal fmt 1)
                        (equal (bits sum0 42 0) 0)
                        (equal (bits d57 44 0) 0))))
     :concl (and (<= (- d57)
                     (+ (si (mv-nth 0 (nextrem sum0 car0 d57 q fmt))
                            57)
                        (si (mv-nth 1 (nextrem sum0 car0 d57 q fmt))
                            57)))
                 (< (+ (si (mv-nth 0 (nextrem sum0 car0 d57 q fmt))
                           57)
                       (si (mv-nth 1 (nextrem sum0 car0 d57 q fmt))
                           57))
                    d57))
     :disabledp t
     :g-bindings (gl::auto-bindings
                  (:mix (:nat sum0 57)
                        (:nat car0 57)
                        (:seq (:nat d57 56) (:skip 1)))
                  (:int q 2)
                  (:nat fmt 2))
     :rule-classes :linear))

  (local
   (defthmd rmd-rewrite-aux-2
     (implies (and (not (specialp))
                   (integerp j)
                   (< 1 j)
                   (equal (rmd (1- j))
                          (* (/ *2^55*)
                             (+ (si (rs57 (1- j)) 57) (si (rc57 (1- j)) 57))))
                   (<= (- (d)) (rmd (1- j)))
                   (< (rmd (1- j)) (d)))
              (equal (rmd j)
                     (* (/ *2^55*)
                        (+ (si (rs57 j) 57) (si (rc57 j) 57)))))
     :hints (("Goal"
              :expand ((rs57 j) (rc57 j))
              :use (rmd-recurrence
                    d57-rewrite
                    (:instance rmd-rewrite-aux-1
                               (sum0 (rs57 (1- j)))
                               (car0 (rc57 (1- j)))
                               (d57 (d57))
                               (q (q j))
                               (fmt (fmtrem))))
              :in-theory (e/d (bits-rs57&rc57-0
                               bits-d57-0
                               q-rewrite
                               approx
                               fmtrem
                               f)
                              (acl2::mod-sums-cancel-1
                               acl2::default-times-2
                               bits-tail-gen
                               mod-does-nothing
                               acl2::mod-x-y-=-x-y
                               acl2::|(equal (+ (- c) x) y)|
                               acl2::reduce-multiplicative-constant-equal
                               acl2::mod-x-y-=-x+y
                               acl2::mod-x-y-=-x
                               acl2::mod-zero
                               acl2::mod-positive
                               acl2::mod-negative
                               acl2::not-integerp-1b
                               acl2::not-integerp-2b
                               acl2::not-integerp-3b
                               acl2::not-integerp-4b
                               acl2::default-mod-ratio
                               acl2::default-plus-1
                               acl2::default-plus-2
                               acl2::prefer-positive-addends-equal
                               acl2::prefer-positive-addends-<))))))

  (local
   (defthmd rmd-bounds-aux-2
     (implies (and (not (specialp))
                   (integerp j)
                   (< 1 j)
                   (equal (rmd (1- j))
                          (* (/ *2^55*)
                             (+ (si (rs57 (1- j)) 57) (si (rc57 (1- j)) 57))))
                   (<= (- (d)) (rmd (1- j)))
                   (< (rmd (1- j)) (d)))
              (and (<= (- (d)) (rmd j))
                   (< (rmd j) (d))))
     :hints (("Goal"
              :expand ((rs57 j) (rc57 j))
              :use (rmd-rewrite-aux-2
                    d57-rewrite
                    (:instance rmd-bounds-aux-1
                               (sum0 (rs57 (1- j)))
                               (car0 (rc57 (1- j)))
                               (d57 (d57))
                               (q (q j))
                               (fmt (fmtrem))))
              :in-theory (e/d (bits-rs57&rc57-0
                               bits-d57-0
                               q-rewrite
                               approx
                               fmtrem
                               f)
                              (acl2::mod-sums-cancel-1
                               acl2::default-less-than-2
                               acl2::default-minus
                               acl2::default-times-2
                               bits-tail-gen
                               mod-does-nothing
                               acl2::mod-x-y-=-x-y
                               acl2::|(equal (+ (- c) x) y)|
                               acl2::reduce-multiplicative-constant-equal
                               acl2::mod-x-y-=-x+y
                               acl2::mod-x-y-=-x
                               acl2::mod-zero
                               acl2::mod-positive
                               acl2::mod-negative
                               acl2::not-integerp-1a
                               acl2::not-integerp-2a
                               acl2::not-integerp-3a
                               acl2::not-integerp-4a
                               acl2::not-integerp-1b
                               acl2::not-integerp-2b
                               acl2::not-integerp-3b
                               acl2::not-integerp-4b
                               acl2::default-mod-ratio
                               acl2::default-plus-1
                               acl2::default-plus-2
                               (:type-prescription si)
                               acl2::prefer-positive-addends-equal
                               acl2::prefer-positive-addends-<))))
     :rule-classes :linear))

  (local
   (defundd rmd-bounds-fn (i)
     (and (equal (rmd i)
                 (* (/ *2^55*)
                    (+ (si (rs57 i) 57) (si (rc57 i) 57))))
          (<= (- (d)) (rmd i))
          (< (rmd i) (d)))))

  (local
   (defthm rmd-bounds-fn-1
     (implies (not (specialp))
              (rmd-bounds-fn 1))
     :hints (("Goal"
              :use (rmd1-rewrite rmd1-bounds)
              :in-theory (e/d (rmd-bounds-fn) ())))))

  (local
   (defthm rmd-bounds-fn-inv
     (implies (and (not (specialp))
                   (posp j)
                   (rmd-bounds-fn (1- j)))
              (rmd-bounds-fn j))
     :hints (("Goal"
              :use (rmd-bounds-fn-1 rmd-rewrite-aux-2 rmd-bounds-aux-2)
              :in-theory (e/d (rmd-bounds-fn) (rmd-bounds-fn-1))))))

  (local
   (defthmd rmd-bounds-fn-valid-induct
     (implies (and (not (specialp))
                   (posp j))
              (rmd-bounds-fn j))
     :hints (("Goal" :induct (induct-on-index j)))))

  (defthmd rmd-rewrite
    (implies (and (not (specialp))
                  (posp j))
             (equal (rmd j)
                    (* (/ *2^55*)
                       (+ (si (rs57 j) 57) (si (rc57 j) 57)))))
    :hints (("Goal"
             :use rmd-bounds-fn-valid-induct
             :in-theory (enable rmd-bounds-fn))))

  (defthm rmd-bounds
    (implies (and (not (specialp))
                  (posp j))
             (and (<= (- (d)) (rmd j))
                  (< (rmd j) (d))))
    :hints (("Goal"
             :use rmd-bounds-fn-valid-induct
             :in-theory (enable rmd-bounds-fn)))
    :rule-classes :linear)
  )
