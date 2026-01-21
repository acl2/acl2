(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))

(include-book "nonstd/nsa/trig" :dir :system)

(local
 (encapsulate
     ( ((wallis *) => * ) )

     (local
      (defun wallis (n) (declare (ignore n)) 0))

   (skip-proofs
    (defthm wallis-of-0
        (equal (wallis 0) (acl2-pi))))

   (skip-proofs
    (defthm wallis-of-1
        (equal (wallis 1) 2)))

   (skip-proofs
    (defthm wallis-recurrence
        (implies (and (integerp n)
                      (<= 2 n))
                 (equal (wallis n)
                        (/ (* (- n 1)
                              (wallis (- n 2)))
                           n)))))

   (skip-proofs
    (defthm wallis-decreasing
        (implies (natp n)
                 (<= (wallis (+ n 1))
                     (wallis n)))))

   (skip-proofs
    (defthm wallis-number
        (implies (natp n)
                 (realp (wallis n)))
      :rule-classes (:type-prescription :rewrite)))

   )
 )

(local
 (defun wallis-expansion (n)
   (if (zp n)
       (acl2-pi)
       (if (equal n 1)
           2
           (* (/ (- n 1) n)
              (wallis-expansion (- n 2)))))))

(local
 (defun wallis-factor (n)
   (if (and (integerp n)
            (<= 2 n))
       (* (/ (- n 1) n)
          (wallis-factor (- n 2)))
       1)))

(local
 (defun wallis-factor-list (n)
   (if (and (integerp n)
            (<= 2 n))
       (cons (/ (- n 1) n)
             (wallis-factor-list (- n 2)))
       nil)))
(local
 (defthm wallis-expansion-for-evens
     (implies (and (natp n)
                   (evenp n))
              (equal (wallis-expansion n)
                     (* (acl2-pi)
                        (wallis-factor n))))))

(local
 (defthm wallis-expansion-for-odds
     (implies (and (natp n)
                   (not (evenp n)))
              (equal (wallis-expansion n)
                     (* 2
                        (wallis-factor n))))))

(encapsulate
    nil

    (local
     (defthm lemma-1
         (implies (and (natp n)
                       (evenp n)
                       (< n 2))
                  (equal n 0))
       :rule-classes nil))

  (defthmd wallis-as-wallis-expansion-for-evens
      (implies (and (natp n)
                    (evenp n))
               (equal (wallis n) (wallis-expansion n)))
    :hints (("Goal"
             :use ((:instance lemma-1))
             :in-theory (disable (wallis-expansion))))

    )
  )

(Encapsulate
    nil

    (local
     (defthm lemma-1
         (implies (and (natp n)
                       (not (evenp n))
                       (< n 2))
                  (equal n 1))
       :rule-classes nil))

  (defthmd wallis-as-wallis-expansion-for-odds
      (implies (and (natp n)
                    (not (evenp n)))
               (equal (wallis n) (wallis-expansion n)))
    :hints (("Goal"
             :use ((:instance lemma-1))
             :in-theory (disable (wallis-expansion))))

    )
  )

(local
 (defthm wallis-expansion-positive
     (< 0 (wallis-expansion n))))

(local
 (defthm wallis-positive
     (implies (natp n)
              (< 0 (wallis n)))
   :hints (("Goal"
            :use ((:instance wallis-expansion-positive)
                  (:instance wallis-as-wallis-expansion-for-evens)
                  (:instance wallisg-as-wallis-expansion-for-odds)
                  )
            :in-theory (disable wallis-expansion-positive
                                (:type-prescription wallis-expansion))))
   :rule-classes (:type-prescription :rewrite)))

(local
 (defthmd wallis-quotient-simplifier
     (implies (and (natp n)
                   (not (evenp n))
                   (<= 2 n))
              (equal (/ (wallis n) (wallis (1- n)))
                     (* (/ 2 (acl2-pi))
                        (/ (wallis-factor n)
                           (wallis-factor (1- n))))))

   :hints (("Goal"
            :do-not-induct t
            :IN-THEORY (e/d (WALLIS-AS-WALLIS-EXPANSION-FOR-ODDS
                             WALLIS-AS-WALLIS-EXPANSION-FOR-EVENS
                             WALLIS-EXPANSION-FOR-EVENS
                             WALLIS-EXPANSION-FOR-ODDS
                             )
                            (WALLIS-RECURRENCE
                             WALLIS-NUMBER
                             ))
            )
           )
   :OTF-FLG T
   ))

(local
 (defthmd wallis-triple-bounds
     (implies (and (natp n)
                   (<= 2 n))
              (and (<= (wallis (1+ n))
                       (wallis n))
                   (<= (wallis n)
                       (wallis (1- n)))))
   :hints (("Goal"
            :use ((:instance wallis-decreasing)
                  (:instance wallis-decreasing (n (1- n))))
            :in-theory (disable wallis-decreasing)))
   ))


(local
 (defthmd wallis-squeeze-bounds-part1
     (implies (and (natp n)
                   (<= 2 n))
              (<= 1
                  (/ (wallis n) (wallis (1+ n)))))
   :hints (("Goal"
            :use ((:instance wallis-triple-bounds)
                  (:instance
                   (:theorem (implies (and (realp x)
                                           (realp y)
                                           (< 0 y)
                                           (<= y x))
                                      (<= 1 (/ x y))))
                   (x (wallis n))
                   (y (wallis (1+ n))))
                  )
            :in-theory (disable wallis-triple-bounds
                                WALLIS-RECURRENCE))
           )
   :otf-flg t
   ))


(local
 (defthmd wallis-squeeze-bounds-part2a
     (implies (and (natp n)
                   (<= 2 n))
              (<= (/ (wallis n) (wallis (1+ n)))
                  (/ (wallis (1- n)) (wallis (1+ n)))))
   :hints (("Goal"
            :use ((:instance wallis-triple-bounds)
                  (:instance
                   (:theorem (implies (and (realp x)
                                           (realp y)
                                           (realp z)
                                           (< 0 z)
                                           (<= x y))
                                      (<= (/ x z) (/ y z))))
                   (x (wallis n))
                   (y (wallis (1- n)))
                   (z (wallis (1+ n)))
                   )
                  )
            :in-theory (disable wallis-triple-bounds
                                wallis-recurrence))
           )
   :otf-flg t
   ))

(local
 (defthmd wallis-squeeze-bounds-part2b
     (implies (and (natp n)
                   (<= 2 n))
              (equal (/ (wallis (1- n)) (wallis (1+ n)))
                     (/ (1+ n) n)
                     ))
   :hints (("Goal"
            :use ((:instance wallis-recurrence
                             (n (1+ n)))
                  )
            :in-theory (disable wallis-recurrence))
           )
   :otf-flg t
   ))

(local
 (defthmd wallis-squeeze-bounds-part2
     (implies (and (natp n)
                   (<= 2 n))
              (<= (/ (wallis n) (wallis (1+ n)))
                  (/ (1+ n) n)))
   :hints (("Goal"
            :use ((:instance wallis-squeeze-bounds-part2a)
                  (:instance wallis-squeeze-bounds-part2b)
                  )
           ))
   :otf-flg t
   ))

(local
 (defthmd wallis-squeeze-bounds
     (implies (and (natp n)
                   (<= 2 n))
              (and (<= 1 (/ (wallis n) (wallis (1+ n))))
                   (<= (/ (wallis n) (wallis (1+ n)))
                       (/ (1+ n) n))))
   :hints (("Goal"
            :use ((:instance wallis-squeeze-bounds-part1)
                  (:instance wallis-squeeze-bounds-part2)
                  )
           ))
   :otf-flg t
   ))

(local
 (defthmd wallis-squeeze-bounds
     (implies (and (natp n)
                   (<= 2 n))
              (and (<= 1 (/ (wallis n) (wallis (1+ n))))
                   (<= (/ (wallis n) (wallis (1+ n)))
                       (/ (1+ n) n))))
   :hints (("Goal"
            :use ((:instance wallis-squeeze-bounds-part1)
                  (:instance wallis-squeeze-bounds-part2)
                  )
           ))
   :otf-flg t
   ))

(local
 (defthmd not-large-0
     (not (i-large 0))
   :hints (("Goal"
            :in-theory (enable i-large)))))

(local
 (defthmd large-then-not-0
     (implies (i-large n)
              (not (equal n 0)))
   :hints (("Goal"
            :in-theory (enable i-large)))))



(local
 (defthm large->=-2
     (implies (and (natp n)
                   (i-large n))
              (<= 2 n))
   :hints (("Goal"
            :use ((:instance large-if->-large
                             (x n)
                             (y 2)))))))1


(local
 (encapsulate
     nil

     (local
      (defthm lemma-1
          (implies (and (integerp n)
                        (<= 0 n)
                        (i-large n))
                   (not (< n 2)))
        :hints (("Goal"
                 :use ((:instance large-if->-large
                                  (x n)
                                  (y 2)))
                 :in-theory (disable large-if->-large)))))

   (local
    (defthm lemma-2
        (implies (i-small eps)
                 (equal (standard-part (+ 1 eps)) 1))
      :hints (("Goal"
               :use ((:instance close-x-y->same-standard-part
                                (x 1)
                                (y (+ 1 eps)))
                     (:instance i-close-to-small-sum
                                (x 1)))
               :in-theory (disable close-x-y->same-standard-part
                                   i-close-to-small-sum)))))


   (defthmd wallis-quotient-asymptotic
        (implies (and (natp n)
                     (i-large n))
                (equal (standard-part (/ (wallis n) (wallis (1+ n)))) 1))
     :hints (("Goal"
              :use ((:instance wallis-squeeze-bounds)
                    (:instance standard-part-squeeze
                               (x 1)
                               (y (/ (wallis n) (wallis (1+ n))))
                               (z (/ (1+ n) n)))
                    (:instance i-large-udivide (x n))
                    )
              :in-theory (disable i-large-udivide
                                  STANDARD-PART-OF-PLUS
                                  WALLIS-RECURRENCE
                                  )
              ))
     :otf-flg t
     )

   (local
    (defthm lemma-3
        (implies (and (natp n)
                      (<= 1 n))
                 (not (i-large (/ (wallis n) (wallis (1- n))))))
      :hints (("Goal"
               :use ((:instance wallis-decreasing (n (1- n)))
                     (:instance large-if->-large
                                (x (/ (wallis n) (wallis (1- n))))
                                (y 1))
                     )
               :in-theory (disable wallis-decreasing
                                   WALLIS-RECURRENCE)))))

   (local
    (defthm lemma-4
        (implies (and (natp n)
                      (<= 1 n))
                 (not (i-large (/ (- n 1) n))))
      :hints (("Goal"
               :use ((:instance large-if->-large
                                (x (/ (- n 1) n))
                                (y 1))
                     )
               :in-theory (disable large-if->-large)))))

   (local
    (defthmd lemma-5
        (implies (and (natp n)
                      (<= 1 n))
                 (equal (/ (wallis (1+ n)))
                        (* (/ (wallis (1- n)))
                           (/ (+ n 1) n))))
      :hints (("Goal"
               :use ((:instance wallis-recurrence
                                (n (1+ n)))
                                        )
               :in-theory (disable wallis-recurrence)))))

   (local
    (defthmd lemma-6
        (implies (and (natp n)
                      (<= 1 n))
                 (equal (/ (wallis n) (wallis (1+ n)))
                        (* (/ (wallis n)
                              (wallis (1- n)))
                           (/ (+ n 1) n))))
      :hints (("Goal"
               :use ((:instance lemma-5))
               :in-theory (disable wallis-recurrence)))))

   (local
    (defthmd lemma-7
        (implies (and (natp n)
                      (i-large n))
                 (natp (1- n)))
      :hints (("Goal"
               :use ((:instance large->=-2))
               :in-theory (disable large->=-2)))))

   (local
    (defthmd lemma-8
        (implies (and (natp n)
                      (i-large n))
                 (not (i-large (+ 1 (/ n)))))
      :hints (("Goal"
               :use ((:instance large-if->-large
                                (x (+ 1 (/ n)))
                                (y 2))
                     )
               :in-theory (disable large-if->-large)))))


   (defthm wallis-quotient-asymptotic-2
       (implies (and (natp n)
                     (i-large n))
                (equal (standard-part (/ (wallis n) (wallis (1- n)))) 1))
     :hints (("Goal"
              :use ((:instance lemma-6)
                    (:instance lemma-8)
                    (:instance wallis-quotient-asymptotic)
                    (:instance standard-part-of-times
                               (x (/ (wallis n) (wallis (1- n))))
                               (y (/ (+ n 1) n)))

                    )
              :in-theory (disable STANDARD-PART-OF-times
                                  wallis-recurrence)
              )
             )
     :otf-flg t
     )

   )
 )

(local
 (defthm-std standard-2/pi
     (standardp (* 2 (/ (ACL2-PI))))))

(local
 (defthm-std standard-2/pi
     (standardp (* 2 (/ (ACL2-PI))))))

(LOCAL
 (DEFTHM limited-2/pi
     (not (i-large (* 2 (/ (ACL2-PI)))))
   :hints (("Goal"
            :use ((:instance standards-are-limited
                             (x (* 2 (/ (ACL2-PI))))))
            :in-theory (disable standards-are-limited)))))

(encapsulate
    nil

    (local
     (defthmd lemma-1
         (implies (natp n)
                  (>= (wallis (1+ n))
                      (wallis (+ n 2))))
       :hints (("Goal"
                :use ((:instance wallis-decreasing
                                 (n (1+ n))))
                :in-theory (disable wallis-positive)))))

  (local
     (defthmd lemma-2
         (implies (and (natp n)
                       (<= 2 n))
                  (>= (/ (wallis (1+ n)) (wallis n))
                      (/ (wallis (+ n 2)) (wallis n))))
       :hints (("Goal"
                :use ((:instance lemma-1)
                      )
                ))))

  (local
   (defthmd lemma-3
       (implies (and (natp n)
                     (<= 2 n))
                (equal (/ (wallis (+ n 2)) (wallis n))
                       (/ (+ n 1)
                          (+ n 2))))
     :hints (("Goal"
              :use ((:instance wallis-recurrence (n (+ n 2)))
                    )
              :in-theory (disable wallis-recurrence)))))


  (local
     (defthmd lemma-4
         (implies (and (natp n)
                       (<= 2 n))
                  (>= (/ (wallis (1+ n)) (wallis n))
                      (/ (+ n 1) (+ n 2))))
       :hints (("Goal"
                :use ((:instance lemma-2)
                      (:instance lemma-3)
                      )
                :in-theory (disable wallis-recurrence)
                ))))

    (local
     (defthmd lemma-5
         (implies (and (natp n)
                       (<= 2 n))
                  (<= (/ (wallis n) (wallis (1+ n)))
                      (/ (+ n 2) (+ n 1))))
       :hints (("Goal"
                :use ((:instance lemma-4)
                      (:instance
                       (:theorem
                        (implies (and (realp x)
                                      (realp y)
                                      (< 0 x)
                                      (< 0 y)
                                      (>= x y))
                                 (<= (/ x) (/ y))))
                       (x (/ (wallis (1+ n)) (wallis n)))
                       (y (/ (+ n 1) (+ n 2))))
                      )
                :in-theory (disable wallis-recurrence)
                ))
       :otf-flg t
       ))

    (local
     (defthmd lemma-6
         (implies (posp n)
                  (equal (/ (+ n 2) (+ n 1))
                         (+ (/ n (+ n 1))
                            (/ 2 (+ n 1)))))))

    (local
     (defthmd lemma-7
         (implies (posp n)
                  (<= (/ n (+ n 1))
                      1))))

    (local
     (defthmd lemma-8
         (implies (posp n)
                  (<= (/ 2 (+ n 1))
                      2))))

    (local
     (defthmd lemma-9
         (implies (posp n)
                  (<= (/ (+ n 2) (+ n 1))
                      3))
       :hints (("Goal"
                :use ((:instance lemma-6)
                      (:instance lemma-7)
                      (:instance lemma-8)
                      (:instance
                       (:theorem (implies (and (realp x)
                                               (realp y)
                                               (realp z)
                                               (realp y2)
                                               (realp z2)
                                               (equal (+ y z) x)
                                               (<= y y2)
                                               (<= z z2)n
                                               )
                                          (<= x (+ y2 z2))))
                       (x (* (+ N 2) (/ (+ N 1))))
                       (y (* N (/ (+ N 1))))
                       (z (* 2 (/ (+ N 1))))
                       (y2 1)
                       (z2 2))
                      )
                ))))

    (defthm limited-wallis-quotient
        (implies (and (natp n)
                      (<= 2 n))
                 (not (i-large (/ (wallis n) (wallis (1+ n))))))
      :hints (("Goal"
               :use ((:instance large-if->-large
                                (x (/ (wallis n) (wallis (1+ n))))
                                (y 4))
                     (:instance lemma-5)
                     (:instance lemma-9))
               :in-theory (disable wallis-recurrence))))
    )

(local
 (defthm limited-wallis-expansion
     (implies (and (natp n)
                   (<= 2 n))
              (not (i-large (/ (wallis-expansion n) (wallis-expansion (1+ n))))))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance limited-wallis-quotient)
                  (:instance wallis-as-wallis-expansion-for-evens)
                  (:instance wallis-as-wallis-expansion-for-evens (n (1+ n)))
                  (:instance wallis-as-wallis-expansion-for-odds)
                  (:instance wallis-as-wallis-expansion-for-odds (n (1+ n))))
            :in-theory (disable limited-wallis-quotient
                                WALLIS-RECURRENCE
                                WALLIS-EXPANSION-FOR-EVENS
                                WALLIS-EXPANSION-FOR-ODDS)))))

(local
 (defthm-std standard-pi/2
     (standardp (/ (acl2-pi) 2))))

(local
 (defthm not-small-pi/2
     (not (i-small (/ (acl2-pi) 2)))
   :hints (("Goal"
            :use ((:instance standard-small-is-zero
                             (x (/ (acl2-pi) 2))))))))

(local
 (defthm not-small-2/pi
     (not (i-small (/ 2 (acl2-pi))))
   :hints (("Goal"
            :use ((:instance standard-small-is-zero
                             (x (/ 2 (acl2-pi)))))))))


(local
 (defthm wallis-factor-not-0
     (not (equal (wallis-factor n) 0))))


(local
 (defthm limited-wallis-factor
     (implies (and (natp n)
                   (<= 2 n))
              (not (i-large (/ (wallis-factor n) (wallis-factor (1+ n))))))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance large*limited->large
                             (x (/ (wallis-factor n)
                                   (wallis-factor (1+ n))))
                             (y (/ (acl2-pi) 2))
                             )
                  (:instance large*limited->large
                             (x (/ (wallis-factor n)
                                   (wallis-factor (1+ n))))
                             (y (/ 2 (acl2-pi)))
                             )
                  (:instance wallis-expansion-for-evens)
                  (:instance wallis-expansion-for-odds)
                  (:instance wallis-expansion-for-evens (n (1+ n)))
                  (:instance wallis-expansion-for-odds (n (1+ n)))
                  (:instance limited-wallis-expansion)
                  )
            :in-theory (disable WALLIS-RECURRENCE
                                WALLIS-EXPANSION-FOR-EVENS
                                WALLIS-EXPANSION-FOR-ODDS
                                limited-wallis-expansion)))
   :otf-flg t
   ))



(local
    (defthmd limited-wallis-quotient-down
        (implies (and (natp n)
                      (<= 1 n))
                 (not (i-large (/ (wallis n) (wallis (1- n))))))
      :hints (("Goal"
               :use ((:instance wallis-decreasing (n (1- n)))
                     (:instance large-if->-large
                                (x (/ (wallis n) (wallis (1- n))))
                                (y 1))
                     )
               :in-theory (disable wallis-decreasing
                                   WALLIS-RECURRENCE)))))


(local
 (defthmd limited-wallis-factor-qoutient-lemma
     (implies (and (natp n)
                   (not (evenp n))
                   (<= 2 n)
                   (I-LARGE (* (WALLIS-FACTOR N)
                               (/ (WALLIS-FACTOR (+ -1 N))))))
              (i-large (/ (wallis n) (wallis (1- n)))))
   :hints (("Goal"
            :use ((:instance wallis-quotient-simplifier)
                  (:instance limited*large->large
                             (x (/ 2 (acl2-pi)))
                             (y (* (WALLIS-FACTOR N)
                                   (/ (WALLIS-FACTOR (+ -1 N)))))))
            :in-theory (disable limited*large->large
                                wallis-factor
                                wallis-recurrence)))))

(local
 (defthmd limited-wallis-quotient-down
     (implies (and (natp n)
                   (<= 1 n))
              (not (i-large (/ (wallis n) (wallis (1- n))))))
   :hints (("Goal"
            :use ((:instance wallis-decreasing (n (1- n)))
                  (:instance large-if->-large
                             (x (/ (wallis n) (wallis (1- n))))
                             (y 1))
                  )
            :in-theory (disable wallis-decreasing
                                WALLIS-RECURRENCE)))))


(local
 (defthm limited-wallis-factor-qoutient
     (implies (and (natp n)
                   (not (evenp n))
                   (<= 2 n))
              (not (I-LARGE (* (WALLIS-FACTOR N)
                               (/ (WALLIS-FACTOR (+ -1 N)))))))
   :hints (("Goal"
            :use ((:instance limited-wallis-factor-qoutient-lemma)
                  (:instance limited-wallis-quotient-down))
            ))))

(local
 (defthm wallis-product-lemma
     (implies (and (natp n)
                   (not (evenp n))
                   (i-large n))
              (equal (standard-part (/ (wallis-factor n) (wallis-factor (1- n))))
                     (/ (acl2-pi) 2)))
   :hints (("Goal"
            :Do-not-induct t
            :use ((:instance wallis-quotient-asymptotic-2)
                  (:instance wallis-quotient-simplifier)
                  (:instance STANDARD-PART-OF-TIMES
                             (x (* 2 (/ (ACL2-PI))))
                             (y (*  (WALLIS-FACTOR N)
                                    (/ (WALLIS-FACTOR (1- N))))))
                  (:instance
                   (:theorem (implies (equal x y)
                                      (equal (standard-part x)
                                             (standard-part y))))
                   (x (* (WALLIS N) (/ (WALLIS (1- N)))))
                   (y (* 2 (/ (ACL2-PI))
                         (WALLIS-FACTOR N)
                         (/ (WALLIS-FACTOR (1- N))))))
                  (:instance
                   (:theorem
                    (implies (and (realp x)
                                  (realp y)
                                  (realp z)
                                  (< 0 x)
                                  (equal x (* (/ y) z)))
                             (equal (* x y) z)))
                   (x 1/2)
                   (y (acl2-pi))
                   (z (STANDARD-PART (* (WALLIS-FACTOR N)
                                          (/ (WALLIS-FACTOR (1- N)))))))
                  )
            :in-theory (disable STANDARD-PART-OF-TIMES

                                standard-part-of-plus
                                wallis-recurrence
                                ;large-if->-large
                                )
            ))
   :otf-flg t
   ))

(defun wallis-product (n)
  (if (zp n)
      1
      (* (/ (* 2 n) (1- (* 2 n)))
         (/ (* 2 n) (1+ (* 2 n)))
         (wallis-product (1- n)))))

(Defun wallis-product-list (n)
  (if (zp n)
      nil
      (list* (/ (* 2 n) (1- (* 2 n)))
             (/ (* 2 n) (1+ (* 2 n)))
             (wallis-product-list (1- n)))))

(local
 (encapsulate
     nil

     (local
      (defthmd lemma-1
          (IMPLIES (NOT (ZP N))
                   (EQUAL (/ (+ 1 (* -1/2 (/ N))))
                          (* (/ (+ 1 (* -1/2 (/ N)))) (/ 2 2))
                          ))
        ))

   (local
    (defthmd lemma-2
        (IMPLIES (NOT (ZP N))
                 (EQUAL (/ (+ 1 (* -1/2 (/ N))))
                        (/ 2 (* (+ 1
                                   (* -1/2
                                      (/ N)))
                                2))
                        ))
      :hints (("Goal"
               :use ((:instance lemma-1))))
      ))

   (local
    (defthmd lemma-3
        (IMPLIES (NOT (ZP N))
                 (EQUAL (* (+ 1 (* -1/2 (/ N))) 2)
                        (+ 2 (* -1 (/ N)))))))

   (local
    (defthmd lemma-4
        (IMPLIES (NOT (ZP N))
                 (EQUAL (/ (+ 1 (* -1/2 (/ N))))
                        (/ 2 (+ 2 (* -1 (/ N))))
                        ))
      :hints (("Goal"
               :use ((:instance lemma-2)
                     (:instance lemma-3)
                     )
               :IN-THEORY NIL))
      ))

   (local
    (defthmd lemma-5
        (IMPLIES (NOT (ZP N))
                 (EQUAL (/ (+ 1 (* -1/2 (/ N))))
                        (* (/ 2 (+ 2 (* -1 (/ N)))) (/ n n))
                        ))
      :hints (("Goal"
               :use ((:instance lemma-4)
                     )
               ))
      ))

   (local
    (defthmd lemma-6
        (IMPLIES (NOT (ZP N))
                 (EQUAL (/ (+ 1 (* -1/2 (/ N))))
                        (/ (* 2 N) (* n (+ 2 (* -1 (/ N)))))
                        ))
      :hints (("Goal"
               :use ((:instance lemma-5)
                     )
               ))
      ))

   (local
    (defthmd lemma-7
        (IMPLIES (NOT (ZP N))
                 (EQUAL (* n (+ 2 (* -1 (/ N))))
                        (+ -1 (* 2 n))))
      ))

   (local
    (defthmd lemma-8
        (IMPLIES (NOT (ZP N))
                 (EQUAL (/ (+ 1 (* -1/2 (/ N))))
                        (* (* 2 N) (/ (+ -1 (* 2 N))))))
      :hints (("Goal"
               :use ((:instance lemma-6)
                     (:instance lemma-7)
                     )
               :in-theory nil
               ))
      ))

   (local
    (defthm lemma-9
        (IMPLIES (NOT (ZP N))
                 (EQUAL (* 2 N (/ (+ -1 (* 2 N))))
                        (/ (+ 1 (* -1/2 (/ N))))))
      :hints (("Goal"
               :use ((:instance lemma-8))))
      ))

   (defthm wallis-product-lemma-1
       (implies (natp n)
                (equal (wallis-product n)
                       (/ (wallis-factor (1+ (* 2 n)))
                          (wallis-factor (* 2 n)))))
     :otf-flg t)))

(defthm wallis-product-convergence
    (implies (and (natp n)
                  (i-large n))
             (equal (standard-part (wallis-product n))
                    (/ (acl2-pi) 2)))
  :hints (("Goal"
           :use ((:instance wallis-product-lemma-1)
                 (:instance wallis-product-lemma (n (1+ (* 2 n))))
                 )
           :in-theory (disable wallis-product-lemma-1
                               wallis-product
                               wallis-factor)
           )
          )
  :otf-flg t)


(defun df-wallis-product (n)
  (if (zp n)
      (to-df 1)
      (df* (df/ (df* 2 (to-df n))
                (df- 1 (df* 2 (to-df n))))
           (df/ (df* 2 (to-df n))
                (df+ 1 (df* 2 (to-df n))))
           (df-wallis-product (1- n)))))

#|
ACL2(r) !>(df* 2 (df-wallis-product 10))
(df* 2 (df-wallis-product 10))
#d3.067703806643497
ACL2(r) !>(df* 2 (df-wallis-product 20))
(df* 2 (df-wallis-product 20))
#d3.1035169615392313
ACL2(r) !>(df* 2 (df-wallis-product 40))
(df* 2 (df-wallis-product 40))
#d3.122260326421433
ACL2(r) !>(df* 2 (df-wallis-product 100))
(df* 2 (df-wallis-product 100))
#d3.133787490628159
ACL2(r) !>(df* 2 (df-wallis-product 1000))
(df* 2 (df-wallis-product 1000))
#d3.1408077460303865
ACL2(r) !>(df* 2 (df-wallis-product 10000))
(df* 2 (df-wallis-product 10000))
#d3.1415141186818567
|#
