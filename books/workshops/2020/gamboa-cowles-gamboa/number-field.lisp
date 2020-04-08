(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/take" :dir :system))


(encapsulate
  (((number-field-p *) => *))

  (local
   (defun number-field-p (x)
     (rationalp x)))

  (defthm number-field-is-numeric
    (implies (number-field-p x)
             (acl2-numberp x)))

  (defthm number-field-is-closed-addition
    (implies (and (number-field-p x)
                  (number-field-p y))
             (number-field-p (+ x y))))

  (defthm number-field-is-closed-multiplication
    (implies (and (number-field-p x)
                  (number-field-p y))
             (number-field-p (* x y))))

  (defthm number-field-has-additive-inverse
    (implies (number-field-p x)
             (number-field-p (- x))))

  (defthm number-field-has-multiplicative-inverse
    (implies (and (number-field-p x)
                  (not (equal x 0)))
             (number-field-p (/ x))))

  (defthm number-field-is-not-empty
    (and (number-field-p 0)
         (number-field-p 1))))


(defun scale-prods (k prods)
  (if (consp prods)
      (cons (* k (first prods))
            (scale-prods k (rest prods)))
    nil))

(defun all-products (exts)
  (if (consp exts)
      (let ((prods (all-products (rest exts))))
        (append prods
                (scale-prods (first exts) prods)))
    (list 1)))

(defthm len-append
  (equal (len (append x y))
         (+ (len x) (len y))))

(defthm len-scale-prods
  (equal (len (scale-prods k x))
         (len x)))

(defthm len-all-products
  (equal (len (all-products x))
         (expt 2 (len x))))


(defun eval-linear-combination (coords span)
  (if (consp coords)
      (+ (* (first coords) (first span))
         (eval-linear-combination (rest coords) (rest span)))
    0))

(defun-sk is-linear-combination-p (x exts)
  (exists coords
          (and (rational-listp coords)
               (equal (len coords) (expt 2 (len exts)))
               (equal (eval-linear-combination coords (all-products exts))
                      x))))

(defun map-zero (l)
  (if (consp l)
      (cons 0 (map-zero (rest l)))
    nil))

(defthm rational-listp-map-zero
  (rational-listp (map-zero l)))

(defthm len-map-zero
  (equal (len (map-zero l))
         (len l)))

(defthm eval-linear-combination-map-zero
  (equal (eval-linear-combination (map-zero coords) span) 0)
  :hints (("Goal"
           :do-not-induct t
           :induct (eval-linear-combination coords span))))

(defthm rational-listp-append
  (implies (and (rational-listp x)
                (rational-listp y))
           (rational-listp (append x y))))

(defun eval-linear-combination-append-coords-hint (coords1 coords2 x)
  (if (consp coords1)
      (eval-linear-combination-append-coords-hint (rest coords1)
                                                  coords2
                                                  (rest x))
    (list coords2 x)))

(defthm eval-linear-combination-append-coords-lemma-1
  (implies (consp coords1)
           (equal (eval-linear-combination (append coords1 coords2) x)
                  (+ (* (first coords1) (first x))
                     (eval-linear-combination (append (rest coords1) coords2) (rest x))))))


(defthm eval-linear-combination-append-coords
  (equal (eval-linear-combination (append coords1 coords2) x)
         (+ (eval-linear-combination coords1 (take (len coords1) x))
            (eval-linear-combination coords2 (nthcdr (len coords1) x))))
  :hints (("Goal"
           :do-not-induct t
           :induct (eval-linear-combination-append-coords-hint coords1 coords2 x))))

(defthm is-linear-combination-is-tower
  (implies (consp exts)
           (implies (is-linear-combination-p x (cdr exts))
                    (is-linear-combination-p x exts)))
  :hints (("Goal"
           :use ((:instance is-linear-combination-p-suff
                            (x x)
                            (exts exts)
                            (coords (append (is-linear-combination-p-witness x (cdr exts))
                                            (map-zero (is-linear-combination-p-witness x (cdr exts))))))
                 )
           )))

(defthm rational-is-linear-combination
  (implies (rationalp x)
           (is-linear-combination-p x exts))
  :hints (("Goal"
           :induct (map-zero exts))
          ("Subgoal *1/2"
           :use ((:instance is-linear-combination-p-suff
                            (x x)
                            (exts exts)
                            (coords (list x)))))
          ))


(defthm is-linear-combination-p-is-numeric
  (implies (is-linear-combination-p x exts)
           (acl2-numberp x)))

(defun add-coords (coords1 coords2)
  (if (consp coords1)
      (cons (+ (first coords1) (first coords2))
            (add-coords (rest coords1) (rest coords2)))
    nil))

(defthm len-add-coords
  (equal (len (add-coords coords1 coords2))
         (len coords1)))

(defthm rational-list-p-add-coords
  (implies (and (rational-listp coords1)
                (rational-listp coords2))
           (rational-listp (add-coords coords1 coords2))))

(defthm sum-of-linear-combinations
  (implies (equal (len coords1) (len coords2))
           (equal (eval-linear-combination (add-coords coords1 coords2) exts)
                  (+ (eval-linear-combination coords1 exts)
                     (eval-linear-combination coords2 exts)))))

(defthm is-linear-combination-p-is-closed-addition
  (implies (and (is-linear-combination-p x exts)
                (is-linear-combination-p y exts))
           (is-linear-combination-p (+ x y) exts))
  :hints (("Goal"
           :use ((:instance is-linear-combination-p-suff
                            (x (+ x y))
                            (exts exts)
                            (coords (add-coords (is-linear-combination-p-witness x exts)
                                                (is-linear-combination-p-witness y exts))))
                 )
           ))
  )


(defun negate-coords (coords)
  (if (consp coords)
      (cons (- (first coords))
            (negate-coords (rest coords)))
    nil))

(defthm len-negate-coords
  (equal (len (negate-coords coords))
         (len coords)))

(defthm rational-list-p-negate-coords
  (implies (rational-listp coords)
           (rational-listp (negate-coords coords))))

(defthm negate-of-linear-combination
  (equal (eval-linear-combination (negate-coords coords) exts)
         (- (eval-linear-combination coords exts))))

(defthm is-linear-combination-p-has-additive-inverse
  (implies (is-linear-combination-p x exts)
           (is-linear-combination-p (- x) exts))
  :hints (("Goal"
           :use ((:instance is-linear-combination-p-suff
                            (x (- x))
                            (exts exts)
                            (coords (negate-coords (is-linear-combination-p-witness x exts))))
                 )
           ))
  )



(defthm eval-linear-combination-of-single
  (implies (and (equal (len coords) 1)
                (rational-listp coords))
           (EQUAL (EVAL-LINEAR-COMBINATION coords l)
                  (* (first coords) (first l)))))

(defthm rational-listp-take
  (implies (and (rational-listp l)
                (<= n (len l)))
           (rational-listp (take n l))))

(defthm rational-listp-nthcdr
  (implies (rational-listp l)
           (rational-listp (nthcdr n l))))




(defthm scale-prods-append
  (equal (scale-prods k (append x y))
         (append (scale-prods k x)
                 (scale-prods k y))))

(defun eval-linear-combination-append-hint (coords x y)
  (if (consp x)
      (eval-linear-combination-append-hint (rest coords)
                                           (rest x)
                                           y)
    (list y coords)))

(defthm eval-linear-combination-append
  (equal (eval-linear-combination coords (append x y))
         (+ (eval-linear-combination (take (len x) coords) x)
            (eval-linear-combination (nthcdr (len x) coords) y)))
  :hints (("Goal"
           :do-not-induct t
           :induct (eval-linear-combination-append-hint coords x y))))

(defun eval-linear-combination-split-hint (coords exts)
  (if (consp exts)
      (list (eval-linear-combination-split-hint (take (expt 2 (len (rest exts))) coords)
                                                (rest exts))
            (eval-linear-combination-split-hint (nthcdr (expt 2 (len (rest exts))) coords)
                                                (rest exts)))
    coords))

(defthm eval-linear-combination-scale-prods
  (equal (eval-linear-combination coords (scale-prods k l))
         (* k (eval-linear-combination coords l))))

(defthm rational-listp-take-expt-len-cddr
  (implies (and (consp exts)
                (consp (cdr exts))
                (rational-listp coords)
                (equal (len coords)
                       (expt 2 (+ 2 (len (cddr exts))))))
           (rational-listp (take (expt 2 (+ 1 (len (cddr exts)))) coords)))
  :hints (("Goal"
           :use ((:instance rational-listp-take
                            (l coords)
                            (n (expt 2 (+ 1 (len (cddr exts))))))))))

(defthmd eval-linear-combination-split
  (implies (and (equal (len coords) (expt 2 (len exts)))
                (rational-listp coords)
                (acl2-number-listp exts))
           (equal (eval-linear-combination coords (all-products exts))
                  (if (consp exts)
                      (+ (eval-linear-combination (take (expt 2 (len (rest exts))) coords)
                                                  (all-products (rest exts)))
                         (* (first exts)
                            (eval-linear-combination (nthcdr (expt 2 (len (rest exts))) coords)
                                                     (all-products (rest exts)))))
                    (first coords))))
  :hints (("Goal"
           :do-not-induct t
           :induct (eval-linear-combination-split-hint coords exts))))




(defthm eval-linear-combination-product-split-1
  (implies (and (equal (len coords1) (expt 2 (len exts)))
                (rational-listp coords1)
                (equal (len coords2) (expt 2 (len exts)))
                (rational-listp coords2)
                (acl2-number-listp exts))
           (equal (* (eval-linear-combination coords1 (all-products exts))
                     (eval-linear-combination coords2 (all-products exts)))
                  (if (consp exts)
                      (+ (* (eval-linear-combination (take (expt 2 (len (rest exts))) coords1)
                                                     (all-products (rest exts)))
                            (eval-linear-combination (take (expt 2 (len (rest exts))) coords2)
                                                     (all-products (rest exts))))
                         (* (first exts)
                            (eval-linear-combination (take (expt 2 (len (rest exts))) coords1)
                                                     (all-products (rest exts)))
                            (eval-linear-combination (nthcdr (expt 2 (len (rest exts))) coords2)
                                                     (all-products (rest exts))))
                         (* (first exts)
                            (eval-linear-combination (take (expt 2 (len (rest exts))) coords2)
                                                     (all-products (rest exts)))
                            (eval-linear-combination (nthcdr (expt 2 (len (rest exts))) coords1)
                                                     (all-products (rest exts))))
                         (* (expt (first exts) 2)
                            (eval-linear-combination (nthcdr (expt 2 (len (rest exts))) coords1)
                                                     (all-products (rest exts)))
                            (eval-linear-combination (nthcdr (expt 2 (len (rest exts))) coords2)
                                                     (all-products (rest exts)))))
                    (* (first coords1) (first coords2)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance eval-linear-combination-split
                            (coords coords1)
                            (exts exts))
                 (:instance eval-linear-combination-split
                            (coords coords2)
                            (exts exts)))
           :in-theory (disable eval-linear-combination-split eval-linear-combination all-products take nthcdr))))







(defun product-coords (coords1 coords2 exts)
  (if (consp exts)
      (append (add-coords (product-coords (take (expt 2 (len (rest exts))) coords1)
                                          (take (expt 2 (len (rest exts))) coords2)
                                          (rest exts))
                          (product-coords (is-linear-combination-p-witness (expt (first exts) 2) (rest exts))
                                          (product-coords (nthcdr (expt 2 (len (rest exts))) coords1)
                                                          (nthcdr (expt 2 (len (rest exts))) coords2)
                                                          (rest exts))
                                          (rest exts)))
              (add-coords (product-coords (take (expt 2 (len (rest exts))) coords1)
                                          (nthcdr (expt 2 (len (rest exts))) coords2)
                                          (rest exts))
                          (product-coords (take (expt 2 (len (rest exts))) coords2)
                                          (nthcdr (expt 2 (len (rest exts))) coords1)
                                          (rest exts))))
    (list (* (first coords1) (first coords2)))))

(defun quadratic-extensions-p (exts)
  (if (consp exts)
      (and (acl2-numberp (first exts))
           (not (is-linear-combination-p (first exts) (rest exts)))
           (is-linear-combination-p (expt (first exts) 2) (rest exts))
           (quadratic-extensions-p (rest exts)))
    (equal exts nil)))

(defthm quadratic-extension-is-number-listp
  (implies (quadratic-extensions-p exts)
           (acl2-number-listp exts)))

(defthm len-product-coords
  (equal (len (product-coords coords1 coords2 exts))
         (expt 2 (len exts))))

(defthm car-product-coords-of-single-1
  (implies (and (consp exts)
                (not (cdr exts))
                (quadratic-extensions-p exts)
                (equal (len coords1) 2)
                (equal (len coords2) 2)
                (rational-listp coords1)
                (rational-listp coords2))
           (equal (car (product-coords coords1 coords2 exts))
                  (+ (* (first coords1) (first coords2))
                     (* (car exts) (car exts)
                        (second coords1) (second coords2))))))

(defthm cadr-product-coords-of-single-1
  (implies (and (consp exts)
                (not (cdr exts))
                (quadratic-extensions-p exts)
                (equal (len coords1) 2)
                (equal (len coords2) 2)
                (rational-listp coords1)
                (rational-listp coords2))
           (equal (cadr (product-coords coords1 coords2 exts))
                  (+ (* (first coords1) (second coords2))
                     (* (first coords2) (second coords1))))))


(defthm len-all-products-cdr-exts
  (implies (and (consp exts)
                (equal (len coords)
                       (expt 2 (+ 1 (len (cdr exts))))))
           (< (expt 2 (len (cdr exts)))
              (len coords)))
  :rule-classes :linear)




(defthm quadratic-extensions-p-forward
  (implies (quadratic-extensions-p exts)
           (quadratic-extensions-p (cdr exts)))
  :rule-classes :forward-chaining)

(defthm rational-listp-take-len-all-prods
  (implies (and (equal (len coords) (expt 2 (len exts)))
                (consp exts)
                (rational-listp coords))
           (rational-listp (take (expt 2 (len (cdr exts))) coords)))
  :hints (("Goal"
           :use ((:instance rational-listp-take
                            (n (expt 2 (len (cdr exts))))
                            (l coords)))))
  :rule-classes :forward-chaining)

(defthm expt-2-len-n-monotonic
  (implies (and (natp l)
                (natp n)
                (equal l (expt 2 (+ 1 n))))
           (< (expt 2 n) l))
  :rule-classes :linear)


(defthm rational-listp-nthcdr-len-all-prods
  (implies (and (equal (len coords) (expt 2 (len exts)))
                (rational-listp coords))
           (rational-listp (take (expt 2 (len (cdr exts)))
                                 coords)))
  :hints (("Goal"
           :use ((:instance rational-listp-take
                            (n (expt 2 (len (cdr exts))))
                            (l coords)))))
  :rule-classes :forward-chaining)

(defthm number-p-car-exts
  (implies (and (consp exts)
                (quadratic-extensions-p exts))
           (acl2-numberp (car exts)))
  :rule-classes :forward-chaining)

(defthm number-listp-cdr-exts
  (implies (and (consp exts)
                (quadratic-extensions-p exts))
           (quadratic-extensions-p (cdr exts)))
  :rule-classes :forward-chaining)

(defthm len-linear-combination-witness
  (implies (and (quadratic-extensions-p exts)
                (consp exts))
           (equal (len (is-linear-combination-p-witness
                        (expt (car exts) 2)
                        (cdr exts)))
                  (expt 2 (len (cdr exts))))))

(defthm rational-listp-linear-combination-witness
  (implies (and (quadratic-extensions-p exts)
                (consp exts))
           (rational-listp (is-linear-combination-p-witness
                            (expt (car exts) 2)
                            (cdr exts)))))

(defthm take-append-same-len
  (implies (and (equal (append x y) z)
                (true-listp x)
                (consp z))
           (equal (take (len x) z) x))
  )

(defthm take-first-part-of-product-coords
  (implies (consp exts)
           (equal (take (expt 2 (len (cdr exts)))
                        (product-coords coords1 coords2 exts))
                  (add-coords (product-coords (take (expt 2 (len (rest exts))) coords1)
                                              (take (expt 2 (len (rest exts))) coords2)
                                              (rest exts))
                              (product-coords (is-linear-combination-p-witness (* (first exts) (first exts)) (rest exts))
                                              (product-coords (nthcdr (expt 2 (len (rest exts))) coords1)
                                                              (nthcdr (expt 2 (len (rest exts))) coords2)
                                                              (rest exts))
                                              (rest exts)))))
  :hints (("Goal"
           :do-not-induct t
           :expand ((product-coords coords1 coords2 exts))
           :use ((:instance take-append-same-len
                            (x (ADD-COORDS
                                (PRODUCT-COORDS (TAKE (EXPT 2 (LEN (REST EXTS)))
                                                      COORDS1)
                                                (TAKE (EXPT 2 (LEN (REST EXTS)))
                                                      COORDS2)
                                                (REST EXTS))
                                (PRODUCT-COORDS
                                 (IS-LINEAR-COMBINATION-P-WITNESS
                                  (* (FIRST EXTS) (FIRST EXTS))
                                  (REST EXTS))
                                 (PRODUCT-COORDS (NTHCDR (EXPT 2 (LEN (REST EXTS)))
                                                         COORDS1)
                                                 (NTHCDR (EXPT 2 (LEN (REST EXTS)))
                                                         COORDS2)
                                                 (REST EXTS))
                                 (REST EXTS))))
                            (y (ADD-COORDS
                                (PRODUCT-COORDS (TAKE (EXPT 2 (LEN (REST EXTS)))
                                                      COORDS1)
                                                (NTHCDR (EXPT 2 (LEN (REST EXTS)))
                                                        COORDS2)
                                                (REST EXTS))
                                (PRODUCT-COORDS (TAKE (EXPT 2 (LEN (REST EXTS)))
                                                      COORDS2)
                                                (NTHCDR (EXPT 2 (LEN (REST EXTS)))
                                                        COORDS1)
                                                (REST EXTS))))
                            (z (product-coords coords1 coords2 exts))))
           :in-theory (disable take-append-same-len
                               product-coords)))  )

(defthm nthcdr-append-same-len
  (implies (and (equal (append x y) z)
                (consp z))
           (equal (nthcdr (len x) z) y))
  :hints (("Subgoal *1/1"
           :use ((:instance
                  (:theorem (implies (< 0 (len x)) (consp x)))
                  (x (cdr x)))
                 (:instance
                  (:theorem (implies (equal (len x) 0) (not (consp x))))
                  (x (cdr x))))))
  )

(defthm nthcdr-second-part-of-product-coords
  (implies (consp exts)
           (equal (nthcdr (expt 2 (len (cdr exts)))
                          (product-coords coords1 coords2 exts))
                  (add-coords (product-coords (take (expt 2 (len (rest exts))) coords1)
                                              (nthcdr (expt 2 (len (rest exts))) coords2)
                                              (rest exts))
                              (product-coords (take (expt 2 (len (rest exts))) coords2)
                                              (nthcdr (expt 2 (len (rest exts))) coords1)
                                              (rest exts)))))
  :hints (("Goal"
           :do-not-induct t
           :expand ((product-coords coords1 coords2 exts))
           :use ((:instance nthcdr-append-same-len
                            (x (ADD-COORDS
                                (PRODUCT-COORDS (TAKE (EXPT 2 (LEN (REST EXTS)))
                                                      COORDS1)
                                                (TAKE (EXPT 2 (LEN (REST EXTS)))
                                                      COORDS2)
                                                (REST EXTS))
                                (PRODUCT-COORDS
                                 (IS-LINEAR-COMBINATION-P-WITNESS
                                  (* (FIRST EXTS) (FIRST EXTS))
                                  (REST EXTS))
                                 (PRODUCT-COORDS (NTHCDR (EXPT 2 (LEN (REST EXTS)))
                                                         COORDS1)
                                                 (NTHCDR (EXPT 2 (LEN (REST EXTS)))
                                                         COORDS2)
                                                 (REST EXTS))
                                 (REST EXTS))))
                            (y (ADD-COORDS
                                (PRODUCT-COORDS (TAKE (EXPT 2 (LEN (REST EXTS)))
                                                      COORDS1)
                                                (NTHCDR (EXPT 2 (LEN (REST EXTS)))
                                                        COORDS2)
                                                (REST EXTS))
                                (PRODUCT-COORDS (TAKE (EXPT 2 (LEN (REST EXTS)))
                                                      COORDS2)
                                                (NTHCDR (EXPT 2 (LEN (REST EXTS)))
                                                        COORDS1)
                                                (REST EXTS))))
                            (z (product-coords coords1 coords2 exts))))
           :in-theory (disable nthcdr-append-same-len
                               product-coords))))


(defthm nthcdr-of-append
  (implies (equal (len x) lx)
           (equal (nthcdr lx (append x y)) y)))


(encapsulate
  nil
  
  (local
   (defthmd lemma-1
     (implies (and (quadratic-extensions-p exts)
                   (equal (len coords1) (expt 2 (len exts)))
                   (rational-listp coords1)
                   (equal (len coords2) (expt 2 (len exts)))
                   (rational-listp coords2)
                   (consp exts)
                   )
              (and (quadratic-extensions-p (cdr exts))
                   (equal (len (take (expt 2 (len (cdr exts)))
                                     coords1))
                          (expt 2 (len (cdr exts))))
                   (rational-listp (take (expt 2 (len (cdr exts)))
                                         coords1))
                   (equal (len (take (expt 2 (len (cdr exts)))
                                     coords2))
                          (expt 2 (len (cdr exts))))
                   (rational-listp (take (expt 2 (len (cdr exts)))
                                         coords2))
                   (equal (len (nthcdr (expt 2 (len (cdr exts)))
                                       coords1))
                          (expt 2 (len (cdr exts))))
                   (rational-listp (nthcdr (expt 2 (len (cdr exts)))
                                           coords1))
                   (equal (len (nthcdr (expt 2 (len (cdr exts)))
                                       coords2))
                          (expt 2 (len (cdr exts))))
                   (rational-listp (nthcdr (expt 2 (len (cdr exts)))
                                           coords2))                
                   (equal (len (is-linear-combination-p-witness (expt (car exts) 2)
                                                                (cdr exts)))
                          (expt 2 (len (cdr exts))))
                   (rational-listp
                    (is-linear-combination-p-witness (expt (car exts) 2)
                                                     (cdr exts)))
                   (equal (len (product-coords (nthcdr (expt 2 (len (cdr exts)))
                                                       coords1)
                                               (nthcdr (expt 2 (len (cdr exts)))
                                                       coords2)
                                               (cdr exts)))
                          (expt 2 (len (cdr exts))))
                   ))
     :INSTRUCTIONS (:PROMOTE :S (:DROP 1 3 4 5) :PROVE)
     ))

  (defthm rational-listp-product-coords
    (implies (and (quadratic-extensions-p exts)
                  (equal (len coords1) (expt 2 (len exts)))
                  (rational-listp coords1)
                  (equal (len coords2) (expt 2 (len exts)))
                  (rational-listp coords2))
             (rational-listp (product-coords coords1 coords2 exts)))
    :hints (("Goal"
             :do-not-induct t
             :induct (product-coords coords1 coords2 exts)
             )
            ("Subgoal *1/1"
             :expand ((PRODUCT-COORDS COORDS1 COORDS2 EXTS))
             :use ((:instance lemma-1))
             :in-theory (disable product-coords
                                 is-linear-combination-p
                                 quadratic-extensions-p
                                 rational-listp)
             )))

  (defthm rational-listp-product-coords-nthcdr
    (implies (and (equal (len coords1) (expt 2 (len exts)))
                  (equal (len coords2) (expt 2 (len exts)))
                  (rational-listp coords1)
                  (rational-listp coords2)
                  (quadratic-extensions-p (cdr exts))
                  (consp exts)
                  )
             (rational-listp (product-coords (nthcdr (expt 2 (len (cdr exts)))
                                                     coords1)
                                             (nthcdr (expt 2 (len (cdr exts)))
                                                     coords2)
                                             (cdr exts))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance rational-listp-product-coords
                              (coords1 (nthcdr (expt 2 (len (cdr exts))) coords1))
                              (coords2 (nthcdr (expt 2 (len (cdr exts))) coords2))
                              (exts (cdr exts))))
             :in-theory (disable rational-listp-product-coords)))
    )

  (local
   (defthmd lemma-2
     (implies (and (quadratic-extensions-p exts)
                   (equal (len coords1) (expt 2 (len exts)))
                   (rational-listp coords1)
                   (equal (len coords2) (expt 2 (len exts)))
                   (rational-listp coords2)
                   (consp exts)
                   )
              (and
               (quadratic-extensions-p (cdr exts))
               (equal (len (is-linear-combination-p-witness (expt (car exts) 2)
                                                            (cdr exts)))
                      (expt 2 (len (cdr exts))))
               (rational-listp
                (is-linear-combination-p-witness (expt (car exts) 2)
                                                 (cdr exts)))
               (rational-listp (product-coords (nthcdr (expt 2 (len (cdr exts)))
                                                       coords1)
                                               (nthcdr (expt 2 (len (cdr exts)))
                                                       coords2)
                                               (cdr exts)))))))

  


  (defthm product-of-linear-combinations
    (implies (and (quadratic-extensions-p exts)
                  (equal (len coords1) (expt 2 (len exts)))
                  (rational-listp coords1)
                  (equal (len coords2) (expt 2 (len exts)))
                  (rational-listp coords2)
                  )
             (equal (eval-linear-combination (product-coords coords1 coords2 exts)
                                             (all-products exts))
                    (* (eval-linear-combination coords1
                                                (all-products exts))
                       (eval-linear-combination coords2
                                                (all-products exts)))))
    :instructions ((:induct (product-coords coords1 coords2 exts))
                   :prove :promote (:use lemma-1)
                   :promote (:forwardchain 1)
                   (:demote 12)
                   :promote (:use lemma-2)
                   :promote (:forwardchain 1)
                   (:demote 24)
                   :promote (:forwardchain 2)
                   (:forwardchain 2)
                   (:forwardchain 2)
                   (:forwardchain 2)
                   (:forwardchain 2)
                   (:dv 1)
                   (:dv 1)
                   :x :up
                   (:rewrite eval-linear-combination-split)
                   (:dv 1)
                   :s :up :s (:dv 1)
                   (:rewrite sum-of-linear-combinations)
                   (:dv 1)
                   := :up (:dv 2)
                   := (:dv 1)
                   (:= (expt (car exts) 2))
                   :up (:dv 2)
                   := :up :up :nx (:dv 2)
                   (:dv 1)
                   (:rewrite nthcdr-of-append)
                   :up
                   (:rewrite sum-of-linear-combinations)
                   (:dv 1)
                   := :nx := :top (:dv 2)
                   (:rewrite eval-linear-combination-product-split-1)
                   (:dv 1)
                   (:= t)
                   :up :s (:dv 1)
                   := :nx (:dv 2)
                   := :top
                   (:in-theory (disable eval-linear-combination
                                        is-linear-combination-p
                                        quadratic-extensions-p))
                   :s :prove
                   :prove :prove :prove :prove (:dv 1)
                   (:rewrite len-append)
                   (:dv 1)
                   (:rewrite len-add-coords)
                   (:rewrite len-product-coords)
                   :nx (:rewrite len-add-coords)
                   (:rewrite len-product-coords)
                   :up :up (:demote 1)
                   :drop
                   :prove (:rewrite rational-listp-append)
                   (:rewrite rational-list-p-add-coords)
                   (:rewrite rational-listp-product-coords)
                   (:rewrite rational-listp-product-coords)
                   (:rewrite rational-list-p-add-coords)
                   (:rewrite rational-listp-product-coords)
                   (:rewrite rational-listp-product-coords)
                   :prove)
    )
  )


(defthm is-linear-combination-p-is-closed-multiplication
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p y exts))
           (is-linear-combination-p (* x y) exts))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance is-linear-combination-p-suff
                            (x (* x y))
                            (exts exts)
                            (coords (product-coords (is-linear-combination-p-witness x exts)
                                                    (is-linear-combination-p-witness y exts)
                                                    exts)))
                 (:instance rational-listp-product-coords
                            (coords1 (is-linear-combination-p-witness x exts))
                            (coords2 (is-linear-combination-p-witness y exts))
                            (exts exts))
                 )
           :in-theory (disable rational-listp-product-coords
                               quadratic-extensions-p
;is-linear-combination-p
                               eval-linear-combination
                               EVAL-LINEAR-COMBINATION-PRODUCT-SPLIT-1)
           ))
  )

(defun subfield-part (x exts)
  (if (consp exts)
      (eval-linear-combination (take (expt 2 (len (rest exts)))
                                     (is-linear-combination-p-witness x exts))
                               (all-products (rest exts)))
    (fix x)))

(defun extension-part (x exts)
  (if (consp exts)
      (eval-linear-combination (nthcdr (expt 2 (len (rest exts)))
                                       (is-linear-combination-p-witness x exts))
                               (all-products (rest exts)))
    0))

(defun is-linear-combination-listp (l exts)
  (if (consp l)
      (and (is-linear-combination-p (first l) exts)
           (is-linear-combination-listp (rest l) exts))
    (equal l nil)))

(defthmd rational-listp-is-linear-combination-listp
  (implies (rational-listp l)
           (is-linear-combination-listp l exts))
  :hints (("Subgoal *1/3"
           :use ((:instance rational-is-linear-combination
                            (x (car l))
                            (exts exts)))
           :in-theory (disable rational-is-linear-combination))))


(defun list-of-zeros (n)
  (if (zp n)
      nil
    (cons 0 (list-of-zeros (1- n)))))

(defun all-zeros-p (l)
  (if (consp l)
      (and (equal (first l) 0)
           (all-zeros-p (rest l)))
    (equal l nil)))

(defthm eval-linear-combination-all-zeros
  (implies (all-zeros-p l)
           (equal (eval-linear-combination l span) 0)))

(defthm all-zeros-p-list-of-zeros
  (all-zeros-p (list-of-zeros n)))

(defthm len-list-of-zeros
  (equal (len (list-of-zeros n)) (nfix n)))

(defthm car-all-products
  (equal (car (all-products exts)) 1))

(defthm is-linear-combination-car-exts-lemma-1
  (implies (and (consp exts)
                (acl2-number-listp exts)
                )
           (equal (eval-linear-combination (append (list-of-zeros (expt 2 (len (rest exts))))
                                                   (cons 1 (list-of-zeros (1- (expt 2 (len (rest exts)))))))
                                           (all-products exts))
                  (first exts)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance eval-linear-combination-split
                            (coords (append (list-of-zeros (expt 2 (len (rest exts))))
                                            (cons 1 (list-of-zeros (1- (expt 2 (len (rest exts))))))))
                            (exts exts)))
           :in-theory (disable eval-linear-combination-split))))

(defthm rational-listp-list-of-zeros
  (rational-listp (list-of-zeros n)))

(defthm is-linear-combination-car-exts-lemma-2
  (rational-listp (append (list-of-zeros (expt 2 (len (rest exts))))
                          (cons 1 (list-of-zeros (1- (expt 2 (len (rest exts)))))))))

(defthm is-linear-combination-car-exts
  (implies (and (consp exts)
                (quadratic-extensions-p exts))
           (is-linear-combination-p (car exts) exts))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance is-linear-combination-p-suff
                            (x (car exts))
                            (exts exts)
                            (coords (append (list-of-zeros (expt 2 (len (rest exts))))
                                            (cons 1 (list-of-zeros (1- (expt 2 (len (rest exts)))))))))
                 (:instance is-linear-combination-car-exts-lemma-1)
                 )
           :in-theory (disable is-linear-combination-car-exts-lemma-1)))
  )



(defthmd is-linear-combination-eval-linear-combination-lemma-1
  ;; SLOW
  (implies (and (is-linear-combination-listp coords exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-listp l exts))
           (is-linear-combination-p (eval-linear-combination coords l)
                                    exts))
  :hints (("Goal"
           :do-not-induct t
           :induct (eval-linear-combination coords l))
          ("Subgoal *1/1"
           :use ((:instance is-linear-combination-p-is-closed-multiplication
                            (x (first coords))
                            (y (first l)))
                 (:instance is-linear-combination-p-is-closed-addition
                            (x (* (first coords) (first l)))
                            (y (eval-linear-combination (rest coords) (rest l)))))
           :in-theory (disable is-linear-combination-p-is-closed-multiplication
                               is-linear-combination-p-is-closed-addition)))
  )

(defthm is-linear-combination-listp-append
  (implies (and (is-linear-combination-listp x exts)
                (is-linear-combination-listp y exts))
           (is-linear-combination-listp (append x y) exts)))

(defthm is-linear-combination-listp-scale-prods
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p k exts)
                (is-linear-combination-listp x exts))
           (is-linear-combination-listp (scale-prods k x) exts))
  :hints (("Subgoal *1/2"
           :use ((:instance is-linear-combination-p-is-closed-multiplication
                            (x k)
                            (y (first x))))
           :in-theory (disable is-linear-combination-p-is-closed-multiplication)))
  )

(defthm is-linear-combination-listp-all-products-lemma-1
  (is-linear-combination-listp '(1) nil)
  :hints (("Goal"
           :expand ((is-linear-combination-listp '(1) nil))
           :in-theory (disable (is-linear-combination-listp))
           )))

(defthm is-linear-combination-listp-cdr-forward
  (implies (and (consp exts)
                (is-linear-combination-listp l (cdr exts)))
           (is-linear-combination-listp l exts))
  :hints (("Goal"
           :do-not-induct t
           :induct (is-linear-combination-listp l exts))
          ("Subgoal *1/2"
           :use ((:instance is-linear-combination-is-tower
                            (x (car l))
                            (exts exts)))
           :in-theory (disable is-linear-combination-is-tower)
           )
          )
  :rule-classes :forward-chaining)


(defthm is-linear-combination-listp-all-products
  (implies (quadratic-extensions-p exts)
           (is-linear-combination-listp (all-products exts) exts))
  :hints (("Goal"
           :do-not-induct t
           :induct (all-products exts)
           :in-theory (disable quadratic-extensions-p))))


(defthmd is-linear-combination-eval-linear-combination-lemma-2
  (implies (and (is-linear-combination-listp coords exts)
                (quadratic-extensions-p exts))
           (is-linear-combination-p (eval-linear-combination coords (all-products exts))
                                    exts))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance is-linear-combination-eval-linear-combination-lemma-1
                            (l (all-products exts))))
           :in-theory (disable is-linear-combination-eval-linear-combination-lemma-1))))


(defthmd is-linear-combination-eval-linear-combination
  (implies (and (rational-listp coords)
                (quadratic-extensions-p exts))
           (is-linear-combination-p (eval-linear-combination coords (all-products exts))
                                    exts))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance is-linear-combination-eval-linear-combination-lemma-2)
                 (:instance rational-listp-is-linear-combination-listp
                            (l coords)
                            (exts exts)))
           :in-theory (disable is-linear-combination-eval-linear-combination-lemma-2
                               rational-listp-is-linear-combination-listp))))


(defthm subfield-extension-parts-1
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts))
           (equal (+ (subfield-part x exts)
                     (* (extension-part x exts) (first exts)))
                  x)))

(defthm subfield-extension-parts-2
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts))
           (is-linear-combination-p (subfield-part x exts) (rest exts)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance is-linear-combination-eval-linear-combination
                            (coords (take (expt 2 (len (cdr exts)))
                                          (is-linear-combination-p-witness x exts)))
                            (exts (cdr exts))))
           :in-theory (disable is-linear-combination-eval-linear-combination)
           )
          )
  )

(defthm subfield-extension-parts-3
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts))
           (is-linear-combination-p (extension-part x exts) (rest exts)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance is-linear-combination-eval-linear-combination
                            (coords (nthcdr (expt 2 (len (cdr exts)))
                                            (is-linear-combination-p-witness x exts)))
                            (exts (cdr exts))))
           :in-theory (disable is-linear-combination-eval-linear-combination)
           )
          )
  )

(defthm numberp-subfield-extension-parts
  (and (acl2-numberp (subfield-part x exts))
       (acl2-numberp (extension-part x exts))))

(in-theory (disable subfield-part (subfield-part) extension-part (extension-part)))

(defun qef-conjugate (x exts)
  (- (subfield-part x exts) (* (extension-part x exts) (first exts))))

(defthm car-exts-not-zero
  (implies (and (consp exts)
                (quadratic-extensions-p exts))
           (not (equal (car exts) 0)))
  :hints (("Goal"
           :use ((:instance rational-is-linear-combination
                            (x 0)
                            (exts exts)))
           :in-theory (disable rational-is-linear-combination))))

(defthm qef-conjugate-same-as-x
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (equal (qef-conjugate x exts) x))
           (equal (extension-part x exts) 0))
  :hints (("Goal"
           :use ((:instance subfield-extension-parts-1)
                 (:instance car-exts-not-zero))
           :in-theory (disable quadratic-extensions-p
                               is-linear-combination-p
                               subfield-extension-parts-1
                               car-exts-not-zero))
          ("Subgoal 1"
           :cases ((consp exts))
           :in-theory (enable extension-part))
          )
  :rule-classes nil)

(defthmd conjugate-zero-lemma-1
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (not (equal (extension-part x exts) 0))
                (is-linear-combination-p (/ (extension-part x exts)) (rest exts)))
           (not (equal (qef-conjugate x exts) 0)))
  :hints (("Goal"
           :use ((:instance (:theorem (implies (and (acl2-numberp a)
                                                    (acl2-numberp b)
                                                    (acl2-numberp c)
                                                    (not (equal b 0))
                                                    (equal a (* b c)))
                                               (equal c (/ a b))))
                            (a (subfield-part x exts))
                            (b (extension-part x exts))
                            (c (car exts)))
                 (:instance is-linear-combination-p-is-closed-multiplication
                            (x (subfield-part x exts))
                            (y (/ (extension-part x exts)))
                            (exts (rest exts))))
           :in-theory (disable is-linear-combination-p)))
  )

(defthm conjugate-zero-lemma-2
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (equal (extension-part x exts) 0)
                (equal (qef-conjugate x exts) 0))
           (equal x 0))
  :hints (("Goal"
           :use ((:instance subfield-extension-parts-1))
           :in-theory (disable subfield-extension-parts-1)))
  :rule-classes nil)


(defthmd conjugate-zero-lemma
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p (/ (extension-part x exts)) (rest exts))
                (not (equal x 0)))
           (not (equal (qef-conjugate x exts) 0)))
  :hints (("Goal"
           :use ((:instance conjugate-zero-lemma-1)
                 (:instance conjugate-zero-lemma-2))
           :in-theory (disable qef-conjugate quadratic-extensions-p is-linear-combination-p))))

(defthmd *-x-conjugate-zero
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p (/ (extension-part x exts)) (rest exts))
                (not (equal x 0)))
           (not (equal (* x (qef-conjugate x exts)) 0)))
  :hints (("Goal"
           :use ((:instance conjugate-zero-lemma))
           :in-theory (disable ;x-times-qef-conjugate
                       qef-conjugate
                       quadratic-extensions-p
                       is-linear-combination-p))))


(defthm x-times-qef-conjugate
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts))
           (equal (* x (qef-conjugate x exts))
                  (- (expt (subfield-part x exts) 2)
                     (* (expt (extension-part x exts) 2)
                        (expt (first exts) 2)))))
  :hints (("Goal"
           :use ((:instance subfield-extension-parts-1))
           :in-theory (disable quadratic-extensions-p
                               is-linear-combination-p
                               subfield-extension-parts-1)))
  )

(defthm is-linear-combination-p-has-multiplicative-inverse-lemma-1
  (implies (and (not (consp exts))
                (is-linear-combination-p x exts)
                (not (equal x 0)))
           (is-linear-combination-p (/ x) exts))
  :hints (("Goal"
           :use ((:instance rational-is-linear-combination
                            (x (/ x))
                            (exts nil)))))
  )

(defthm is-linear-combination-p-has-multiplicative-inverse-lemma-2
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p (/ (extension-part x exts)) (rest exts))
                (not (equal x 0)))
           (equal (/ (qef-conjugate x exts) (* x (qef-conjugate x exts)))
                  (/ x)))
  :hints (("Goal"
           :use ((:instance conjugate-zero-lemma))
           :in-theory (disable qef-conjugate
                               quadratic-extensions-p
                               is-linear-combination-p)))
  :rule-classes nil)

(defthm is-linear-combination-p-has-multiplicative-inverse-lemma-3
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p (/ (extension-part x exts)) (rest exts))
                (acl2-numberp z)
                (not (equal x 0)))
           (equal (/ (qef-conjugate x exts) z)
                  (+ (/ (subfield-part x exts) z)
                     (* (/ (- (extension-part x exts)) z)
                        (first exts)))))
  :hints (("Goal"
           :in-theory (disable quadratic-extensions-p
                               is-linear-combination-p)))
  :rule-classes nil)

(defthm is-linear-combination-p-has-multiplicative-inverse-lemma-4
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p (/ (extension-part x exts)) (rest exts))
                (not (equal x 0)))
           (equal (+ (/ (subfield-part x exts)
                        (* x (qef-conjugate x exts)))
                     (* (/ (- (extension-part x exts))
                           (* x (qef-conjugate x exts)))
                        (first exts)))
                  (/ x)))
  :hints (("Goal"
           :use ((:instance is-linear-combination-p-has-multiplicative-inverse-lemma-2)
                 (:instance is-linear-combination-p-has-multiplicative-inverse-lemma-3
                            (x x)
                            (exts exts)
                            (z (* x (qef-conjugate x exts))))
                 )
           :in-theory (disable quadratic-extensions-p
                               is-linear-combination-p)))
  :rule-classes nil)

(defthm *-qef-conjugate-in-subfield-lemma-1
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts))
           (is-linear-combination-p (expt (subfield-part x exts) 2) (rest exts)))
  :hints (("Goal"
           :use ((:instance subfield-extension-parts-2)
                 (:instance is-linear-combination-p-is-closed-multiplication
                            (x (subfield-part x exts))
                            (y (subfield-part x exts))
                            (exts (rest exts)))
                 )
           :in-theory (disable subfield-extension-parts-2
                               quadratic-extensions-p
                               is-linear-combination-p)
           )
          )
  :rule-classes nil)

(defthm *-qef-conjugate-in-subfield-lemma-2
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts))
           (is-linear-combination-p (expt (extension-part x exts) 2) (rest exts)))
  :hints (("Goal"
           :use ((:instance subfield-extension-parts-3)
                 (:instance is-linear-combination-p-is-closed-multiplication
                            (x (extension-part x exts))
                            (y (extension-part x exts))
                            (exts (rest exts)))
                 )
           :in-theory (disable subfield-extension-parts-2
                               quadratic-extensions-p
                               is-linear-combination-p)
           )
          )
  :rule-classes nil)

(defthm *-qef-conjugate-in-subfield-lemma-3
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts))
           (is-linear-combination-p (* (expt (extension-part x exts) 2)
                                       (expt (first exts) 2))
                                    (rest exts)))
  :hints (("Goal"
           :use ((:instance *-qef-conjugate-in-subfield-lemma-2)
                 (:instance is-linear-combination-p-is-closed-multiplication
                            (x (expt (extension-part x exts) 2))
                            (y (expt (first exts) 2))
                            (exts (rest exts)))
                 )
           :in-theory (disable is-linear-combination-p)
           )
          )
  :rule-classes nil)

(defthm *-qef-conjugate-in-subfield-lemma-4
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts))
           (is-linear-combination-p (- (* (expt (extension-part x exts) 2)
                                          (expt (first exts) 2)))
                                    (rest exts)))
  :hints (("Goal"
           :use ((:instance *-qef-conjugate-in-subfield-lemma-3)
                 (:instance is-linear-combination-p-has-additive-inverse
                            (x (* (expt (extension-part x exts) 2)
                                  (expt (first exts) 2)))
                            (exts (rest exts)))
                 )
           :in-theory (disable quadratic-extensions-p
                               is-linear-combination-p)
           )
          )
  :rule-classes nil)

(defthm *-qef-conjugate-in-subfield-lemma-5
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts))
           (is-linear-combination-p (- (expt (subfield-part x exts) 2)
                                       (* (expt (extension-part x exts) 2)
                                          (expt (first exts) 2)))
                                    (rest exts)))
  :hints (("Goal"
           :use ((:instance *-qef-conjugate-in-subfield-lemma-1)
                 (:instance *-qef-conjugate-in-subfield-lemma-4)
                 (:instance is-linear-combination-p-is-closed-addition
                            (x (expt (subfield-part x exts) 2))
                            (y (- (* (expt (extension-part x exts) 2)
                                     (expt (first exts) 2))))
                            (exts (rest exts)))
                 )
           :in-theory (disable quadratic-extensions-p
                               is-linear-combination-p)
           )
          )
  :rule-classes nil)

(defthm *-qef-conjugate-in-subfield
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts))
           (is-linear-combination-p (* x (qef-conjugate x exts))
                                    (rest exts)))
  :hints (("Goal"
           :use ((:instance x-times-qef-conjugate)
                 (:instance *-qef-conjugate-in-subfield-lemma-5)
                 )
           :in-theory nil
           )
          )
  :rule-classes nil)


(defthm is-linear-combination-p-has-multiplicative-inverse-lemma-5
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p (/ (extension-part x exts)) (rest exts))
                (is-linear-combination-p (/ (* x (qef-conjugate x exts))) (rest exts))
                (not (equal x 0)))
           (is-linear-combination-p (/ (subfield-part x exts)
                                       (* x (qef-conjugate x exts)))
                                    (rest exts)))
  :hints (("Goal"
           :use ((:instance subfield-extension-parts-2)
                 (:instance is-linear-combination-p-is-closed-multiplication
                            (x (subfield-part x exts))
                            (y (/ (* x (qef-conjugate x exts))))
                            (exts (rest exts)))
                 )
           :in-theory (disable quadratic-extensions-p
                               is-linear-combination-p
                               qef-conjugate)))
  :rule-classes nil)

(defthm is-linear-combination-p-has-multiplicative-inverse-lemma-6
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts))
           (is-linear-combination-p (- (extension-part x exts))
                                    (rest exts)))
  :hints (("Goal"
           :use ((:instance subfield-extension-parts-3)
                 (:instance is-linear-combination-p-has-additive-inverse
                            (x (extension-part x exts))
                            (exts (rest exts)))
                 )
           :in-theory (disable quadratic-extensions-p
                               is-linear-combination-p
                               subfield-extension-parts-3)
           )
          )
  :rule-classes nil)

(defthm is-linear-combination-p-has-multiplicative-inverse-lemma-7
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p (/ (extension-part x exts)) (rest exts))
                (is-linear-combination-p (/ (* x (qef-conjugate x exts))) (rest exts))
                (not (equal x 0)))
           (is-linear-combination-p (/ (- (extension-part x exts))
                                       (* x (qef-conjugate x exts)))
                                    (rest exts)))
  :hints (("Goal"
           :use ((:instance is-linear-combination-p-has-multiplicative-inverse-lemma-6)
                 (:instance is-linear-combination-p-is-closed-multiplication
                            (x (- (extension-part x exts)))
                            (y (/ (* x (qef-conjugate x exts))))
                            (exts (rest exts)))
                 )
           :in-theory (disable quadratic-extensions-p
                               is-linear-combination-p
                               qef-conjugate)))
  :rule-classes nil)

(defthm subfield-extension-sum-is-in-linear-combination
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p alpha (rest exts))
                (is-linear-combination-p beta (rest exts)))
           (is-linear-combination-p (+ alpha (* beta (car exts)))
                                    exts))
  :hints (("Goal"
           :use ((:instance is-linear-combination-p-is-closed-multiplication
                            (x beta)
                            (y (car exts))
                            (exts exts))
                 (:instance is-linear-combination-p-is-closed-addition
                            (x alpha)
                            (y (* beta (car exts)))
                            (exts exts))
                 (:instance is-linear-combination-is-tower
                            (x alpha)
                            (exts exts))
                 (:instance is-linear-combination-is-tower
                            (x beta)
                            (exts exts))
                 )
           :in-theory (disable quadratic-extensions-p
                               is-linear-combination-p
                               is-linear-combination-p-is-closed-addition
                               is-linear-combination-p-is-closed-multiplication
                               is-linear-combination-is-tower)))
  )

(defthm is-linear-combination-p-has-multiplicative-inverse-lemma-8
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p (/ (extension-part x exts)) (rest exts))
                (is-linear-combination-p (/ (* x (qef-conjugate x exts))) (rest exts))
                (not (equal x 0)))
           (is-linear-combination-p (+ (/ (subfield-part x exts)
                                          (* x (qef-conjugate x exts)))
                                       (* (/ (- (extension-part x exts))
                                             (* x (qef-conjugate x exts)))
                                          (first exts)))
                                    exts))
  :hints (("Goal"
           :use ((:instance subfield-extension-sum-is-in-linear-combination
                            (alpha (/ (subfield-part x exts)
                                      (* x (qef-conjugate x exts))))
                            (beta (/ (- (extension-part x exts))
                                     (* x (qef-conjugate x exts))))
                            (exts exts))
                 (:instance is-linear-combination-p-has-multiplicative-inverse-lemma-5)
                 (:instance is-linear-combination-p-has-multiplicative-inverse-lemma-7))
           :in-theory (disable quadratic-extensions-p
                               is-linear-combination-p
                               subfield-extension-sum-is-in-linear-combination)))
  :rule-classes nil)

(defthm is-linear-combination-p-has-multiplicative-inverse-lemma
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p (/ (extension-part x exts)) (rest exts))
                (is-linear-combination-p (/ (* x (qef-conjugate x exts))) (rest exts))
                (not (equal x 0)))
           (is-linear-combination-p (/ x) exts))
  :hints (("Goal"
           :use ((:instance is-linear-combination-p-has-multiplicative-inverse-lemma-4)
                 (:instance is-linear-combination-p-has-multiplicative-inverse-lemma-8))
           :in-theory nil))
  :rule-classes nil)

(defun is-linear-combination-p-has-multiplicative-inverse-hint-2 (x exts)
  (if (consp exts)
      (append (is-linear-combination-p-has-multiplicative-inverse-hint-2 (extension-part x exts) (rest exts))
              (is-linear-combination-p-has-multiplicative-inverse-hint-2 (* x (qef-conjugate x exts)) (rest exts)))
    (list x exts)))

(defthm is-linear-combination-p-has-multiplicative-inverse
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (not (equal x 0)))
           (is-linear-combination-p (/ x) exts))
  :hints (("Goal"
           :do-not-induct t
           :induct (is-linear-combination-p-has-multiplicative-inverse-hint-2 x exts)
           )
          ("Subgoal *1/1"
           :use ((:instance is-linear-combination-p-has-multiplicative-inverse-lemma)
                 (:instance *-qef-conjugate-in-subfield))
           :in-theory (disable quadratic-extensions-p
                               is-linear-combination-p
                               qef-conjugate
                               x-times-qef-conjugate))
          )
  )

;;-------------
;; Now some facts about conjugates

(defthmd zero-extension-part-means-subfield
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (equal (extension-part x exts) 0))
           (is-linear-combination-p x (cdr exts)))
  :hints (("Goal"
           :use ((:instance subfield-extension-parts-1)
                 (:instance subfield-extension-parts-2))
           :in-theory (disable subfield-extension-parts-1
                               subfield-extension-parts-2)))
  )

(defthmd subfield-means-zero-extension-part-lemma-1
  (implies (and (number-field-p alpha)
                (number-field-p beta)
                (not (equal beta 0))
                (number-field-p x)
                (acl2-numberp gamma)
                (equal (+ alpha (* beta gamma))
                       x))
           (equal (/ (- x alpha) beta)
                  gamma)))

(defthmd subfield-means-zero-extension-part-lemma-2
  (implies (and (number-field-p alpha)
                (number-field-p beta)
                (not (equal beta 0))
                (number-field-p x)
                (acl2-numberp gamma)
                (equal (+ alpha (* beta gamma))
                       x))
           (number-field-p (- alpha)))
  :hints (("Goal"
           :by (:instance number-field-has-additive-inverse
                          (x alpha)))))

(defthmd subfield-means-zero-extension-part-lemma-3
  (implies (and (number-field-p alpha)
                (number-field-p beta)
                (not (equal beta 0))
                (number-field-p x)
                (acl2-numberp gamma)
                (equal (+ alpha (* beta gamma))
                       x))
           (number-field-p (- x alpha)))
  :hints (("Goal"
           :use ((:instance number-field-is-closed-addition
                            (x x)
                            (y (- alpha)))
                 (:instance subfield-means-zero-extension-part-lemma-2)))))

(defthmd subfield-means-zero-extension-part-lemma-4
  (implies (and (number-field-p alpha)
                (number-field-p beta)
                (not (equal beta 0))
                (number-field-p x)
                (acl2-numberp gamma)
                (equal (+ alpha (* beta gamma))
                       x))
           (number-field-p (/ beta)))
  :hints (("Goal"
           :by (:instance number-field-has-multiplicative-inverse
                          (x beta)))))

(defthmd subfield-means-zero-extension-part-lemma-5
  (implies (and (number-field-p alpha)
                (number-field-p beta)
                (not (equal beta 0))
                (number-field-p x)
                (acl2-numberp gamma)
                (equal (+ alpha (* beta gamma))
                       x))
           (number-field-p (/ (- x alpha)
                              beta)))
  :hints (("Goal"
           :use ((:instance number-field-is-closed-multiplication
                            (x (- x alpha))
                            (y (/ beta)))
                 (:instance subfield-means-zero-extension-part-lemma-3)
                 (:instance subfield-means-zero-extension-part-lemma-4)))))

(defthmd subfield-means-zero-extension-part-lemma
  (implies (and (number-field-p alpha)
                (number-field-p beta)
                (not (equal beta 0))
                (number-field-p x)
                (acl2-numberp gamma)
                (equal (+ alpha (* beta gamma))
                       x))
           (number-field-p gamma))
  :hints (("Goal"
           :use ((:instance subfield-means-zero-extension-part-lemma-1)
                 (:instance subfield-means-zero-extension-part-lemma-5)))))

(defthmd subfield-means-zero-extension-part-contradiction-lemma
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x (rest exts))
                (not (equal (extension-part x exts) 0))
                (acl2-numberp x))
           (is-linear-combination-p (car exts) (rest exts)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance
                  (:functional-instance subfield-means-zero-extension-part-lemma
                                        (number-field-p
                                         (lambda (x)
                                           (is-linear-combination-p
                                            x
                                            (if (quadratic-extensions-p (rest exts))
                                                (rest exts)
                                              nil)))))
                  (alpha (subfield-part x exts))
                  (beta  (extension-part x exts))
                  (gamma (car exts))
                  (x x))
                 (:instance subfield-extension-parts-1))
           :in-theory (disable is-linear-combination-p
                               quadratic-extensions-p
                               subfield-extension-parts-1)
           )
          ))                  


(defthmd subfield-means-zero-extension-part
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x (cdr exts)))
           (equal (extension-part x exts) 0))
  :hints (("Goal"
           :use ((:instance subfield-means-zero-extension-part-contradiction-lemma))
           :in-theory (disable is-linear-combination-p)))
  )

(defthmd subfield-extension-parts-of-zero
  (implies (and (consp exts)
                (quadratic-extensions-p exts))
           (and (equal (subfield-part 0 exts) 0)
                (equal (extension-part 0 exts) 0)))
  :hints (("Goal"
           :use ((:instance subfield-means-zero-extension-part
                            (x 0))
                 (:instance subfield-extension-parts-1
                            (x 0)
                            (exts exts)))
           :in-theory (disable is-linear-combination-p
                               subfield-extension-parts-1
                               quadratic-extensions-p)))
  )

(defthm subfield-extension-parts-unique-lemma-1
  (implies (and (number-field-p alpha)
                (number-field-p beta)
                (not (number-field-p gamma))
                (acl2-numberp gamma)
                (equal (+ alpha (* beta gamma)) 0))
           (equal beta 0))
  :hints (("Goal"
           :use ((:instance subfield-means-zero-extension-part-lemma
                            (x 0)))))
  :rule-classes nil)

(defthm subfield-extension-parts-unique-lemma-2
  (implies (and (number-field-p alpha)
                (number-field-p beta)
                (not (number-field-p gamma))
                (acl2-numberp gamma)
                (equal (+ alpha (* beta gamma)) 0))
           (equal alpha 0))
  :hints (("Goal"
           :use ((:instance subfield-extension-parts-unique-lemma-1))))
  :rule-classes nil)

(defthmd subfield-extension-parts-unique-lemma-3
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p alpha (cdr exts))
                (is-linear-combination-p beta (cdr exts))
                (equal (+ alpha (* beta (car exts))) x))
           (equal (+ (- (subfield-part x exts) alpha)
                     (* (- (extension-part x exts) beta)
                        (car exts)))
                  0))
  :hints (("Goal"
           :use ((:instance subfield-extension-parts-1))
           :in-theory (disable is-linear-combination-p
                               subfield-extension-parts-1
                               quadratic-extensions-p)))
  )

(defthmd subfield-extension-parts-unique
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p alpha (cdr exts))
                (is-linear-combination-p beta (cdr exts))
                (equal (+ alpha (* beta (car exts))) x))
           (and (equal (subfield-part x exts) alpha)
                (equal (extension-part x exts) beta)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance
                  (:functional-instance subfield-extension-parts-unique-lemma-1
                                        (number-field-p
                                         (lambda (x)
                                           (is-linear-combination-p
                                            x
                                            (if (quadratic-extensions-p (rest exts))
                                                (rest exts)
                                              nil)))))                                        
                  (alpha (+ (SUBFIELD-PART X EXTS) (- ALPHA)))
                  (beta (+ (EXTENSION-PART X EXTS) (- BETA)))
                  (gamma (car exts)))
                 (:instance
                  (:functional-instance subfield-extension-parts-unique-lemma-2
                                        (number-field-p
                                         (lambda (x)
                                           (is-linear-combination-p
                                            x
                                            (if (quadratic-extensions-p (rest exts))
                                                (rest exts)
                                              nil)))))                                        
                  (alpha (+ (SUBFIELD-PART X EXTS) (- ALPHA)))
                  (beta (+ (EXTENSION-PART X EXTS) (- BETA)))
                  (gamma (car exts)))
                 (:instance subfield-extension-parts-unique-lemma-3)
                 (:instance subfield-extension-parts-2
                            (x (+ ALPHA (* BETA (CAR EXTS)))))
                 (:instance subfield-extension-parts-3
                            (x (+ ALPHA (* BETA (CAR EXTS))))))
           :in-theory (disable is-linear-combination-p
                               subfield-extension-parts-2
                               subfield-extension-parts-3)))
  )

(defthm subfield-of-not-consp-exts
  (implies (not (consp exts))
           (equal (subfield-part x exts) (fix x)))
  :hints (("Goal"
           :expand ((subfield-part x exts)))))

(defthm extension-of-not-consp-exts
  (implies (not (consp exts))
           (equal (extension-part x exts) 0))
  :hints (("Goal"
           :expand ((extension-part x exts)))))

(defthm subfield-part-of-sum
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p y exts))
           (equal (subfield-part (+ x y) exts)
                  (+ (subfield-part x exts)
                     (subfield-part y exts))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance subfield-extension-parts-unique
                            (alpha (+ (subfield-part x exts)
                                      (subfield-part y exts)))
                            (beta (+ (extension-part x exts)
                                     (extension-part y exts)))
                            (x (+ x y))
                            (exts exts))
                 (:instance subfield-extension-parts-1
                            (x x)
                            (exts exts))
                 (:instance subfield-extension-parts-1
                            (x y)
                            (exts exts))
                 )
           :in-theory (disable is-linear-combination-p
                               quadratic-extensions-p
                               subfield-extension-parts-1))))

(defthm extension-part-of-sum
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p y exts))
           (equal (extension-part (+ x y) exts)
                  (+ (extension-part x exts)
                     (extension-part y exts))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance subfield-extension-parts-unique
                            (alpha (+ (subfield-part x exts)
                                      (subfield-part y exts)))
                            (beta (+ (extension-part x exts)
                                     (extension-part y exts)))
                            (x (+ x y))
                            (exts exts))
                 (:instance subfield-extension-parts-1
                            (x x)
                            (exts exts))
                 (:instance subfield-extension-parts-1
                            (x y)
                            (exts exts))
                 )
           :in-theory (disable is-linear-combination-p
                               quadratic-extensions-p
                               subfield-extension-parts-1))))


(defthm qef-conjugate-of-sum
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p y exts))
           (equal (qef-conjugate (+ x y) exts)
                  (+ (qef-conjugate x exts)
                     (qef-conjugate y exts)))))

(defthm subfield-part-of-negation
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts))
           (equal (subfield-part (- x) exts)
                  (- (subfield-part x exts))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance subfield-extension-parts-unique
                            (alpha (- (subfield-part x exts)))
                            (beta (- (extension-part x exts)))
                            (x (- x))
                            (exts exts))
                 (:instance subfield-extension-parts-1
                            (x x)
                            (exts exts))
                 )
           :in-theory (disable is-linear-combination-p
                               quadratic-extensions-p
                               subfield-extension-parts-1))))

(defthm extension-part-of-negation
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts))
           (equal (extension-part (- x) exts)
                  (- (extension-part x exts))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance subfield-extension-parts-unique
                            (alpha (- (subfield-part x exts)))
                            (beta (- (extension-part x exts)))
                            (x (- x))
                            (exts exts))
                 (:instance subfield-extension-parts-1
                            (x x)
                            (exts exts))
                 )
           :in-theory (disable is-linear-combination-p
                               quadratic-extensions-p
                               subfield-extension-parts-1))))

(defthm qef-conjugate-of-negation
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts))
           (equal (qef-conjugate (- x) exts)
                  (- (qef-conjugate x exts)))))


(defthm subfield-extension-part-of-product-lemma-1
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p y exts))
           (equal (* x y)
                  (+ (+ (* (subfield-part x exts)
                           (subfield-part y exts))
                        (* (expt (car exts) 2)
                           (extension-part x exts)
                           (extension-part y exts)))
                     (* (car exts)
                        (+ (* (subfield-part x exts)
                              (extension-part y exts))
                           (* (subfield-part y exts)
                              (extension-part x exts)))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance subfield-extension-parts-1
                            (x x)
                            (exts exts))
                 (:instance subfield-extension-parts-1
                            (x y)
                            (exts exts)))
           :in-theory (disable is-linear-combination-p
                               quadratic-extensions-p
                               subfield-extension-parts-1)))
  :rule-classes nil)

(defthmd subfield-part-of-product-lemma-1
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p y exts))
           (is-linear-combination-p (* (subfield-part x exts)
                                       (subfield-part y exts))
                                    (cdr exts)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance is-linear-combination-p-is-closed-multiplication
                            (x (subfield-part x exts))
                            (y (subfield-part y exts))
                            (exts (cdr exts)))
                 (:instance subfield-extension-parts-2
                            (x x)
                            (exts exts))
                 (:instance subfield-extension-parts-2
                            (x y)
                            (exts exts)))
           :in-theory  (disable is-linear-combination-p
                                is-linear-combination-p-is-closed-multiplication
                                subfield-extension-parts-2))))

(defthmd subfield-part-of-product-lemma-2
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p y exts))
           (is-linear-combination-p (* (extension-part x exts)
                                       (extension-part y exts))
                                    (cdr exts)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance is-linear-combination-p-is-closed-multiplication
                            (x (extension-part x exts))
                            (y (extension-part y exts))
                            (exts (cdr exts)))
                 (:instance subfield-extension-parts-3
                            (x x)
                            (exts exts))
                 (:instance subfield-extension-parts-3
                            (x y)
                            (exts exts)))
           :in-theory  (disable is-linear-combination-p
                                is-linear-combination-p-is-closed-multiplication
                                subfield-extension-parts-3))))

(defthmd subfield-part-of-product-lemma-3
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p y exts))
           (is-linear-combination-p (* (expt (car exts) 2)
                                       (extension-part x exts)
                                       (extension-part y exts))
                                    (cdr exts)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance is-linear-combination-p-is-closed-multiplication
                            (x (expt (car exts) 2))
                            (y (* (extension-part x exts)
                                  (extension-part y exts)))
                            (exts (cdr exts)))
                 (:instance subfield-part-of-product-lemma-2))
           :in-theory  (disable is-linear-combination-p
                                is-linear-combination-p-is-closed-multiplication))))

(defthmd subfield-part-of-product-lemma-4
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p y exts))
           (is-linear-combination-p (+ (* (subfield-part x exts)
                                          (subfield-part y exts))
                                       (* (expt (car exts) 2)
                                          (extension-part x exts)
                                          (extension-part y exts)))
                                    (cdr exts)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance is-linear-combination-p-is-closed-addition
                            (x (* (subfield-part x exts)
                                  (subfield-part y exts)))
                            (y (* (expt (car exts) 2)
                                  (extension-part x exts)
                                  (extension-part y exts)))
                            (exts (cdr exts)))
                 (:instance subfield-part-of-product-lemma-1)
                 (:instance subfield-part-of-product-lemma-3))
           :in-theory  (disable is-linear-combination-p
                                is-linear-combination-p-is-closed-addition))))


(defthm subfield-part-of-product
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p y exts))
           (equal (subfield-part (* x y) exts)
                  (+ (* (subfield-part x exts)
                        (subfield-part y exts))
                     (* (expt (car exts) 2)
                        (extension-part x exts)
                        (extension-part y exts)))))
  :hints (("Goal"
           :do-not-induct t
           :cases ((consp exts))
           :use ((:instance subfield-extension-parts-unique
                            (alpha (+ (* (subfield-part x exts)
                                         (subfield-part y exts))
                                      (* (expt (car exts) 2)
                                         (extension-part x exts)
                                         (extension-part y exts))))
                            (beta (+ (* (subfield-part x exts)
                                        (extension-part y exts))
                                     (* (subfield-part y exts)
                                        (extension-part x exts))))
                            (x (* x y))
                            (exts exts))
                 (:instance subfield-extension-part-of-product-lemma-1)
                 (:instance subfield-part-of-product-lemma-4)
                 )
           :in-theory (disable is-linear-combination-p
                               quadratic-extensions-p))))

(defthmd extension-part-of-product-lemma-1
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p y exts))
           (is-linear-combination-p (* (subfield-part x exts)
                                       (extension-part y exts))
                                    (cdr exts)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance is-linear-combination-p-is-closed-multiplication
                            (x (subfield-part x exts))
                            (y (extension-part y exts))
                            (exts (cdr exts)))
                 (:instance subfield-extension-parts-2
                            (x x)
                            (exts exts))
                 (:instance subfield-extension-parts-3
                            (x y)
                            (exts exts)))
           :in-theory  (disable is-linear-combination-p
                                is-linear-combination-p-is-closed-multiplication
                                subfield-extension-parts-2
                                subfield-extension-parts-3))))

(defthmd extension-part-of-product-lemma-2
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p y exts))
           (is-linear-combination-p (* (extension-part x exts)
                                       (subfield-part y exts))
                                    (cdr exts)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance extension-part-of-product-lemma-1
                            (x y)
                            (y x)
                            (exts exts)))
           :in-theory  (disable is-linear-combination-p
                                quadratic-extensions-p))))


(defthmd extension-part-of-product-lemma-3
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p y exts))
           (is-linear-combination-p (+ (* (subfield-part x exts)
                                          (extension-part y exts))
                                       (* (extension-part x exts)
                                          (subfield-part y exts)))
                                    (cdr exts)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance is-linear-combination-p-is-closed-addition
                            (x (* (subfield-part x exts)
                                  (extension-part y exts)))
                            (y (* (extension-part x exts)
                                  (subfield-part y exts)))
                            (exts (cdr exts)))
                 (:instance extension-part-of-product-lemma-1)
                 (:instance extension-part-of-product-lemma-2))
           :in-theory  (disable is-linear-combination-p
                                is-linear-combination-p-is-closed-addition))))

(defthm extension-part-of-product
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p y exts))
           (equal (extension-part (* x y) exts)
                  (+ (* (subfield-part x exts)
                        (extension-part y exts))
                     (* (extension-part x exts)
                        (subfield-part y exts)))))
  :hints (("Goal"
           :do-not-induct t
           :cases ((consp exts))
           :use ((:instance subfield-extension-parts-unique
                            (alpha (+ (* (subfield-part x exts)
                                         (subfield-part y exts))
                                      (* (expt (car exts) 2)
                                         (extension-part x exts)
                                         (extension-part y exts))))
                            (beta (+ (* (subfield-part x exts)
                                        (extension-part y exts))
                                     (* (subfield-part y exts)
                                        (extension-part x exts))))
                            (x (* x y))
                            (exts exts))
                 (:instance subfield-extension-part-of-product-lemma-1)
                 (:instance extension-part-of-product-lemma-3)
                 (:instance subfield-part-of-product-lemma-4)
                 )
           :in-theory (disable is-linear-combination-p
                               quadratic-extensions-p))))

(defthm qef-conjugate-of-product
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-p y exts))
           (equal (qef-conjugate (* x y) exts)
                  (* (qef-conjugate x exts)
                     (qef-conjugate y exts)))))





(defthm in-subfield-when-conjugate-x-is-x
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (equal (qef-conjugate x exts) x))
           (is-linear-combination-p x (cdr exts)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance qef-conjugate-same-as-x)
                 (:instance subfield-extension-parts-1)
                 (:instance subfield-extension-parts-2))
           :in-theory (disable subfield-extension-parts-1
                               subfield-extension-parts-2
                               quadratic-extensions-p
                               is-linear-combination-p
                               qef-conjugate))))

(defthm qef-conjugate-of-rational
  (implies (and (rationalp x)
                (quadratic-extensions-p exts))
           (equal (qef-conjugate x exts) x))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rational-is-linear-combination
                            (x x)
                            (exts (cdr exts)))
                 (:instance rational-is-linear-combination
                            (x x)
                            (exts exts))
                 (:instance subfield-extension-parts-1)
                 (:instance subfield-means-zero-extension-part))
           :in-theory (disable rational-is-linear-combination
                               subfield-extension-parts-1
                               subfield-means-zero-extension-part
                               quadratic-extensions-p
                               EVAL-LINEAR-COMBINATION-OF-SINGLE
                               EVAL-LINEAR-COMBINATION)))
  )

(defthm qef-conjugate-of-inverse
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (not (equal x 0)))
           (equal (qef-conjugate (/ x) exts)
                  (/ (qef-conjugate x exts))))
  :hints (("Goal"
           :use ((:instance qef-conjugate-of-product
                            (x x)
                            (y (/ x))
                            (exts exts))
                 )
           :in-theory (disable quadratic-extensions-p
                               is-linear-combination-p
                               qef-conjugate
                               qef-conjugate-of-product)
           )))



(include-book "polylist")

(defthm scale-poly-by-1
  (implies (polynomial-p poly)
           (equal (scale-polynomial poly 1) poly)))

(defthm add-0-to-poly
  (implies (polynomial-p poly)
           (equal (polynomial-+ poly '(0))
                  (if (consp poly)
                      poly
                    '(0)))))

(defmacro real-polynomial-p (poly)
  `(and (polynomial-p ,poly)
        (real-listp ,poly)))


(in-theory (disable CAR-EXTS-NOT-ZERO
                    EXPT-2-LEN-N-MONOTONIC
                    QUADRATIC-EXTENSION-IS-NUMBER-LISTP))

(defthmd product-divide-polynomial-lemma-1
  (implies (and (equal (len poly) 4)
                (acl2-numberp a)
                )
           (equal (divide-polynomial-with-remainder-by-x+a poly a)
                  (list (- (first poly) (* a (- (second poly) (* a (- (third poly) (* a (fourth poly)))))))
                        (- (second poly) (* a (- (third poly) (* a (fourth poly)))))
                        (- (third poly) (* a (fourth poly)))
                        (fourth poly))))
  :hints (("Goal"
           :do-not-induct t
           :expand ((divide-polynomial-with-remainder-by-x+a poly a))
           )
          )
  )

(defthmd product-divide-polynomial-lemma-2
  (implies (and (acl2-numberp x3)
                (acl2-numberp a))
           (equal (polynomial-* (list x1 x2 x3) (list a 1))
                  (list (* x1 a)
                        (+ (* x2 a) x1)
                        (+ (* x3 a) x2)
                        x3)))
  :hints (("Goal"
           :do-not-induct t
           :expand ((polynomial-* (list x1 x2 x3) (list a 1)))
           )
          )
  )

(defthmd product-divide-polynomial-lemma-3
  (implies (and (polynomial-p poly)
                (equal (len poly) 4)
                (acl2-numberp a)
                )
           (equal (polynomial-* (cdr (divide-polynomial-with-remainder-by-x+a poly a))
                                (list a 1))
                  (list (* (- (second poly) (* a (- (third poly) (* a (fourth poly)))))
                           a)
                        (+ (* (- (third poly) (* a (fourth poly)))
                              a)
                           (- (second poly) (* a (- (third poly) (* a (fourth poly))))))
                        (+ (* (fourth poly)
                              a)
                           (- (third poly) (* a (fourth poly))))
                        (fourth poly))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance product-divide-polynomial-lemma-1)
                 (:instance product-divide-polynomial-lemma-2
                            (x1 (- (second poly) (* a (- (third poly) (* a (fourth poly))))))
                            (x2 (- (third poly) (* a (fourth poly))))
                            (x3 (fourth poly))))
           :in-theory (disable polynomial-*
                               divide-polynomial-with-remainder-by-x+a)
           )))

(defthmd product-divide-polynomial-lemma-4
  (implies (and (polynomial-p poly)
                (equal (len poly) 4)
                (acl2-numberp a)
                )
           (equal (polynomial-* (cdr (divide-polynomial-with-remainder-by-x+a poly a))
                                (list a 1))
                  (list (* (- (second poly) (* a (- (third poly) (* a (fourth poly)))))
                           a)
                        (second poly)
                        (third poly)
                        (fourth poly))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance product-divide-polynomial-lemma-3))
           :in-theory (disable polynomial-*
                               divide-polynomial-with-remainder-by-x+a)
           )))

(defthmd product-divide-polynomial-lemma-5
  (implies (and (polynomial-p poly)
                (equal (len poly) 4)
                (acl2-numberp a)
                )
           (equal (polynomial-+
                   (polynomial-* (cdr (divide-polynomial-with-remainder-by-x+a poly a))
                                 (list a 1)
                                 )
                   (list (car (divide-polynomial-with-remainder-by-x+a poly a))))
                  (list (first poly)
                        (second poly)
                        (third poly)
                        (fourth poly))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance product-divide-polynomial-lemma-1)
                 (:instance product-divide-polynomial-lemma-4))
           :in-theory (disable polynomial-*
                               divide-polynomial-with-remainder-by-x+a)
           )))

(defthmd product-divide-polynomial-lemma-6
  (implies (and (polynomial-p poly)
                (equal (len poly) 4)
                (acl2-numberp a)
                )
           (equal (polynomial-+
                   (polynomial-* (cdr (divide-polynomial-with-remainder-by-x+a poly a))
                                 (list a 1)
                                 )
                   (list (car (divide-polynomial-with-remainder-by-x+a poly a))))
                  poly))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance product-divide-polynomial-lemma-5))
           :in-theory (disable polynomial-*
                               divide-polynomial-with-remainder-by-x+a)
           )))

(defthmd product-divide-polynomial-lemma-7
  (implies (and (polynomial-p poly)
                (equal (len poly) 4)
                (acl2-numberp a)
                (equal (eval-polynomial poly a) 0)
                )
           (equal (polynomial-* (cdr (divide-polynomial-with-remainder-by-x+a poly (- a)))
                                (list (- a) 1)
                                )
                  poly))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance product-divide-polynomial-lemma-6
                            (a (- a)))
                 (:instance remainder=0_when-divide-poly-by_x-z=z-is-zero-of-poly
                            (z a)))
           :in-theory (disable polynomial-*
                               divide-polynomial-with-remainder-by-x+a
                               remainder=0_when-divide-poly-by_x-z=z-is-zero-of-poly
                               NORMALIZE-FACTORS-GATHER-EXPONENTS)
           )))

(defthmd product-divide-polynomial-lemma-8
  (implies (and (polynomial-p poly)
                (equal (len poly) 4)
                (acl2-numberp a)
                (equal (eval-polynomial poly a) 0)
                (acl2-numberp b)
                (equal (eval-polynomial poly b) 0)
                (not (equal a b))
                )
           (equal (eval-polynomial (cdr (divide-polynomial-with-remainder-by-x+a poly (- a)))
                                   b)
                  0))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance other-zeros-also-zeros-of-quotient )
                 )
           :in-theory (disable polynomial-*
                               eval-polynomial
                               divide-polynomial-with-remainder-by-x+a
                               other-zeros-also-zeros-of-quotient)
           )))

(defthmd product-divide-polynomial-lemma-9
  (implies (and (polynomial-p poly)
                (equal (len poly) 4)
                (acl2-numberp a)
                (equal (eval-polynomial poly a) 0)
                (acl2-numberp b)
                (equal (eval-polynomial poly b) 0)
                (not (equal a b))
                )
           (equal (len (cdr (divide-polynomial-with-remainder-by-x+a poly (- a))))
                  3))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance len-divide-poly-by-x+a=len
                            (poly poly)
                            (a (- a)))
                 )
           :in-theory (disable polynomial-*
                               eval-polynomial
                               divide-polynomial-with-remainder-by-x+a
                               len-divide-poly-by-x+a=len)
           )))

(defthmd product-divide-polynomial-lemma-10
  (implies (and (equal (len poly) 3)
                (acl2-numberp a)
                )
           (equal (divide-polynomial-with-remainder-by-x+a poly a)
                  (list (- (first poly) (* a (- (second poly) (* a (third poly)))))
                        (- (second poly) (* a (third poly)))
                        (third poly))))
  :hints (("Goal"
           :do-not-induct t
           :expand ((divide-polynomial-with-remainder-by-x+a poly a))
           )
          )
  )

(defthmd product-divide-polynomial-lemma-11
  (implies (and (acl2-numberp x2)
                (acl2-numberp a))
           (equal (polynomial-* (list x1 x2) (list a 1))
                  (list (* x1 a)
                        (+ (* x2 a) x1)
                        x2)))
  :hints (("Goal"
           :do-not-induct t
           :expand ((polynomial-* (list x1 x2) (list a 1)))
           )
          )
  )

(defthmd product-divide-polynomial-lemma-12
  (implies (and (polynomial-p poly)
                (equal (len poly) 3)
                (acl2-numberp a)
                )
           (equal (polynomial-* (cdr (divide-polynomial-with-remainder-by-x+a poly a))
                                (list a 1))
                  (list (* (- (second poly) (* a (third poly)))
                           a)
                        (+ (* (third poly) a)
                           (- (second poly) (* a (third poly))))
                        (third poly))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance product-divide-polynomial-lemma-10)
                 (:instance product-divide-polynomial-lemma-11
                            (x1 (- (second poly) (* a (third poly))))
                            (x2 (third poly))))
           :in-theory (disable polynomial-*
                               divide-polynomial-with-remainder-by-x+a)
           )))

(defthmd product-divide-polynomial-lemma-13
  (implies (and (polynomial-p poly)
                (equal (len poly) 3)
                (acl2-numberp a)
                )
           (equal (polynomial-* (cdr (divide-polynomial-with-remainder-by-x+a poly a))
                                (list a 1))
                  (list (* (- (second poly) (* a (third poly)))
                           a)
                        (second poly)
                        (third poly))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance product-divide-polynomial-lemma-12))
           :in-theory (disable polynomial-*
                               divide-polynomial-with-remainder-by-x+a)
           )))

(defthmd product-divide-polynomial-lemma-14
  (implies (and (polynomial-p poly)
                (equal (len poly) 3)
                (acl2-numberp a)
                )
           (equal (polynomial-+
                   (polynomial-* (cdr (divide-polynomial-with-remainder-by-x+a poly a))
                                 (list a 1)
                                 )
                   (list (car (divide-polynomial-with-remainder-by-x+a poly a))))
                  (list (first poly)
                        (second poly)
                        (third poly))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance product-divide-polynomial-lemma-10)
                 (:instance product-divide-polynomial-lemma-13))
           :in-theory (disable polynomial-*
                               divide-polynomial-with-remainder-by-x+a)
           )))

(defthmd product-divide-polynomial-lemma-15
  (implies (and (polynomial-p poly)
                (equal (len poly) 3)
                (acl2-numberp a)
                )
           (equal (polynomial-+
                   (polynomial-* (cdr (divide-polynomial-with-remainder-by-x+a poly a))
                                 (list a 1)
                                 )
                   (list (car (divide-polynomial-with-remainder-by-x+a poly a))))
                  poly))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance product-divide-polynomial-lemma-14))
           :in-theory (disable polynomial-*
                               divide-polynomial-with-remainder-by-x+a)
           )))

(defthmd product-divide-polynomial-lemma-16
  (implies (and (polynomial-p poly)
                (equal (len poly) 3)
                (acl2-numberp a)
                (equal (eval-polynomial poly a) 0)
                )
           (equal (polynomial-* (cdr (divide-polynomial-with-remainder-by-x+a poly (- a)))
                                (list (- a) 1)
                                )
                  poly))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance product-divide-polynomial-lemma-15
                            (a (- a)))
                 (:instance remainder=0_when-divide-poly-by_x-z=z-is-zero-of-poly
                            (z a)))
           :in-theory (disable polynomial-*
                               divide-polynomial-with-remainder-by-x+a
                               remainder=0_when-divide-poly-by_x-z=z-is-zero-of-poly)
           )))

(defthmd product-divide-polynomial-lemma-17
  (implies (and (polynomial-p poly)
                (equal (len poly) 3)
                (acl2-numberp a)
                (equal (eval-polynomial poly a) 0)
                (acl2-numberp b)
                (equal (eval-polynomial poly b) 0)
                (not (equal a b))
                )
           (equal (eval-polynomial (cdr (divide-polynomial-with-remainder-by-x+a poly (- a)))
                                   b)
                  0))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance other-zeros-also-zeros-of-quotient )
                 )
           :in-theory (disable polynomial-*
                               eval-polynomial
                               divide-polynomial-with-remainder-by-x+a
                               other-zeros-also-zeros-of-quotient)
           )))

(defthmd product-divide-polynomial-lemma-18
  (implies (and (polynomial-p poly)
                (equal (len poly) 3)
                (acl2-numberp a)
                (equal (eval-polynomial poly a) 0)
                (acl2-numberp b)
                (equal (eval-polynomial poly b) 0)
                (not (equal a b))
                )
           (equal (len (cdr (divide-polynomial-with-remainder-by-x+a poly (- a))))
                  2))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance len-divide-poly-by-x+a=len
                            (poly poly)
                            (a (- a)))
                 )
           :in-theory (disable polynomial-*
                               eval-polynomial
                               divide-polynomial-with-remainder-by-x+a
                               len-divide-poly-by-x+a=len)
           )))

(defthmd product-divide-polynomial-lemma-19
  (implies (and (polynomial-p poly)
                (equal (len poly) 4)
                (acl2-numberp a)
                (equal (eval-polynomial poly a) 0)
                (acl2-numberp b)
                (equal (eval-polynomial poly b) 0)
                (not (equal a b))
                )
           (equal (polynomial-*
                   (polynomial-*
                    (cdr (divide-polynomial-with-remainder-by-x+a
                          (cdr (divide-polynomial-with-remainder-by-x+a
                                poly (- a)))
                          (- b)))
                    (list (- b) 1))
                   (list (- a) 1)
                   )
                  poly))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance product-divide-polynomial-lemma-16
                            (poly (cdr (divide-polynomial-with-remainder-by-x+a
                                        poly (- a))))
                            (a b))
                 (:instance product-divide-polynomial-lemma-7)
                 (:instance product-divide-polynomial-lemma-8)
                 (:instance product-divide-polynomial-lemma-9)
                 )
           :in-theory (disable polynomial-*
                               eval-polynomial
                               divide-polynomial-with-remainder-by-x+a
                               len-divide-poly-by-x+a=len
                               real-listp-divide-poly-by-x+a
                               NORMALIZE-FACTORS-GATHER-EXPONENTS)
           )))

(defthmd product-divide-polynomial-lemma-20
  (implies (and (polynomial-p poly)
                (equal (len poly) 4)
                (acl2-numberp a)
                (equal (eval-polynomial poly a) 0)
                (acl2-numberp b)
                (equal (eval-polynomial poly b) 0)
                (not (equal a b))
                )
           (equal (polynomial-*
                   (polynomial-*
                    (cdr (divide-polynomial-with-remainder-by-x+a
                          (list (+ (second poly) (* a (+ (third poly) (* a (fourth poly)))))
                                (+ (third poly) (* a (fourth poly)))
                                (fourth poly))
                          (- b)))
                    (list (- b) 1))
                   (list (- a) 1)
                   )
                  poly))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance product-divide-polynomial-lemma-1
                            (poly poly)
                            (a (- a)))
                 (:instance product-divide-polynomial-lemma-19)
                 (:instance (:theorem
                             (implies (and (polynomial-p poly)
                                           (equal (len poly) 4))
                                      (equal (list (cadr poly)
                                                   (caddr poly)
                                                   (cadddr poly))
                                             (cdr poly)))))
                 )
           :in-theory (disable polynomial-*
                               eval-polynomial
                               divide-polynomial-with-remainder-by-x+a
                               len-divide-poly-by-x+a=len
                               real-listp-divide-poly-by-x+a
                               )
           )
          ))

(defthmd product-divide-polynomial-lemma-21
  (implies (and (polynomial-p poly)
                (equal (len poly) 4)
                (acl2-numberp a)
                (equal (eval-polynomial poly a) 0)
                (acl2-numberp b)
                (equal (eval-polynomial poly b) 0)
                (not (equal a b))
                )
           (equal (polynomial-*
                   (polynomial-*
                    (list (+ (third poly)
                             (* a (fourth poly))
                             (* b (fourth poly)))
                          (fourth poly))
                    (list (- b) 1))
                   (list (- a) 1)
                   )
                  poly))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance product-divide-polynomial-lemma-20)
                 (:instance product-divide-polynomial-lemma-10
                            (poly (list (+ (second poly) (* a (+ (third poly) (* a (fourth poly)))))
                                        (+ (third poly) (* a (fourth poly)))
                                        (fourth poly)))
                            (a (- b)))
                 )
           :in-theory (disable polynomial-*
                               eval-polynomial
                               divide-polynomial-with-remainder-by-x+a
                               len-divide-poly-by-x+a=len
                               real-listp-divide-poly-by-x+a
                               NORMALIZE-FACTORS-GATHER-EXPONENTS)
           )
          ))

(defthmd product-divide-polynomial-lemma-22
  (implies (and (polynomial-p poly)
                (equal (len poly) 4)
                (acl2-numberp a)
                (equal (eval-polynomial poly a) 0)
                (acl2-numberp b)
                (equal (eval-polynomial poly b) 0)
                (not (equal a b))
                )
           (equal (polynomial-*
                   (polynomial-*
                    (list (+ (third poly)
                             (* (fourth poly)
                                (+ a b)))
                          (fourth poly))
                    (list (- b) 1))
                   (list (- a) 1)
                   )
                  poly))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance product-divide-polynomial-lemma-21)
                 )
           :in-theory (disable polynomial-*
                               eval-polynomial
                               divide-polynomial-with-remainder-by-x+a
                               len-divide-poly-by-x+a=len
                               real-listp-divide-poly-by-x+a
                               NORMALIZE-FACTORS-GATHER-EXPONENTS)
           )
          ))

(defthm product-divide-polynomial-lemma-23
  (implies (and (acl2-numberp c1)
                (acl2-numberp c2)
                (acl2-numberp x)
                (not (equal c2 0))
                (equal x (- (/ c1 c2)))
                )
           (equal (eval-polynomial (list c1 c2) x) 0)
           )
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance (:theorem
                             (implies (and (realp x)
                                           (realp y)
                                           (equal (+ x y) 0))
                                      (equal y (- x))))
                            (x c1)
                            (y (* c2 x)))
                 (:instance (:theorem
                             (implies (and (realp x)
                                           (realp y)
                                           (realp z)
                                           (not (equal x 0))
                                           (equal (* x y) z))
                                      (equal y (/ z x))))
                            (x c2)
                            (y x)
                            (z (- c1))))
           )
          )
  :rule-classes nil)

(defthm product-divide-polynomial-lemma-24
  (implies (and (polynomial-p poly1)
                (polynomial-p poly2)
                (polynomial-p poly3)
                (equal (eval-polynomial poly1 x) 0))
           (equal (eval-polynomial (polynomial-*
                                    (polynomial-*
                                     poly1
                                     poly2)
                                    poly3)
                                   x)
                  0))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable eval-polynomial polynomial-*)
           ))
  :rule-classes nil)

(defthmd product-divide-polynomial-lemma-25
  (implies (and (polynomial-p poly)
                (equal (len poly) 4)
                (not (equal (fourth poly) 0))
                (acl2-numberp a)
                (equal (eval-polynomial poly a) 0)
                (acl2-numberp b)
                (equal (eval-polynomial poly b) 0)
                (not (equal a b))
                (equal c (- (/ (+ (third poly)
                                  (* (fourth poly)
                                     (+ a b)))
                               (fourth poly))))
                )
           (equal (eval-polynomial poly c) 0))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance product-divide-polynomial-lemma-22)
                 (:instance product-divide-polynomial-lemma-23
                            (c1 (+ (third poly)
                                   (* (fourth poly)
                                      (+ a b))))
                            (c2 (- (fourth poly)))
                            (x c))
                 (:instance product-divide-polynomial-lemma-24
                            (poly1 (list (+ (third poly)
                                            (* (fourth poly)
                                               (+ a b)))
                                         (fourth poly)))
                            (poly2 (list (- b) 1))
                            (poly3 (list (- a) 1))
                            (x c))
                 )
           :in-theory (disable polynomial-*
                               eval-polynomial
                               divide-polynomial-with-remainder-by-x+a
                               len-divide-poly-by-x+a=len
                               real-listp-divide-poly-by-x+a
                               NORMALIZE-FACTORS-GATHER-EXPONENTS
                               SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)
           )
          ))

(defthm is-linear-combination-eval-polynomial
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-listp poly exts))
           (is-linear-combination-p (eval-polynomial poly x) exts))
  :hints (("Goal"
           :do-not-induct t
           :induct (eval-polynomial poly x)
           :in-theory (disable quadratic-extensions-p
                               is-linear-combination-p))))

(defthm conjugate-x-is-x-when-in-subfield
  (implies (and (consp exts)
                (quadratic-extensions-p exts)
                (is-linear-combination-p x (cdr exts)))
           (equal (qef-conjugate x exts) x))
  :hints (("Goal"
           :use ((:instance subfield-means-zero-extension-part)
                 (:instance subfield-extension-parts-1))
           :in-theory (disable subfield-means-zero-extension-part
                               quadratic-extensions-p
                               is-linear-combination-p))))

(defthm conjugate-of-nil-extensions
  (equal (qef-conjugate x nil)
         (fix x))
  :hints (("Goal"
           :in-theory (enable subfield-part extension-part))))


(defthmd quadratic-extensions-of-atom
  (implies (and (quadratic-extensions-p exts)
                (not (consp exts)))
           (null exts)))

(defthm eval-polynomial-qef-conjugate
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-listp poly (rest exts)))
           (equal (eval-polynomial poly (qef-conjugate x exts))
                  (qef-conjugate (eval-polynomial poly x) exts)))
  :hints (("Goal"
           :do-not-induct t
           :induct (eval-polynomial poly x)
           :in-theory (disable quadratic-extensions-p
                               is-linear-combination-p
                               qef-conjugate))
          ("Subgoal *1/1"
           :use ((:instance qef-conjugate-of-sum
                            (x (CAR POLY))
                            (y (* X (EVAL-POLYNOMIAL (CDR POLY) X)))
                            (exts exts))
                 (:instance qef-conjugate-of-product
                            (x x)
                            (y (eval-polynomial (cdr poly) x))
                            (exts exts))
                 (:instance is-linear-combination-p-is-closed-addition
                            (x (car poly))
                            (y (* X (EVAL-POLYNOMIAL (CDR POLY) X)))
                            (exts exts))
                 (:instance is-linear-combination-p-is-closed-multiplication
                            (x x)
                            (y (EVAL-POLYNOMIAL (CDR POLY) X))
                            (exts exts))
                 (:instance is-linear-combination-eval-polynomial
                            (poly (cdr poly))
                            (exts exts)
                            (x x))
                 (:instance is-linear-combination-listp-cdr-forward
                            (l (cdr poly))
                            (exts exts))
                 (:instance conjugate-x-is-x-when-in-subfield
                            (x (car poly))
                            (exts exts))
                 (:instance quadratic-extensions-of-atom)
                 )
           :do-not '(generalize)
           :in-theory (disable quadratic-extensions-p
                               is-linear-combination-p
                               is-linear-combination-p-is-closed-addition
                               is-linear-combination-p-is-closed-multiplication
                               is-linear-combination-eval-polynomial
                               is-linear-combination-listp-cdr-forward
                               conjugate-x-is-x-when-in-subfield
                               qef-conjugate
                               qef-conjugate-of-sum
                               qef-conjugate-of-product))
          ))


(defthmd conjugate-of-root-is-root-of-polynomial
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-listp poly (rest exts))
                (equal (eval-polynomial poly x) 0))
           (equal (eval-polynomial poly (qef-conjugate x exts)) 0))
  :hints (("Goal"
           :use ((:instance eval-polynomial-qef-conjugate)
                 )
           :in-theory (disable eval-polynomial-qef-conjugate
                               quadratic-extensions-p
                               is-linear-combination-p
                               is-linear-combination-listp
                               eval-polynomial))))

(defun-sk exists-root-in-field-extension (poly exts)
  (exists (x)
          (and (equal (eval-polynomial poly x) 0)
               (is-linear-combination-p x exts))))


(defthmd poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-1
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-listp poly (rest exts))
                (acl2-numberp x) 
                (equal (eval-polynomial poly x) 0)
                (equal (qef-conjugate x exts) x))
           (exists-root-in-field-extension poly (rest exts)))
  :hints (("Goal"
           :use ((:instance exists-root-in-field-extension-suff
                            (poly poly)
                            (exts (rest exts))
                            (x x)))
           :in-theory (disable QUADRATIC-EXTENSIONS-P
                               is-linear-combination-p
                               is-linear-combination-listp
                               eval-polynomial)
           )))

(defthmd poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-2
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-listp poly (rest exts))
                (acl2-numberp x) 
                (equal (eval-polynomial poly x) 0)
                (not (equal (qef-conjugate x exts) x))
                (polynomial-p poly)
                (equal (len poly) 4)
                (not (equal (fourth poly) 0))
                (equal c (- (/ (+ (third poly)
                                  (* (fourth poly)
                                     (+ x (qef-conjugate x exts))))
                               (fourth poly)))))
           (equal (eval-polynomial poly c) 0))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance conjugate-of-root-is-root-of-polynomial)
                 (:instance product-divide-polynomial-lemma-25
                            (a x)
                            (b (qef-conjugate x exts))
                            (poly poly)
                            (c c))
                 )
           :in-theory (disable quadratic-extensions-p
                               is-linear-combination-p
                               is-linear-combination-listp
                               eval-polynomial
                               qef-conjugate))))

(defthm x+x-conjugate
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                )
           (equal (+ x (qef-conjugate x exts))
                  (* 2 (subfield-part x exts))))
  :hints (("Goal"
           :use ((:instance subfield-extension-parts-1))
           :in-theory (disable quadratic-extensions-p
                               is-linear-combination-p
                               subfield-extension-parts-1)))
  )

(defthmd poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-3
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-listp poly (rest exts))
                (acl2-numberp x) 
                (equal (eval-polynomial poly x) 0)
                (not (equal (qef-conjugate x exts) x))
                (polynomial-p poly)
                (equal (len poly) 4)
                (not (equal (fourth poly) 0))
                (equal c (- (/ (+ (third poly)
                                  (* 2
                                     (fourth poly)
                                     (subfield-part x exts)))
                               (fourth poly)))))
           (equal (eval-polynomial poly c) 0))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-2)
                 )
           :in-theory (disable quadratic-extensions-p
                               is-linear-combination-p
                               is-linear-combination-listp
                               eval-polynomial
                               qef-conjugate))))

(defthmd poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-4
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-listp poly (rest exts))
                (equal (len poly) 4))
           (is-linear-combination-p (third poly) (rest exts)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable is-linear-combination-p
                               quadratic-extensions-p))))

(defthmd poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-5
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-listp poly (rest exts))
                (equal (len poly) 4))
           (is-linear-combination-p (fourth poly) (rest exts)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable is-linear-combination-p
                               quadratic-extensions-p))))

(defthmd poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-6
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-listp poly (rest exts))
                (equal (len poly) 4))
           (is-linear-combination-p (* 2 (fourth poly)) (rest exts)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance is-linear-combination-p-is-closed-multiplication
                            (x 2)
                            (y (fourth poly))
                            (exts (rest exts)))
                 (:instance poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-5))
           :in-theory (disable is-linear-combination-p
                               quadratic-extensions-p))))

(defthmd poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-7
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-listp poly (rest exts))
                (equal (len poly) 4))
           (is-linear-combination-p (* 2 (fourth poly) (subfield-part x exts))
                                    (rest exts)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance is-linear-combination-p-is-closed-multiplication
                            (x (* 2 (fourth poly)))
                            (y (subfield-part x exts))
                            (exts (rest exts)))
                 (:instance poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-6)
                 (:instance subfield-extension-parts-2))
           :in-theory (disable is-linear-combination-p
                               quadratic-extensions-p))))

(defthmd poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-8
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-listp poly (rest exts))
                (equal (len poly) 4))
           (is-linear-combination-p (+ (third poly)
                                       (* 2 (fourth poly) (subfield-part x exts)))
                                    (rest exts)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance is-linear-combination-p-is-closed-addition
                            (x (third poly))
                            (y (* 2 (fourth poly) (subfield-part x exts)))
                            (exts (rest exts)))
                 (:instance poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-7)
                 (:instance poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-4))
           :in-theory (disable is-linear-combination-p
                               quadratic-extensions-p))))

(defthmd poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-9
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-listp poly (rest exts))
                (equal (len poly) 4)
                (not (equal (fourth poly) 0)))
           (is-linear-combination-p (/ (+ (third poly)
                                          (* 2 (fourth poly) (subfield-part x exts)))
                                       (fourth poly))
                                    (rest exts)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance is-linear-combination-p-is-closed-multiplication
                            (x (+ (third poly)
                                  (* 2 (fourth poly) (subfield-part x exts))))
                            (y (/ (fourth poly)))
                            (exts (rest exts)))
                 (:instance is-linear-combination-p-has-multiplicative-inverse
                            (x (fourth poy))
                            (exts (rest exts)))
                 (:instance poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-8)
                 (:instance poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-5))
           :in-theory (disable is-linear-combination-p
                               quadratic-extensions-p))))

(defthmd poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-10
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-listp poly (rest exts))
                (equal (len poly) 4)
                (not (equal (fourth poly) 0)))
           (is-linear-combination-p (- (/ (+ (third poly)
                                             (* 2 (fourth poly) (subfield-part x exts)))
                                          (fourth poly)))
                                    (rest exts)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance is-linear-combination-p-has-additive-inverse
                            (x (/ (+ (third poly)
                                     (* 2 (fourth poly) (subfield-part x exts)))
                                  (fourth poly)))
                            (exts (rest exts)))
                 (:instance poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-9))
           :in-theory (disable is-linear-combination-p
                               quadratic-extensions-p))))

(defthmd poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-11
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-listp poly (rest exts))
                (acl2-numberp x) 
                (equal (eval-polynomial poly x) 0)
                (not (equal (qef-conjugate x exts) x))
                (polynomial-p poly)
                (equal (len poly) 4)
                (not (equal (fourth poly) 0))
                )
           (exists-root-in-field-extension poly (rest exts)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance exists-root-in-field-extension-suff
                            (poly poly)
                            (exts (rest exts))
                            (x (- (/ (+ (third poly)
                                        (* 2 (fourth poly) (subfield-part x exts)))
                                     (fourth poly)))))
                 (:instance poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-10)
                 (:instance poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-3
                            (c (- (/ (+ (third poly)
                                        (* 2 (fourth poly) (subfield-part x exts)))
                                     (fourth poly)))))
                 )
           :in-theory (disable QUADRATIC-EXTENSIONS-P
                               is-linear-combination-p
                               is-linear-combination-listp
                               eval-polynomial
                               qef-conjugate
                               polynomial-p)
           )))

(defthmd poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-12
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-p x exts)
                (is-linear-combination-listp poly (rest exts))
                (acl2-numberp x) 
                (equal (eval-polynomial poly x) 0)
                (polynomial-p poly)
                (equal (len poly) 4)
                (not (equal (fourth poly) 0))
                )
           (exists-root-in-field-extension poly (rest exts)))
  :hints (("Goal"
           :use ((:instance poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-1)
                 (:instance poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-11))
           :in-theory nil)))

(defthmd poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma
  (implies (and (quadratic-extensions-p exts)
                (is-linear-combination-listp poly (rest exts))
                (polynomial-p poly)
                (equal (len poly) 4)
                (not (equal (fourth poly) 0))
                (exists-root-in-field-extension poly exts)
                )
           (exists-root-in-field-extension poly (rest exts)))
  :hints (("Goal"
           :use ((:instance poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma-12
                            (x (exists-root-in-field-extension-witness poly exts))
                            (poly poly)
                            (exts exts))
                 (:instance exists-root-in-field-extension))
           :in-theory (disable quadratic-extensions-p
                               is-linear-combination-p
                               is-linear-combination-listp
                               polynomial-p
                               NORMALIZE-FACTORS-GATHER-EXPONENTS))))

(defthmd poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield
  (implies (and (quadratic-extensions-p exts)
                (polynomial-p poly)
                (rational-listp poly)
                (equal (len poly) 4)
                (not (equal (fourth poly) 0))
                (exists-root-in-field-extension poly exts)
                )
           (exists-root-in-field-extension poly nil))
  :hints (("Goal"
           :induct (len exts)
           :in-theory (disable quadratic-extensions-p
                               ))
          ("Subgoal *1/1"
           :use ((:instance poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield-lemma)
                 (:instance rational-listp-is-linear-combination-listp
                            (l poly)
                            (exts (rest exts)))
                 )
           :in-theory '(quadratic-extensions-p))
          )
  )

(defun-sk exists-rational-root (poly)
  (exists (x)
          (and (equal (eval-polynomial poly x) 0)
               (rationalp x))))

(defthm in-nil-extension-means-rational
  (implies (exists-root-in-field-extension poly nil)
           (exists-rational-root poly))
  :hints (("Goal"
           :use ((:instance exists-rational-root-suff
                            (poly poly)
                            (x (exists-root-in-field-extension-witness poly nil)))))))


(defthmd poly-coeffs-in-subfield-and-root-in-field-implies-exists-rational-root
  (implies (and (quadratic-extensions-p exts)
                (polynomial-p poly)
                (rational-listp poly)
                (equal (len poly) 4)
                (not (equal (fourth poly) 0))
                (exists-root-in-field-extension poly exts)
                )
           (exists-rational-root poly))
  :hints (("Goal"
           :use ((:instance poly-coeffs-in-subfield-and-root-in-field-implies-exists-root-in-subfield))
           :in-theory (disable quadratic-extensions-p
                               polynomial-p
                               rational-listp
                               exists-root-in-field-extension
                               exists-rational-root))))

(defthmd poly-coeffs-in-subfield-and-root-in-field-implies-exists-rational-root-no-sk
  (implies (and (quadratic-extensions-p exts)
                (polynomial-p poly)
                (rational-listp poly)
                (equal (len poly) 4)
                (not (equal (fourth poly) 0))
                (is-linear-combination-p x exts)
                (equal (eval-polynomial poly x) 0)
                )
           (exists-rational-root poly))
  :hints (("Goal"
           :use ((:instance poly-coeffs-in-subfield-and-root-in-field-implies-exists-rational-root)
                 (:instance exists-root-in-field-extension-suff
                            (poly poly)
                            (exts exts)
                            (x x))
                 )
           :in-theory (disable quadratic-extensions-p
                               polynomial-p
                               rational-listp
                               exists-root-in-field-extension
                               exists-rational-root))))

;; Now that we've shown that a (cubic) polynomial with rational coefficients must have a
;; rational root when it has a root in a quadratic field extension, we turn our attention
;; to roots of polynomials with rational coefficients. In particular, we prove the
;; rational-root theorem (for cubics) that will let us know the possible rational roots
;; of a (cubic) polynomial with integer coefficients.

(defthmd rational-root-theorem-lemma-1
  (implies (and (polynomial-p poly)
                (equal (len poly) 4))
           (equal (eval-polynomial poly x)
                  (+ (first poly)
                     (* x (second poly))
                     (* (expt x 2) (third poly))
                     (* (expt x 3) (fourth poly))))))


(defthmd rational-root-theorem-lemma-2
  (implies (rationalp x)
           (equal (expt x n)
                  (* (expt (numerator x) n)
                     (expt (denominator x) (- n)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rational-implies1)
                 (:instance rational-implies2))
           :in-theory (disable rational-implies2))))  

(defthmd rational-root-theorem-lemma-3
  (implies (and (polynomial-p poly)
                (equal (len poly) 4)
                (rationalp x)
                (equal (eval-polynomial poly x) 0)
                )
           (equal (+ (first poly)
                     (* (second poly)
                        (numerator x)
                        (/ (denominator x)))
                     (* (third poly)
                        (expt (numerator x) 2)
                        (expt (denominator x) -2))
                     (* (fourth poly)
                        (expt (numerator x) 3)
                        (expt (denominator x) -3)))
                  0))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rational-root-theorem-lemma-1)
                 (:instance rational-root-theorem-lemma-2
                            (x x)
                            (n 2))
                 (:instance rational-root-theorem-lemma-2
                            (x x)
                            (n 3)))
           ))
  )

(defthmd rational-root-theorem-lemma-4
  (implies (and (integerp c1)
                (integerp c2)
                (integerp c3)
                (integerp c4)
                (integerp n)
                (posp d))
           (equal (* (+ c1
                        (* c2 n (/ d))
                        (* c3 (expt n 2) (expt d -2))
                        (* c4 (expt n 3) (expt d -3)))
                     (expt d 3))
                  (+ (* c1 (expt d 3))
                     (* c2 n (expt d 2))
                     (* c3 (expt n 2) d)
                     (* c4 (expt n 3)))))
  )

(defthmd rational-root-theorem-lemma-5
  (implies (and (integerp c1)
                (integerp c2)
                (integerp c3)
                (integerp c4)
                (integerp n)
                (posp d)
                (equal (+ c1
                          (* c2 n (/ d))
                          (* c3 (expt n 2) (expt d -2))
                          (* c4 (expt n 3) (expt d -3)))
                       0))
           (equal (+ (* c1 (expt d 3))
                     (* c2 n (expt d 2))
                     (* c3 (expt n 2) d)
                     (* c4 (expt n 3)))
                  0))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rational-root-theorem-lemma-4)
                 ))))

(defthmd rational-root-theorem-lemma-6
  (implies (and (integerp c1)
                (integerp c2)
                (integerp c3)
                (integerp c4)
                (integerp n)
                (posp d)
                (equal (+ c1
                          (* c2 n (/ d))
                          (* c3 (expt n 2) (expt d -2))
                          (* c4 (expt n 3) (expt d -3)))
                       0))
           (equal (* c4 (expt n 3))
                  (* d (- (+ (* c1 (expt d 2))
                             (* c2 n d)
                             (* c3 (expt n 2)))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rational-root-theorem-lemma-5)
                 ))))

(defthmd rational-root-theorem-lemma-7
  (implies (and (integerp c1)
                (integerp c2)
                (integerp c3)
                (integerp c4)
                (integerp n)
                (posp d)
                (equal (+ c1
                          (* c2 n (/ d))
                          (* c3 (expt n 2) (expt d -2))
                          (* c4 (expt n 3) (expt d -3)))
                       0))
           (equal (/ (* c4 (expt n 3)) d)
                  (- (+ (* c1 (expt d 2))
                        (* c2 n d)
                        (* c3 (expt n 2))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rational-root-theorem-lemma-6)
                 (:instance (:theorem
                             (implies (and (acl2-numberp x)
                                           (acl2-numberp y)
                                           (acl2-numberp z)
                                           (not (equal z 0))
                                           (equal x (* z y)))
                                      (equal (/ x z) y)))
                            (x (* c4 (expt n 3)))
                            (z d)
                            (y (- (+ (* c1 (expt d 2))
                                     (* c2 n d)
                                     (* c3 (expt n 2))))))
                 ))))

(defthmd rational-root-theorem-lemma-8
  (implies (and (integerp c1)
                (integerp c2)
                (integerp c3)
                (integerp c4)
                (integerp n)
                (posp d))
           (integerp (- (+ (* c1 (expt d 2))
                           (* c2 n d)
                           (* c3 (expt n 2))))))
  )

(defthmd rational-root-theorem-lemma-9
  (implies (and (integerp c1)
                (integerp c2)
                (integerp c3)
                (integerp c4)
                (integerp n)
                (posp d)
                (equal (+ c1
                          (* c2 n (/ d))
                          (* c3 (expt n 2) (expt d -2))
                          (* c4 (expt n 3) (expt d -3)))
                       0))
           (integerp (/ (* c4 (expt n 3)) d)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rational-root-theorem-lemma-7)
                 (:instance rational-root-theorem-lemma-8)
                 ))))

(include-book "arithmetic-5/support/num-and-denom-helper" :dir :system)

(defthmd rational-root-theorem-lemma-10
  (implies (and (integerp x)
                (integerp y)
                (< 0 y)
                (integerp (/ x y)))
           (equal (nonneg-int-mod x y) 0)))

(defthmd rational-root-theorem-lemma-11
  (implies (and (integerp x)
                (integerp y)
                (< 0 y)
                (integerp (/ x y)))
           (equal (nonneg-int-mod (abs x) y) 0))
  :hints (("Goal"
           :use ((:instance rational-root-theorem-lemma-10
                            (x x)
                            (y y))
                 (:instance rational-root-theorem-lemma-10
                            (x (- x))
                            (y y)))))
  )

(defthmd rational-root-theorem-lemma-12
  (implies (and (rationalp r)
                (integerp x)
                (integerp (* x r)))
           (equal (nonneg-int-mod (* x (numerator r)) (denominator r)) 0))
  :hints (("Goal"
           :use ((:instance rational-root-theorem-lemma-10
                            (x (* x (numerator r)))
                            (y (denominator r)))))))


(defthmd rational-root-theorem-lemma-13
  (implies (and (rationalp r)
                (integerp x)
                (integerp (* x r)))
           (equal (nonneg-int-mod (* (abs x) (numerator r)) (denominator r)) 0))
  :hints (("Goal"
           :use ((:instance rational-root-theorem-lemma-12)
                 (:instance rational-root-theorem-lemma-12
                            (r r)
                            (x (- x)))
                 ))))

(defthmd rational-root-theorem-lemma-14
  (implies (and (rationalp r)
                (integerp x)
                (integerp (* x r))
                (<= 0 r)
                )
           (equal (nonneg-int-mod x (denominator r)) 0))
  :hints (("Goal"
           :use ((:instance rational-root-theorem-lemma-13)
                 (:instance divisor-of-product-divides-factor
                            (x x)
                            (y (numerator r))
                            (z (denominator r)))
                 (:instance nonneg-int-gcd-numerator-denominator
                            (x r))
                 )
           :in-theory (disable nonneg-int-gcd-numerator-denominator)
           )))

(defthmd rational-root-theorem-lemma-15
  (implies (and (rationalp r)
                (integerp x)
                (integerp (* x r))
                (<= 0 r))
           (equal (nonneg-int-mod (abs x) (denominator r)) 0))
  :hints (("Goal"
           :use ((:instance rational-root-theorem-lemma-14)
                 (:instance rational-root-theorem-lemma-14
                            (r r)
                            (x (- x)))
                 )
           )))

(defthmd rational-root-theorem-lemma-16
  (implies (and (rationalp r)
                (integerp x)
                (integerp (* x r))
                (< r 0))
           (equal (nonneg-int-mod x (denominator r)) 0))
  :hints (("Goal"
           :use ((:instance rational-root-theorem-lemma-14
                            (r (- r)))
                 (:instance divisor-of-product-divides-factor
                            (x x)
                            (y (- (numerator r)))
                            (z (denominator r)))
                 (:instance nonneg-int-gcd-numerator-denominator
                            (x (- r)))
                 )
           :in-theory (disable nonneg-int-gcd-numerator-denominator)
           )))


(defthmd rational-root-theorem-lemma-17
  (implies (and (rationalp r)
                (integerp x)
                (integerp (* x r))
                (< r 0))
           (equal (nonneg-int-mod (abs x) (denominator r)) 0))
  :hints (("Goal"
           :use ((:instance rational-root-theorem-lemma-16)
                 (:instance rational-root-theorem-lemma-16
                            (r r)
                            (x (- x)))
                 )
           )))

(defthmd rational-root-theorem-lemma-18
  (implies (and (rationalp r)
                (integerp x)
                (integerp (* x r)))
           (equal (nonneg-int-mod (abs x) (denominator r)) 0))
  :hints (("Goal"
           :use ((:instance rational-root-theorem-lemma-15)
                 (:instance rational-root-theorem-lemma-17)))))

(defthm rational-root-theorem-lemma-19
  (implies (and (integerp x)
                (integerp d)
                (<= 0 x)
                (< 0 d)
                (equal (nonneg-int-mod x d) 0))
           (integerp (/ x d)))
  )

(defthm rational-root-theorem-lemma-20
  (implies (and (integerp x)
                (integerp d)
                (< 0 d)
                (equal (nonneg-int-mod (abs x) d) 0))
           (integerp (/ x d)))
  :hints (("Goal"
           :use ((:instance rational-root-theorem-lemma-19)
                 (:instance rational-root-theorem-lemma-19
                            (d d)
                            (x (- x)))
                 )
           )))

(defthmd rational-root-theorem-lemma-21
  (implies (and (rationalp r)
                (integerp x)
                (integerp (* x r)))
           (integerp (/ x (denominator r))))
  :hints (("Goal"
           :use ((:instance rational-root-theorem-lemma-18)
                 (:instance rational-root-theorem-lemma-20
                            (x x)
                            (d (denominator r)))))))

(defthmd rational-root-theorem-lemma-22
  (implies (and (integerp x)
                (integerp n)
                (posp d))
           (equal (* (/ n d) x n)
                  (* x (/ d) (expt n 2)))))

(defthmd rational-root-theorem-lemma-23
  (implies (and (rationalp r)
                (integerp x)
                (integerp (* x (expt (numerator r) 2) (/ (denominator r)))))
           (integerp (* x r)))
  :hints (("Goal"
           :use ((:instance rational-root-theorem-lemma-21
                            (r r)
                            (x (* x (numerator r))))
                 (:instance Rational-implies2
                            (x r))
                 (:instance rational-root-theorem-lemma-22
                            (x x)
                            (n (numerator r))
                            (d (denominator r)))
                 ))))

(defthmd rational-root-theorem-lemma-24
  (implies (and (rationalp r)
                (integerp x)
                (integerp (* x (expt (numerator r) 2) (/ (denominator r)))))
           (integerp (/ x (denominator r))))
  :hints (("Goal"
           :use ((:instance rational-root-theorem-lemma-21)
                 (:instance rational-root-theorem-lemma-23)
                 ))))

(defthmd rational-root-theorem-lemma-25
  (implies (and (rationalp r)
                (integerp x)
                (integerp (* x (expt (numerator r) 3) (/ (denominator r)))))
           (integerp (* x r)))
  :hints (("Goal"
           :use ((:instance rational-root-theorem-lemma-24
                            (r r)
                            (x (* x (numerator r))))
                 (:instance Rational-implies2
                            (x r))
                 ))))

(defthmd rational-root-theorem-lemma-26
  (implies (and (rationalp r)
                (integerp x)
                (integerp (* x (expt (numerator r) 3) (/ (denominator r)))))
           (integerp (/ x (denominator r))))
  :hints (("Goal"
           :use ((:instance rational-root-theorem-lemma-21)
                 (:instance rational-root-theorem-lemma-25)
                 ))))

(defthmd rational-root-theorem-lemma-27
  (implies (and (integerp c1)
                (integerp c2)
                (integerp c3)
                (integerp c4)
                (rationalp r)
                (equal (+ c1
                          (* c2 (numerator r) (/ (denominator r)))
                          (* c3 (expt (numerator r) 2) (expt (denominator r) -2))
                          (* c4 (expt (numerator r) 3) (expt (denominator r) -3)))
                       0))
           (integerp (/ (* c4 (expt (numerator r) 3)) (denominator r))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rational-root-theorem-lemma-9
                            (n (numerator r))
                            (d (denominator r))
                            )
                 ))))

(defthmd rational-root-theorem-lemma-28
  (implies (and (integerp c1)
                (integerp c2)
                (integerp c3)
                (integerp c4)
                (rationalp r)
                (equal (+ c1
                          (* c2 (numerator r) (/ (denominator r)))
                          (* c3 (expt (numerator r) 2) (expt (denominator r) -2))
                          (* c4 (expt (numerator r) 3) (expt (denominator r) -3)))
                       0))
           (integerp (/ c4 (denominator r))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rational-root-theorem-lemma-27)
                 (:instance rational-root-theorem-lemma-26
                            (x c4))
                 ))))


(defthmd rational-root-theorem-part-1
  (implies (and (polynomial-p poly)
                (integer-listp poly)
                (equal (len poly) 4)
                (rationalp x)
                (equal (eval-polynomial poly x) 0)
                )
           (integerp (/ (fourth poly) (denominator x))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rational-root-theorem-lemma-3)
                 (:instance rational-root-theorem-lemma-9
                            (c1 (first poly))
                            (c2 (second poly))
                            (c3 (third poly))
                            (c4 (fourth poly))
                            (n (numerator x))
                            (d (denominator x)))
                 (:instance rational-root-theorem-lemma-28
                            (c1 (first poly))
                            (c2 (second poly))
                            (c3 (third poly))
                            (c4 (fourth poly))
                            (r x)))
           )))


(defthmd rational-root-theorem-lemma-29
  (implies (and (integerp c1)
                (integerp c2)
                (integerp c3)
                (integerp c4)
                (integerp n)
                (posp d)
                (equal (+ c1
                          (* c2 n (/ d))
                          (* c3 (expt n 2) (expt d -2))
                          (* c4 (expt n 3) (expt d -3)))
                       0))
           (equal (* c1 (expt d 3))
                  (* n (- (+ (* c2 (expt d 2))
                             (* c3 n d)
                             (* c4 (expt n 2)))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rational-root-theorem-lemma-5)
                 ))))

(defthmd rational-root-theorem-lemma-30
  (implies (and (integerp c1)
                (integerp c2)
                (integerp c3)
                (integerp c4)
                (integerp n)
                (not (equal n 0))
                (posp d)
                (equal (+ c1
                          (* c2 n (/ d))
                          (* c3 (expt n 2) (expt d -2))
                          (* c4 (expt n 3) (expt d -3)))
                       0))
           (equal (/ (* c1 (expt d 3)) n)
                  (- (+ (* c2 (expt d 2))
                        (* c3 n d)
                        (* c4 (expt n 2))))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rational-root-theorem-lemma-6)
                 (:instance (:theorem
                             (implies (and (acl2-numberp x)
                                           (acl2-numberp y)
                                           (acl2-numberp z)
                                           (not (equal z 0))
                                           (equal x (* z y)))
                                      (equal (/ x z) y)))
                            (x (* c1 (expt d 3)))
                            (z n)
                            (y (- (+ (* c2 (expt d 2))
                                     (* c3 n d)
                                     (* c4 (expt n 2))))))
                 ))))

(defthmd rational-root-theorem-lemma-31
  (implies (and (integerp c1)
                (integerp c2)
                (integerp c3)
                (integerp c4)
                (integerp n)
                (not (equal n 0))
                (posp d))
           (integerp (- (+ (* c2 (expt d 2))
                           (* c3 n d)
                           (* c4 (expt n 2)))))))

(defthmd rational-root-theorem-lemma-32
  (implies (and (integerp c1)
                (integerp c2)
                (integerp c3)
                (integerp c4)
                (integerp n)
                (not (equal n 0))
                (posp d)
                (equal (+ c1
                          (* c2 n (/ d))
                          (* c3 (expt n 2) (expt d -2))
                          (* c4 (expt n 3) (expt d -3)))
                       0))
           (integerp (/ (* c1 (expt d 3)) n)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rational-root-theorem-lemma-30)
                 (:instance rational-root-theorem-lemma-31))
           )))

(defthm rational-root-theorem-lemma-33
  (implies (and (rationalp r)
                (< 0 r))
           (and (equal (numerator (/ r))
                       (denominator r))
                (equal (denominator (/ r))
                       (numerator r))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance Unique-rationalp
                            (n (denominator r))
                            (d (numerator r)))
                 (:instance Rational-implies2
                            (x r)))
           :in-theory (disable Unique-rationalp
                               Rational-implies2)))
  )

(defthm rational-root-theorem-lemma-34
  (implies (and (rationalp r)
                (< r 0))
           (and (equal (numerator (/ r))
                       (- (denominator r)))
                (equal (denominator (/ r))
                       (- (numerator r)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rational-root-theorem-lemma-33
                            (r (- r))))))
  )

(defthmd rational-root-theorem-lemma-35
  (implies (and (rationalp r)
                (not (equal r 0))
                (integerp x)
                (integerp (* x (expt (denominator r) 3) (/ (numerator r)))))
           (integerp (/ x (numerator r))))
  :hints (("Goal"
           :use ((:instance rational-root-theorem-lemma-26
                            (r (/ r))
                            (x x))
                 (:instance rational-root-theorem-lemma-33)
                 (:instance rational-root-theorem-lemma-34)
                 ))))

(defthmd rational-root-theorem-lemma-36
  (implies (and (integerp c1)
                (integerp c2)
                (integerp c3)
                (integerp c4)
                (rationalp r)
                (not (equal r 0))
                (equal (+ c1
                          (* c2 (numerator r) (/ (denominator r)))
                          (* c3 (expt (numerator r) 2) (expt (denominator r) -2))
                          (* c4 (expt (numerator r) 3) (expt (denominator r) -3)))
                       0))
           (integerp (/ c1 (numerator r))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rational-root-theorem-lemma-32
                            (n (numerator r))
                            (d (denominator r)))
                 (:instance rational-root-theorem-lemma-35
                            (x c1)))
           )))

(defthmd rational-root-theorem-lemma-37
  (implies (and (consp poly)
                (polynomial-p poly))
           (equal (eval-polynomial poly 0) (first poly))))

(defthmd rational-root-theorem-part-2
  (implies (and (polynomial-p poly)
                (integer-listp poly)
                (equal (len poly) 4)
                (rationalp x)
                (equal (eval-polynomial poly x) 0)
                )
           (integerp (/ (first poly) (numerator x))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rational-root-theorem-lemma-3)
                 (:instance rational-root-theorem-lemma-9
                            (c1 (first poly))
                            (c2 (second poly))
                            (c3 (third poly))
                            (c4 (fourth poly))
                            (n (numerator x))
                            (d (denominator x)))
                 (:instance rational-root-theorem-lemma-36
                            (c1 (first poly))
                            (c2 (second poly))
                            (c3 (third poly))
                            (c4 (fourth poly))
                            (r x)))
           )))

;; Now that we have the rational root theorem, let's use it to show
;; the impossibility of doubling a cube

(defconst *poly-double-cube*   '(-2  0 0 1))

(defthm factors-of-1
  (implies (and (integerp n)
                (not (equal n 0))
                (integerp (/ 1 n)))
           (or (equal n -1)
               (equal n 1)))
  :rule-classes nil
  )

(defthm factors-of--2
  (implies (and (integerp n)
                (not (equal n 0))
                (integerp (/ -2 n)))
           (or (equal n -2)
               (equal n -1)
               (equal n 1)
               (equal n 2)))
  :hints (("Goal"
           :cases ((< 2 n)
                   (< n -2))))
  :rule-classes nil
  )

(defthmd possible-rational-roots-of-double-cube
  (implies (and (rationalp x)
                (equal (eval-polynomial *poly-double-cube* x) 0))
           (or (equal x 2)
               (equal x 1)
               (equal x -1)
               (equal x -2)))
  :hints (("Goal"
           :use ((:instance factors-of-1
                            (n (denominator x)))
                 (:instance factors-of--2
                            (n (numerator x)))
                 (:instance rational-root-theorem-part-1
                            (poly *poly-double-cube*)
                            (x x))
                 (:instance rational-root-theorem-part-2
                            (poly *poly-double-cube*)
                            (x x))
                 )
           )
          )
  )

(defthm no-rational-roots-of-double-cube
  (implies (rationalp x)
           (not (equal (eval-polynomial *poly-double-cube* x) 0)))
  :hints (("Goal"
           :use ((:instance possible-rational-roots-of-double-cube)))))

(defthm no-rational-roots-of-double-cube-sk
  (not (exists-rational-root *poly-double-cube*))
  :hints (("Goal"
           :use ((:instance exists-rational-root)
                 (:instance no-rational-roots-of-double-cube
                            (x (exists-rational-root-witness *poly-double-cube*)))
                 ))))

(defthmd roots-not-in-quadratic-extension-double-cube
  (implies (and (quadratic-extensions-p exts)
                (equal (eval-polynomial *poly-double-cube* x) 0))
           (not (is-linear-combination-p x exts)))
  :hints (("Goal"
           :use ((:instance poly-coeffs-in-subfield-and-root-in-field-implies-exists-rational-root-no-sk
                            (exts exts)
                            (x x)
                            (poly *poly-double-cube*))
                 (:instance no-rational-roots-of-double-cube-sk)))))

;; So now let's find some specific numbers that are not in any quadratic extension field

(include-book "prior/raise-to")

(defthmd raise-to-1/3-cubed
  (implies (acl2-numberp x)
           (equal (expt (raise-to x 1/3) 3)
                  x))
  :hints (("Goal"
           :use ((:instance power-of-sums
                            (x 1/3)
                            (y 1/3)
                            (a x))
                 (:instance power-of-sums
                            (x 1/3)
                            (y 2/3)
                            (a x))
                 )
           :in-theory (disable raise-to power-of-sums))))

(defthmd cube-root-of-two-is-root-of-poly-double-cube
  (equal (eval-polynomial *poly-double-cube* (raise-to 2 1/3)) 0)
  :hints (("Goal"
           :use ((:instance rational-root-theorem-lemma-1
                            (poly *poly-double-cube*)
                            (x (raise-to 2 1/3)))
                 (:instance raise-to-1/3-cubed
                            (x 2))))))

(defthm cube-root-of-two-is-not-in-quadratic-extension
  (implies (quadratic-extensions-p exts)
           (not (is-linear-combination-p (raise-to 2 1/3) exts)))
  :hints (("Goal"
           :use ((:instance roots-not-in-quadratic-extension-double-cube
                            (exts exts)
                            (x (raise-to 2 1/3) ))
                 (:instance cube-root-of-two-is-root-of-poly-double-cube)))))

(defthm cube-root-of-two-is-irrational
  (and (realp (raise-to 2 1/3))
       (not (rationalp (raise-to 2 1/3))))
  :hints (("Goal"
           :use ((:instance cube-root-of-two-is-root-of-poly-double-cube)
                 (:instance no-rational-roots-of-double-cube
                            (x (raise-to 2 1/3))))
           :in-theory (disable (raise-to)))))


;; Now let's look at the impossibility of trisecting an angle

(defconst *poly-trisect-angle* '(-1 -6 0 8))

(defthm factors-of--1
  (implies (and (integerp n)
                (not (equal n 0))
                (integerp (/ -1 n)))
           (or (equal n -1)
               (equal n 1)))
  :rule-classes nil
  )

(defthm factors-of-8
  (implies (and (integerp n)
                (not (equal n 0))
                (integerp (/ 8 n)))
           (or (equal n -8)
               (equal n -4)
               (equal n -2)
               (equal n -1)
               (equal n 1)
               (equal n 2)
               (equal n 4)
               (equal n 8)))
  :hints (("Goal"
           :cases ((< 8 n)
                   (= n -8)
                   (= n -7)
                   (= n -6)
                   (= n -5)
                   (= n -4)
                   (= n -3)
                   (= n -2)
                   (= n -1)
                   (= n 0)
                   (= n 1)
                   (= n 2)
                   (= n 3)
                   (= n 4)
                   (= n 5)
                   (= n 6)
                   (= n 7)
                   (= n 8)
                   (< n -8))))
  :rule-classes nil
  )

(defthmd possible-rational-roots-of-trisect-angle
  (implies (and (rationalp x)
                (equal (eval-polynomial *poly-trisect-angle* x) 0))
           (or (equal x 1/8)
               (equal x 1/4)
               (equal x 1/2)
               (equal x 1)
               (equal x -1/8)
               (equal x -1/4)
               (equal x -1/2)
               (equal x -1)))
  :hints (("Goal"
           :use ((:instance factors-of-8
                            (n (denominator x)))
                 (:instance factors-of--1
                            (n (numerator x)))
                 (:instance rational-root-theorem-part-1
                            (poly *poly-trisect-angle*)
                            (x x))
                 (:instance rational-root-theorem-part-2
                            (poly *poly-trisect-angle*)
                            (x x))
                 (:instance rational-implies2)
                 )
           :in-theory (disable rational-implies2)
           )
          )
  )

(defthm no-rational-roots-of-trisect-angle
  (implies (rationalp x)
           (not (equal (eval-polynomial *poly-trisect-angle* x) 0)))
  :hints (("Goal"
           :use ((:instance possible-rational-roots-of-trisect-angle)))))


(defthm no-rational-roots-of-trisect-angle-sk
  (not (exists-rational-root *poly-trisect-angle*))
  :hints (("Goal"
           :use ((:instance exists-rational-root)
                 (:instance no-rational-roots-of-trisect-angle
                            (x (exists-rational-root-witness *poly-trisect-angle*)))
                 ))))

(defthmd roots-not-in-quadratic-extension-trisect-angle
  (implies (and (quadratic-extensions-p exts)
                (equal (eval-polynomial *poly-trisect-angle* x) 0))
           (not (is-linear-combination-p x exts)))
  :hints (("Goal"
           :use ((:instance poly-coeffs-in-subfield-and-root-in-field-implies-exists-rational-root-no-sk
                            (exts exts)
                            (x x)
                            (poly *poly-trisect-angle*))
                 (:instance no-rational-roots-of-trisect-angle-sk)))))

(include-book "nonstd/nsa/trig" :dir :system)


(defthmd cosine-2x-using-cosines
  (equal (acl2-cosine (* 2 x))
         (- (* 2 (expt (acl2-cosine x) 2)) 1))
  :hints (("Goal"
           :use ((:instance cosine-of-sums)
                 (:instance sin**2->1-cos**2))
           :in-theory (disable cosine-of-sums
                               sin**2->1-cos**2))))

(encapsulate
  nil

  (local
   (defthmd cosine-3x-lemma-1
     (equal (acl2-cosine (* 3 x))
            (- (* (acl2-cosine (* 2 x))
                  (acl2-cosine x))
               (* (acl2-sine (* 2 x))
                  (acl2-sine x))))
     :hints (("Goal"
              :use ((:instance cosine-of-sums
                               (x (* 2 x))
                               (y x)))))))

  (local
   (defthmd cosine-3x-lemma-2
     (equal (acl2-cosine (* 3 x))
            (- (* (acl2-cosine (* 2 x))
                  (acl2-cosine x))
               (* (* 2
                     (acl2-sine x)
                     (acl2-cosine x))
                  (acl2-sine x))))
     :hints (("Goal"
              :use ((:instance cosine-3x-lemma-1)
                    (:instance sine-2x)
                    )
              :in-theory (disable sine-2x)
              ))))

  (local
   (defthmd cosine-3x-lemma-3
     (equal (acl2-cosine (* 3 x))
            (- (* (acl2-cosine (* 2 x))
                  (acl2-cosine x))
               (* 2
                  (acl2-cosine x)
                  (expt (acl2-sine x) 2))))
     :hints (("Goal"
              :use ((:instance cosine-3x-lemma-2)
                    )
              ))))

  (local
   (defthmd cosine-3x-lemma-4
     (equal (acl2-cosine (* 3 x))
            (- (* (acl2-cosine (* 2 x))
                  (acl2-cosine x))
               (* 2
                  (acl2-cosine x)
                  (- 1 (expt (acl2-cosine x) 2)))))
     :hints (("Goal"
              :use ((:instance cosine-3x-lemma-3)
                    (:instance (:instance sin**2->1-cos**2))
                    )
              :in-theory (disable sin**2->1-cos**2
                                  cosine-2x)
              ))))

  (local
   (defthmd cosine-3x-lemma-5
     (equal (acl2-cosine (* 3 x))
            (+ (* (acl2-cosine (* 2 x))
                  (acl2-cosine x))
               (- (* 2 (acl2-cosine x)))
               (* 2
                  (acl2-cosine x)
                  (expt (acl2-cosine x) 2))))
     :hints (("Goal"
              :use ((:instance cosine-3x-lemma-4)
                    )
              ))))

  (local
   (defthmd cosine-3x-lemma-6
     (equal (acl2-cosine (* 3 x))
            (+ (* (acl2-cosine (* 2 x))
                  (acl2-cosine x))
               (- (* 2 (acl2-cosine x)))
               (* 2
                  (expt (acl2-cosine x) 3))))
     :hints (("Goal"
              :use ((:instance cosine-3x-lemma-5)
                    )
              ))))

  (local
   (defthmd cosine-3x-lemma-7
     (equal (acl2-cosine (* 3 x))
            (+ (* (- (* 2 (expt (acl2-cosine x) 2)) 1)
                  (acl2-cosine x))
               (- (* 2 (acl2-cosine x)))
               (* 2 (expt (acl2-cosine x) 3))))
     :hints (("Goal"
              :use ((:instance cosine-3x-lemma-6)
                    (:instance cosine-2x-using-cosines)
                    )
              :in-theory (disable cosine-2x)
              ))))

  
  (local
   (defthmd cosine-3x-lemma-8
     (equal (acl2-cosine (* 3 x))
            (+ (* 2 (expt (acl2-cosine x) 3))
               (- (acl2-cosine x))
               (- (* 2 (acl2-cosine x)))
               (* 2 (expt (acl2-cosine x) 3))))
     :hints (("Goal"
              :use ((:instance cosine-3x-lemma-7)
                    )
              ))))

  (defthmd cosine-3x
    (equal (acl2-cosine (* 3 x))
           (+ (* 4 (expt (acl2-cosine x) 3))
              (* -3 (acl2-cosine x))))
    :hints (("Goal"
             :use ((:instance cosine-3x-lemma-8))
             )))
  )

(defthmd cos-trisect-60-lemma-1
  (equal (+ (* 4 (expt (acl2-cosine (/ (acl2-pi) 9)) 3))
            (* -3 (acl2-cosine (/ (acl2-pi) 9))))
         1/2)
  :hints (("Goal"
           :use ((:instance cosine-3x
                            (x (/ (acl2-pi) 9)))
                 (:instance cosine-pi/3))
           :in-theory (disable cosine-pi/3
                               cosine-pi)
           )))

(defthmd cos-trisect-60-lemma-2
  (equal (+ (* 8 (expt (acl2-cosine (/ (acl2-pi) 9)) 3))
            (* -6 (acl2-cosine (/ (acl2-pi) 9)))
            -1)
         0)
  :hints (("Goal"
           :use ((:instance cos-trisect-60-lemma-1))
           )))

(defthmd cos-pi/9-is-root-of-trisect-angle
  (equal (eval-polynomial *poly-trisect-angle* (acl2-cosine (/ (acl2-pi) 9))) 0)
  :hints (("Goal"
           :use ((:instance cos-trisect-60-lemma-2)
                 (:instance rational-root-theorem-lemma-1
                            (poly *poly-trisect-angle*)
                            (x (acl2-cosine (/ (acl2-pi) 9))))
                 ))))

(defthmd cos-pi/9-not-in-quadratic-extension-trisect-angle
  (implies (quadratic-extensions-p exts)
           (not (is-linear-combination-p (acl2-cosine (/ (acl2-pi) 9)) exts)))
  :hints (("Goal"
           :use ((:instance cos-pi/9-is-root-of-trisect-angle)
                 (:instance roots-not-in-quadratic-extension-trisect-angle
                            (x (acl2-cosine (/ (acl2-pi) 9))))))))
