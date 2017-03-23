(in-package "RTL")

(include-book "ecp")

(include-book "coi/nary/nary-mod" :dir :system)

;; The sum of two points may be conveniently represented in the form
;; (u/z^2, v/z^2), where z, u, and v are polynomials in the coordinates
;; of the addends.  The two lemmas below will allow us to represent
;; the result of a composition of additions in such a form.  This
;; provides a means of verifying the identities that we need to establish
;; the group properties: By applying these lemmas to both sides of a
;; conjectured identity and cross-multiplying, we can convert the
;; identity to a polynomial congruence, which we can verify computationally
;; using the book "poly".

(defund tripp (x)
  (and (true-listp x)
       (= (len x) 3)
       (integerp (car x))
       (integerp (cadr x))
       (integerp (caddr x))
       (not (= (mod (caddr x) (p)) 0))))

(defthm int-car-tripp
  (implies (tripp x)
           (integerp (car x)))
  :hints (("Goal" :in-theory (enable tripp)))
  :rule-classes (:type-prescription :rewrite))

(defthm int-cadr-tripp
  (implies (tripp x)
           (integerp (cadr x)))
  :hints (("Goal" :in-theory (enable tripp)))
  :rule-classes (:type-prescription :rewrite))

(defthm int-caddr-tripp
  (implies (tripp x)
           (integerp (caddr x)))
  :hints (("Goal" :in-theory (enable tripp)))
  :rule-classes (:type-prescription :rewrite))

(defthm caddr-0-tripp
  (implies (tripp x)
           (not (equal (mod (caddr x) (p)) 0))) 
  :hints (("Goal" :in-theory (enable tripp))))

(defthm caddr-0-tripp-2
  (implies (tripp x)
           (not (equal (caddr x) 0))) 
  :hints (("Goal" :in-theory (enable tripp))))

(defthm caddr-0-tripp-3
  (implies (tripp x)
           (not (equal (mod (expt (caddr x) 2) (p)) 0))) 
  :hints (("Goal" :use ((:instance mod-expt-0 (p (p)) (n (caddr x)) (k 2))))))

(defthm caddr-0-tripp-4
  (implies (tripp x)
           (not (equal (mod (expt (caddr x) 3) (p)) 0))) 
  :hints (("Goal" :use ((:instance mod-expt-0 (p (p)) (n (caddr x)) (k 3))))))

(defund dx (p)
  (f/ (car p) (expt (caddr p) 2)))

(defund dy (p)
  (f/ (cadr p) (expt (caddr p) 3)))

(defthm natp-dx
  (implies (tripp p)
           (natp (dx p)))
  :hints (("Goal" :in-theory (enable tripp dx)))
  :rule-classes (:type-prescription :rewrite)) 

(defthm natp-dy
  (implies (tripp p)
           (natp (dy p)))
  :hints (("Goal" :in-theory (enable tripp dy)))
  :rule-classes (:type-prescription :rewrite)) 

(defthm mod-dx
  (implies (tripp p)
           (equal (mod (dx p) (p)) (dx p)))
  :hints (("Goal" :in-theory (enable tripp dx))))

(defthm mod-dy
  (implies (tripp p)
           (equal (mod (dy p) (p)) (dy p)))
  :hints (("Goal" :in-theory (enable tripp dy))))

(defun decode3 (p)
  (cons (dx p) (dy p)))

;; Doubling: we define polynomial functions zdbl, udbl, and vdbl 
;; that satisfy the following:

;; Lemma: If P = (u/z^2, v,z^2), then P + P = (u'/z'^2, v',z'^3),
;; where
;;   z' = zdbl(P),
;;   u' = udbl(P),
;;   v' = vdbl(P).

(defund lamdbl (p)
  (f/ (+ (* 3 (expt (dx p) 2))
         (* 2 (a) (dx p))
         1)
      (* 2 (dy p))))

(defthm natp-lamdbl
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (natp (lamdbl p)))
  :hints (("Goal" :in-theory (enable frcp-expt dy lamdbl)
                  :use ((:instance mod-expt-0 (p (p)) (k 3) (n (frcp (caddr p))))
                        (:instance mod-frcp-0 (n (caddr p)))
                        (:instance mod*0 (n (cadr p)) (m (frcp (expt (caddr p) 3)))))))
  :rule-classes (:type-prescription :rewrite)) 

(defund xdbl (p)
  (f- (expt (lamdbl p) 2) (+ (a) (* 2 (dx p)))))

(defund ydbl (p)
  (f- (f* (lamdbl p) (- (dx p) (xdbl p)))
      (dy p)))

(defthm natp-xdbl
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (natp (xdbl p)))
  :hints (("Goal" :in-theory (enable xdbl)))
  :rule-classes (:type-prescription :rewrite)) 

(defthm natp-ydbl
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (natp (ydbl p)))
  :hints (("Goal" :in-theory (enable ydbl frcp-expt dy lamdbl)
                  :use ((:instance mod-expt-0 (p (p)) (k 3) (n (frcp (caddr p))))
                        (:instance mod-frcp-0 (n (caddr p)))
                        (:instance mod*0 (n (cadr p)) (m (frcp (expt (caddr p) 3)))))))
  :rule-classes (:type-prescription :rewrite)) 

(defund zdbl (p)
  (let ((v (cadr p))
        (z (caddr p)))
    (* 2 v z)))

(defund wdbl (p)
  (let ((u (car p))
        (z (caddr p)))
    (+ (* 3 (expt u 2))
       (* 2 (a) u (expt z 2))
       (expt z 4))))

(defund udbl (p)
  (let ((u (car p))
        (v (cadr p))
        (z (caddr p)))
    (- (expt (wdbl p) 2)
      (* 4
         (expt v 2)
         (+ (* (a) (expt z 2))
            (* 2 u))))))

(defund vdbl (p)
  (let ((u (car p))
        (v (cadr p)))
    (- (* (wdbl p)
          (- (* 4 u (expt v 2))
             (udbl p)))
       (* 8 (expt v 4)))))

(defthm natp-zdbl
  (implies (tripp p)
           (integerp (zdbl p)))
  :hints (("Goal" :in-theory (enable tripp zdbl)))
  :rule-classes (:type-prescription :rewrite)) 

(defthm zdbl-0
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (not (equal (mod (zdbl p) (p)) 0)))
  :hints (("Goal" :in-theory (enable zdbl)
                  :use ((:instance mod*0 (n 2) (m (cadr p)))
                        (:instance mod*0 (n (* 2 (cadr p))) (m (caddr p)))))))

(defthm zdbl-0-2
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (not (equal (mod (expt (zdbl p) 2) (p)) 0)))
  :hints (("Goal" :use ((:instance mod-expt-0 (k 2) (p (p)) (n (zdbl p)))))))

(defthm zdbl-0-3
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (not (equal (mod (expt (zdbl p) 3) (p)) 0)))
  :hints (("Goal" :use ((:instance mod-expt-0 (k 3) (p (p)) (n (zdbl p)))))))

(defthm zdbl-0-4
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (not (equal (zdbl p) 0)))
  :hints (("Goal" :in-theory (enable zdbl)
                  :use ((:instance mod*0 (n 2) (m (cadr p)))
                        (:instance mod*0 (n (* 2 (cadr p))) (m (caddr p)))))))

(defthm natp-wdbl
  (implies (tripp p)
           (integerp (wdbl p)))
  :hints (("Goal" :in-theory (enable wdbl)))
  :rule-classes (:type-prescription :rewrite)) 

(defthm natp-udbl
  (implies (tripp p)
           (integerp (udbl p)))
  :hints (("Goal" :in-theory (enable wdbl udbl)))
  :rule-classes (:type-prescription :rewrite)) 

(defthm natp-vdbl
  (implies (tripp p)
           (integerp (vdbl p)))
  :hints (("Goal" :in-theory (enable udbl wdbl vdbl)))
  :rule-classes (:type-prescription :rewrite)) 

(defund dbl (p)
  (list (udbl p)
        (vdbl p)
        (zdbl p)))

(local-defthm decode3-dbl-1
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (not (= (mod (dy p) (p)) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable frcp-expt dy)
                  :use ((:instance mod-expt-0 (n (frcp (caddr p))) (k 3) (p (p)))
                        (:instance mod-frcp-0 (n (caddr p)))
                        (:instance mod*0 (n (cadr p)) (m (frcp (expt (caddr p) 3))))))))

(defthmd decode3-dbl-2
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (not (equal (mod (* 2 (dy p)) (p)) 0)))
  :hints (("Goal" :use (decode3-dbl-1
                        (:instance odd-char (n (dy p)))))))

(defthmd ec-decode3-dbp
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (not (equal (ec- (decode3 p)) (decode3 p))))
  :hints (("Goal" :use (decode3-dbl-2
                        (:instance mod-equal-0 (a (dy p)) (b (- (dy p))) (n (p))))
                  :in-theory (enable ec-))))

(local-defthm decode3-dbl-3
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (ec+slope (cons (dx p) (dy p)) (cons (dx p) (dy p)))
                  (lamdbl p)))
  :hints (("Goal" :in-theory (enable ec+slope lamdbl)
                  :use (decode3-dbl-2))))

(local-defthm decode3-dbl-4
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (ec+x (cons (dx p) (dy p)) (cons (dx p) (dy p)))
                  (xdbl p)))
  :hints (("Goal" :in-theory (enable decode3-dbl-2 xdbl ec+x))))

(local-defthm decode3-dbl-5
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (ec+y (cons (dx p) (dy p)) (cons (dx p) (dy p)))
                  (ydbl p)))
  :hints (("Goal" :in-theory (enable decode3-dbl-2 ydbl ec+y))))

(defthmd decode3-dbl-6
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (ec+ (decode3 p) (decode3 p))
                  (cons (xdbl p) (ydbl p))))
  :hints (("Goal" :use (ec-decode3-dbp) :in-theory (enable ec+rewrite))))

(local-defthmd decode3-dbl-7
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (lamdbl p)
                  (f/ (+ (* 3 (expt (caddr p) 4) (expt (dx p) 2))
                         (* 2 (a) (expt (caddr p) 4) (dx p))
                         (expt (caddr p) 4))
                      (* 2 (expt (caddr p) 4) (dy p)))))
  :hints (("Goal" :in-theory (enable lamdbl)
                  :use ((:instance mod-expt-0 (p (p)) (n (caddr p)) (k 4))
                        (:instance f/cancel (a (expt (caddr p) 4)) 
                                            (n (+ (* 3 (expt (dx p) 2)) (* 2 (a) (dx p)) 1))
                                            (m (* 2 (dy p))))))))

(local-defthmd decode3-dbl-8
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* 3 (expt (caddr p) 4) (expt (dx p) 2)) (p))
                  (mod (* 3 (expt (car p) 2) (expt (caddr p) 4) (frcp (expt (caddr p) 4))) (p))))
  :hints (("Goal" :in-theory (enable frcp-expt dx)
                  :use ((:instance mod-expt-0 (p (p)) (n (caddr p)) (k 4))))))

(local-defthmd decode3-dbl-9
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* 3 (expt (caddr p) 4) (expt (dx p) 2)) (p))
                  (mod (* 3 (expt (car p) 2)) (p))))
  :hints (("Goal" :use (decode3-dbl-8
                        (:instance mod-expt-0 (p (p)) (k 4) (n (caddr p))) 
                        (:instance frcp-cor (m (* 3 (expt (car p) 2))) (n (expt (caddr p) 4)))))))

(local-defthmd decode3-dbl-10
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* 2 (a) (expt (caddr p) 4) (dx p)) (p))
                  (mod (* 2 (a) (car p) (expt (caddr p) 4) (frcp (expt (caddr p) 2))) (p))))
  :hints (("Goal" :in-theory (enable frcp-expt dx)
                  :use ((:instance mod-expt-0 (p (p)) (n (caddr p)) (k 2))))))

(local-defthmd decode3-dbl-11
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* 2 (a) (expt (caddr p) 4) (dx p)) (p))
                  (mod (* 2 (a) (car p) (expt (caddr p) 2)) (p))))
  :hints (("Goal" :use (decode3-dbl-10
                        (:instance mod-expt-0 (p (p)) (n (caddr p)) (k 2))
                        (:instance frcp-cor (m (* 2 (a) (car p) (expt (caddr p) 2))) (n (expt (caddr p) 2)))))))

(local-defthmd decode3-dbl-12
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* 2 (expt (caddr p) 4) (dy p)) (p))
                  (mod (* 2 (cadr p) (expt (caddr p) 4) (frcp (expt (caddr p) 3))) (p))))
  :hints (("Goal" :in-theory (enable frcp-expt dy)
                  :use ((:instance mod-expt-0 (p (p)) (n (caddr p)) (k 3))))))

(local-defthmd decode3-dbl-13
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* 2 (expt (caddr p) 4) (dy p)) (p))
                  (mod (* 2 (cadr p) (caddr p)) (p))))
  :hints (("Goal" :use (decode3-dbl-12
                        (:instance mod-expt-0 (p (p)) (n (caddr p)) (k 3))
                        (:instance frcp-cor (m (* 2 (cadr p) (caddr p))) (n (expt (caddr p) 3)))))))

(local-defthmd decode3-dbl-14
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (not (= (mod (* 2 (expt (caddr p) 4) (dy p)) (p)) 0)))
  :hints (("Goal" :use (decode3-dbl-13
                        (:instance mod*0 (n 2) (m (* (cadr p) (caddr p))))
                        (:instance mod*0 (n (cadr p)) (m (caddr p)))))))

(local-defthmd decode3-dbl-15
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (+ (mod (* 3 (expt (caddr p) 4) (expt (dx p) 2)) (p))
                          (mod (* 2 (a) (expt (caddr p) 4) (dx p)) (p))
                          (mod (expt (caddr p) 4) (p)))
                       (p))
                  (mod (+ (mod (* 3 (expt (car p) 2)) (p))
                          (mod (* 2 (a) (car p) (expt (caddr p) 2)) (p))
                          (mod (expt (caddr p) 4) (p)))
                       (p))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (decode3-dbl-9
                        decode3-dbl-11))))

(local-defthmd decode3-dbl-16
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (+ (* 3 (expt (caddr p) 4) (expt (dx p) 2))
                          (* 2 (a) (expt (caddr p) 4) (dx p))
                          (expt (caddr p) 4))
                       (p))
                  (mod (+ (* 3 (expt (car p) 2))
                          (* 2 (a) (car p) (expt (caddr p) 2))
                          (expt (caddr p) 4))
                       (p))))
  :hints (("Goal" :use (decode3-dbl-15))))

(local-defthmd decode3-dbl-17
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (lamdbl p)
                  (f/ (mod (+ (* 3 (expt (caddr p) 4) (expt (dx p) 2))
                              (* 2 (a) (expt (caddr p) 4) (dx p))
                              (expt (caddr p) 4))
                           (p))
                      (mod (* 2 (expt (caddr p) 4) (dy p))
                           (p)))))
  :hints (("Goal" :in-theory (enable decode3-dbl-7)
                  :use (decode3-dbl-14
                        (:instance f/mod (n (+ (* 3 (expt (caddr p) 4) (expt (dx p) 2))
                                               (* 2 (a) (expt (caddr p) 4) (dx p))
                                               (expt (caddr p) 4)))
                                         (m (* 2 (expt (caddr p) 4) (dy p))))))))

(local-defthmd decode3-dbl-18
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (lamdbl p)
                  (f/ (mod (+ (* 3 (expt (car p) 2))
                              (* 2 (a) (car p) (expt (caddr p) 2))
                              (expt (caddr p) 4))
                           (p))
                      (mod (* 2 (cadr p) (caddr p)) (p)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(decode3-dbl-17))
                  :use (decode3-dbl-13 decode3-dbl-16))))

(local-defthmd decode3-dbl-19
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (lamdbl p)
                  (f/ (wdbl p) (zdbl p))))
  :hints (("Goal" :in-theory (enable wdbl zdbl decode3-dbl-18)
                  :use (decode3-dbl-14 decode3-dbl-13
                        (:instance f/mod (n (+ (* 3 (expt (car p) 2))
                                               (* 2 (a) (car p) (expt (caddr p) 2))
                                               (expt (caddr p) 4)))
                                         (m (* 2 (cadr p) (caddr p))))))))

(local-defthmd decode3-dbl-20
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* (xdbl p) (expt (zdbl p) 2)) (p))
                  (mod (- (* (expt (zdbl p) 2) (expt (lamdbl p) 2))
                          (* (expt (zdbl p) 2) (+ (a) (* 2 (dx p)))))
                       (p))))
  :hints (("Goal" :in-theory (enable xdbl))))

(local-defthmd decode3-dbl-21
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (- (* (expt (zdbl p) 2) (expt (lamdbl p) 2))
                          (* (expt (zdbl p) 2) (+ (a) (* 2 (dx p)))))
                       (p))
                  (mod (- (mod (* (expt (zdbl p) 2) (expt (lamdbl p) 2)) (p))
                          (mod (* (expt (zdbl p) 2) (+ (a) (* 2 (dx p)))) (p)))
                       (p)))))

(local-defthmd decode3-dbl-22
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* (xdbl p) (expt (zdbl p) 2)) (p))
                  (mod (- (mod (* (expt (zdbl p) 2) (expt (lamdbl p) 2)) (p))
                          (mod (* (expt (zdbl p) 2) (+ (a) (* 2 (dx p)))) (p)))
                       (p))))
  :hints (("Goal" :use (decode3-dbl-20 decode3-dbl-21)
                    :in-theory (theory 'minimal-theory))))

(local-defthmd decode3-dbl-23
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* (expt (zdbl p) 2) (expt (lamdbl p) 2)) (p))
                  (mod (* (expt (wdbl p) 2) (frcp (expt (zdbl p) 2)) (expt (zdbl p) 2)) (p))))
  :hints (("Goal" :in-theory (enable frcp-expt decode3-dbl-19))))

(local-defthmd decode3-dbl-24
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* (expt (zdbl p) 2) (expt (lamdbl p) 2)) (p))
                  (mod (expt (wdbl p) 2) (p))))
  :hints (("Goal" :use (decode3-dbl-23
                        (:instance frcp-cor (m (expt (wdbl p) 2)) (n (expt (zdbl p) 2)))
                        (:instance mod-expt-0 (p (p)) (k 2) (n (zdbl p)))))))

(local-defthmd decode3-dbl-25
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* (expt (zdbl p) 2) (+ (a) (* 2 (dx p)))) (p))
                  (mod (+ (* 4 (a) (expt (* (cadr p) (caddr p)) 2))
                          (mod (* 8 (car p) (expt (cadr p) 2) (expt (caddr p) 2) (frcp (expt (caddr p) 2))) (p)))
                       (p))))                          
  :hints (("Goal" :in-theory (enable zdbl dx))))

(local-defthmd decode3-dbl-26
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* 8 (car p) (expt (cadr p) 2) (expt (caddr p) 2) (frcp (expt (caddr p) 2))) (p))
                  (mod (* 8 (car p) (expt (cadr p) 2)) (p))))
  :hints (("Goal" :use ((:instance frcp-cor (m (* 8 (car p) (expt (cadr p) 2))) (n (expt (caddr p) 2)))
                        (:instance mod-expt-0 (p (p)) (k 2) (n (caddr p)))))))

(local-defthmd decode3-dbl-27
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* (expt (zdbl p) 2) (+ (a) (* 2 (dx p)))) (p))
                  (mod (+ (* 4 (a) (expt (* (cadr p) (caddr p)) 2))
                          (mod (* 8 (car p) (expt (cadr p) 2)) (p)))
                       (p))))                          
  :hints (("Goal" :use (decode3-dbl-25 decode3-dbl-26)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd decode3-dbl-28
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* (expt (zdbl p) 2) (+ (a) (* 2 (dx p)))) (p))
                  (mod (+ (* 4 (a) (expt (* (cadr p) (caddr p)) 2))
                          (* 8 (car p) (expt (cadr p) 2)))
                       (p))))                          
  :hints (("Goal" :use (decode3-dbl-27))))

(local-defthmd decode3-dbl-29
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* (xdbl p) (expt (zdbl p) 2)) (p))
                  (mod (- (mod (expt (wdbl p) 2) (p))
                          (mod (+ (* 4 (a) (expt (* (cadr p) (caddr p)) 2))
                                  (* 8 (car p) (expt (cadr p) 2)))
                               (p)))
                       (p))))
  :hints (("Goal" :use (decode3-dbl-22 decode3-dbl-24 decode3-dbl-28)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd decode3-dbl-30
  (implies (and (tripp p) (integerp (expt (wdbl p) 2))
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* (xdbl p) (expt (zdbl p) 2)) (p))
                  (mod (- (expt (wdbl p) 2)
                          (+ (* 4 (a) (expt (* (cadr p) (caddr p)) 2))
                             (* 8 (car p) (expt (cadr p) 2))))
                       (p))))
  :hints (("Goal" :use (decode3-dbl-29))))

(local-defthmd decode3-dbl-31
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* (xdbl p) (expt (zdbl p) 2)) (p))
                  (mod (- (expt (wdbl p) 2)
                          (+ (* 4 (a) (expt (* (cadr p) (caddr p)) 2))
                             (* 8 (car p) (expt (cadr p) 2))))
                       (p))))
  :hints (("Goal" :use (decode3-dbl-30))))

(local-defthmd decode3-dbl-32
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* (xdbl p) (expt (zdbl p) 2)) (p))
                  (mod (udbl p) (p))))
  :hints (("Goal" :use (decode3-dbl-31)
                  :in-theory (enable udbl))))

(local-defthmd decode3-dbl-33
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (xdbl p) (p))
                  (f/ (udbl p) (expt (zdbl p) 2))))
  :hints (("Goal" :use (decode3-dbl-32
                        (:instance mod-expt-0 (p (p)) (k 2) (n (zdbl p)))
                        (:instance f*/ (m (udbl p)) (a (expt (zdbl p) 2)) (n (xdbl p)))))))

(local (in-theory (enable nary::mod-rules)))

(local-defthmd decode3-dbl-34
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* (ydbl p) (expt (zdbl p) 3)) (p))
                  (mod (- (mod (* (expt (zdbl p) 3) (lamdbl p) (dx p)) (p))
                          (+ (mod (* (expt (zdbl p) 3) (lamdbl p) (xdbl p)) (p))
                             (mod (* (expt (zdbl p) 3) (dy p)) (p))))
                       (p))))
  :hints (("Goal" :in-theory (enable ydbl))))

(local-defthmd decode3-dbl-35
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* (expt (zdbl p) 3) (lamdbl p) (dx p)) (p))
                  (mod (* (expt (zdbl p) 2) (wdbl p) (dx p)) (p))))
  :hints (("Goal" :in-theory (enable decode3-dbl-19)
                  :use ((:instance frcp-cor (m (* (expt (zdbl p) 2) (wdbl p) (dx p))) (n (zdbl p)))))))

(local-defthmd decode3-dbl-36
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* (expt (zdbl p) 2) (wdbl p) (dx p)) (p))
                  (mod (* 4 (car p) (expt (cadr p) 2) (wdbl p)) (p))))
  :hints (("Goal" :in-theory (enable dx zdbl)
                  :use ((:instance frcp-cor (m (* 4 (car p) (expt (cadr p) 2) (wdbl p))) (n (expt (caddr p) 2)))))))

(local-defthmd decode3-dbl-37
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* (expt (zdbl p) 3) (lamdbl p) (dx p)) (p))
                  (mod (* 4 (car p) (expt (cadr p) 2) (wdbl p)) (p))))
  :hints (("Goal" :use (decode3-dbl-36 decode3-dbl-35))))

(local-defthmd decode3-dbl-38
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* (expt (zdbl p) 3) (lamdbl p) (xdbl p)) (p))
                  (mod (* (wdbl p) (udbl p)) (p))))
  :hints (("Goal" :use ((:instance frcp-cor (m (* (wdbl p) (udbl p))) (n (expt (zdbl p) 3))))
                  :in-theory (enable frcp-expt decode3-dbl-19 decode3-dbl-33))))

(local-defthmd decode3-dbl-39
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* (expt (zdbl p) 3) (dy p)) (p))
                  (mod (* 8 (expt (cadr p) 4)) (p))))
  :hints (("Goal" :use ((:instance frcp-cor (m (* 8 (expt (cadr p) 4))) (n (expt (caddr p) 3))))
                  :in-theory (enable frcp-expt zdbl dy))))

(local-defthmd decode3-dbl-40
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* (ydbl p) (expt (zdbl p) 3)) (p))
                  (mod (- (mod (* 4 (car p) (expt (cadr p) 2) (wdbl p)) (p))
                          (+ (mod (* (wdbl p) (udbl p)) (p))
                             (mod (* 8 (expt (cadr p) 4)) (p))))
                       (p))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (decode3-dbl-34 decode3-dbl-37 decode3-dbl-38 decode3-dbl-39))))

(local-defthmd decode3-dbl-41
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* (ydbl p) (expt (zdbl p) 3)) (p))
                  (mod (- (* 4 (car p) (expt (cadr p) 2) (wdbl p))
                          (+ (* (wdbl p) (udbl p))
                             (* 8 (expt (cadr p) 4))))
                       (p))))
  :hints (("Goal" :in-theory (disable NARY::MOD-*-CONGRUENCE) :use (decode3-dbl-40))))

(local-defthmd decode3-dbl-42
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (* (ydbl p) (expt (zdbl p) 3)) (p))
                  (mod (vdbl p) (p))))
  :hints (("Goal" :in-theory (e/d (vdbl) (nary::mod-rules)) :use (decode3-dbl-41))))

(local-defthmd decode3-dbl-43
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (mod (ydbl p) (p))
                  (f/ (vdbl p) (expt (zdbl p) 3))))
  :hints (("Goal" :use (decode3-dbl-42
                        (:instance mod-expt-0 (p (p)) (k 3) (n (zdbl p)))
                        (:instance f*/ (m (vdbl p)) (a (expt (zdbl p) 3)) (n (ydbl p)))))))

(local-defthmd xdbl-rewrite
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (xdbl p)
                  (f/ (udbl p) (expt (zdbl p) 2))))
  :hints (("Goal" :use (decode3-dbl-33) :in-theory (e/d (xdbl) (nary::mod-rules)))))

(local-defthmd ydbl-rewrite
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (ydbl p)
                  (f/ (vdbl p) (expt (zdbl p) 3))))
  :hints (("Goal" :use (decode3-dbl-43) :in-theory (e/d (ydbl) (nary::mod-rules)))))

(local-defthmd decode3-dbl-44
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (decode3 (dbl p))
                  (cons (f/ (udbl p) (expt (zdbl p) 2))
                        (f/ (vdbl p) (expt (zdbl p) 3)))))
  :hints (("Goal" :in-theory (enable decode3 dx dy dbl decode3-dbl-2))))

(local-defthmd decode3-dbl-45
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (decode3 (dbl p))
                  (cons (xdbl p) (ydbl p))))
  :hints (("Goal" :use (decode3-dbl-44 xdbl-rewrite ydbl-rewrite))))

(defthmd dbl-formula
  (implies (and (tripp p)
                (not (= (mod (cadr p) (p)) 0)))
           (equal (decode3 (dbl p))
                  (ec+ (decode3 p) (decode3 p))))
  :hints (("Goal" :use (decode3-dbl-6 decode3-dbl-45) :in-theory (theory 'minimal-theory))))

;; Addition of distinct points: we define polynomial functions zsum 
;; usum and vsum that satisfy the following:

;; Lemma: If P = (u/z^2 ,v,z^2) and Q = (x, y), where u/z^2 <> x, 
;; then P + Q = (u'/z'^2, v',z'^2), where
;;   z' = zsum(P, Q),
;;   u' = usum(P, Q),
;;   v' = vsum(P. Q).

(defund lamsum (p1 p2)
  (f/ (f- (dy p1) (dy p2))
      (f- (dx p1) (dx p2))))

(local-defthmd mod-dx-0
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1))))
           (not (equal (mod (+ (- (dx p2)) (dx p1)) (p)) 0)))
  :hints (("goal" :in-theory (enable dx)
                  :use ((:instance mod-equal-0 (n (p)) (a (dx p1)) (b (dx p2)))))))

(defthm natp-lamsum
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1))))
           (natp (lamsum p1 p2)))
  :hints (("Goal" :use (mod-dx-0) :in-theory (enable lamsum)))
  :rule-classes (:type-prescription :rewrite)) 

(defund xsum (p1 p2)
  (f- (expt (lamsum p1 p2) 2) (+ (a) (dx p1) (dx p2))))

(defund ysum (p1 p2)
  (f- (f* (lamsum p1 p2) (- (dx p1) (xsum p1 p2)))
      (dy p1)))

(defthm natp-xsum
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1))))
           (natp (xsum p1 p2)))
  :hints (("Goal" :in-theory (enable xsum)))
  :rule-classes (:type-prescription :rewrite)) 

(defthm natp-ysum
 (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1))))
           (natp (ysum p1 p2)))
  :hints (("Goal" :in-theory (enable ysum)))
  :rule-classes (:type-prescription :rewrite)) 

(defund zsum (p1 p2)
  (let ((u (car p2))
        (z (caddr p2))
        (x (car p1)))
    (* z
       (- (* x (expt z 2))
          u))))

(defund usum (p1 p2)
  (let ((u (car p2))
        (v (cadr p2))
        (z (caddr p2))
        (x (car p1))
        (y (cadr p1)))
    (- (expt (- (* (expt z 3) y)
                v)
             2)
       (* (+ (* (expt z 2) (+ (a) x))
             u)
          (expt (- (* (expt z 2) x)
                   u)
                2)))))

(defund vsum (p1 p2)
  (let ((v (cadr p2))
        (z (caddr p2))
        (x (car p1))
        (y (cadr p1)))
    (- (* (- (* (expt z 3) y)
             v)
          (- (* (expt (zsum p1 p2) 2) x)
             (usum p1 p2)))
       (* (expt (zsum p1 p2) 3)
          y))))

(defund sum (p1 p2)
  (list (usum p1 p2)
        (vsum p1 p2)
        (zsum p1 p2)))

(defthm decode3-sum1
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1))))
           (equal (ec+slope (cons (dx p1) (dy p1)) (cons (dx p2) (dy p2)))
                  (lamsum p1 p2)))
  :hints (("Goal" :in-theory (enable ec+slope lamsum))))

(local-defthm decode3-sum-2
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1))))
           (equal (ec+x (cons (dx p1) (dy p1)) (cons (dx p2) (dy p2)))
                  (xsum p1 p2)))
  :hints (("Goal" :in-theory (enable xsum ec+x))))

(local-defthm decode3-sum-3
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1))))
           (equal (ec+y (cons (dx p1) (dy p1)) (cons (dx p2) (dy p2)))
                  (ysum p1 p2)))
  :hints (("Goal" :in-theory (enable ysum ec+y))))

(local-defthmd decode3-sum-4
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1))))
           (equal (ec+ (decode3 p1) (decode3 p2))
                  (cons (xsum p1 p2) (ysum p1 p2))))
  :hints (("Goal" :in-theory (enable ec- ec+rewrite))))

(local-defthmd decode3-sum-5
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
           (and (not (= (mod (* (expt (caddr p2) 3) (f- (dx p1) (dx p2))) (p)) 0))
                (equal (lamsum p1 p2)
                       (f/ (mod (* (expt (caddr p2) 3) (f- (dy p1) (dy p2))) (p))
                           (mod (* (expt (caddr p2) 3) (f- (dx p1) (dx p2))) (p))))))
  :hints (("Goal" :in-theory (e/d (lamsum) (f/))
                  :use (mod-dx-0
                        (:instance f/cancel (n (f- (dy p1) (dy p2)))
                                            (m (f- (dx p1) (dx p2)))
                                            (a (expt (caddr p2) 3)))
                        (:instance mod*0 (n (- (dx p1) (dx p2))) (m (expt (caddr p2) 3)))
                        (:instance f/mod (n (* (expt (caddr p2) 3) (f- (dy p1) (dy p2))))
                                         (m (* (expt (caddr p2) 3) (f- (dx p1) (dx p2)))))
                        (:instance mod-expt-0 (p (p)) (k 3) (n (caddr p2)))))))

(local-defthmd decode3-sum-6
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
           (equal (mod (* (expt (caddr p2) 3) (f- (dy p1) (dy p2))) (p))
                  (mod (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)) (p))))                   
  :hints (("Goal" :in-theory (enable dy)
                  :use ((:instance frcp-cor (m (cadr p2)) (n (expt (caddr p2) 3)))
                        (:instance mod-expt-0 (p (p)) (k 3) (n (caddr p2)))))))

(local-defthmd decode3-sum-7
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
           (equal (mod (* (expt (caddr p2) 3) (f- (dx p1) (dx p2))) (p))
                  (mod (* (caddr p2) (- (* (expt (caddr p2) 2) (car p1)) (car p2))) (p))))
  :hints (("Goal" :in-theory (enable dx)
                  :use ((:instance frcp-cor (m (* (caddr p2) (car p2))) (n (expt (caddr p2) 2)))
                        (:instance mod-expt-0 (p (p)) (k 2) (n (caddr p2)))))))

(local-defthmd decode3-sum-8
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
           (and (not (= (mod (zsum p1 p2) (p)) 0))
                (equal (lamsum p1 p2)
                       (f/ (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                           (zsum p1 p2)))))
  :hints (("Goal" :in-theory (e/d (zsum) (f/))
                  :use (decode3-sum-5 decode3-sum-6 decode3-sum-7
                        (:instance f/mod (n (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)))
                                         (m (* (caddr p2) (- (* (expt (caddr p2) 2) (car p1)) (car p2)))))))))

(defthm integerp-zsum
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
           (integerp (zsum p1 p2)))
  :hints (("Goal" :in-theory (enable zsum)))
  :rule-classes (:type-prescription :rewrite)) 

(defthm zsum-0
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
           (not (equal (mod (zsum p1 p2) (p)) 0)))
  :hints (("Goal" :use (decode3-sum-8))))

(defthm zsum-0-2
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
           (not (equal (mod (expt (zsum p1 p2) 2) (p)) 0)))
  :hints (("Goal" :use ((:instance mod-expt-0 (k 2) (p (p)) (n (zsum p1 p2)))))))

(local-defthm zsum-0-3
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
           (not (equal (mod (expt (zsum p1 p2) 3) (p)) 0)))
  :hints (("Goal" :use ((:instance mod-expt-0 (k 3) (p (p)) (n (zsum p1 p2)))))))

(local-defthm zsum-0-4
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
           (not (equal (zsum p1 p2) 0)))
  :hints (("Goal" :use (zsum-0))))

(defthm natp-usum
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
           (integerp (usum p1 p2)))
  :hints (("Goal" :in-theory (enable usum)))
  :rule-classes (:type-prescription :rewrite)) 

(defthm natp-vsum
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
           (integerp (vsum p1 p2)))
  :hints (("Goal" :in-theory (enable usum vsum)))
  :rule-classes (:type-prescription :rewrite)) 

(local-defthmd decode3-sum-9
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (xsum p1 p2) (expt (zsum p1 p2) 2)) (p))
                 (mod (- (mod (* (expt (zsum p1 p2) 2) (expt (lamsum p1 p2) 2)) (p))
                         (mod (* (expt (zsum p1 p2) 2) (+ (a) (dx p1) (dx p2))) (p)))
                      (p))))
  :hints (("Goal" :in-theory (enable xsum))))

(local-defthmd decode3-sum-10
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (zsum p1 p2) 2) (expt (lamsum p1 p2) 2)) (p))
                 (mod (* (expt (zsum p1 p2) 2) 
                         (expt (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)) 2)
                         (expt (frcp (zsum p1 p2)) 2))
                      (p))))                         
  :hints (("Goal" :in-theory (e/d (decode3-sum-8 frcp-expt) (nary::MOD-*-CONGRUENCE)))))

(local-defthmd decode3-sum-11
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (zsum p1 p2) 2) 
                         (expt (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)) 2)
                         (expt (frcp (zsum p1 p2)) 2))
                      (p))
                 (mod (* (expt (zsum p1 p2) 2) 
                         (expt (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)) 2)
                         (mod (expt (frcp (zsum p1 p2)) 2) (p)))
                      (p))))                         
  :hints (("Goal" :use ((:instance mod*rewrite-3 (a (expt (zsum p1 p2) 2))
                                                 (b (expt (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)) 2))
                                                 (c (expt (frcp (zsum p1 p2)) 2))))
                  :in-theory (disable expt mod*rewrite-3 NARY::MOD-rules))))

(local-defthmd decode3-sum-12
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (expt (frcp (zsum p1 p2)) 2) (p))
                 (frcp (expt (zsum p1 p2) 2))))
  :hints (("Goal" :in-theory (enable frcp-expt))))

(local-defthmd decode3-sum-13
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (zsum p1 p2) 2) (expt (lamsum p1 p2) 2)) (p))
                 (mod (* (expt (zsum p1 p2) 2) 
                         (expt (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)) 2)
                         (frcp (expt (zsum p1 p2) 2)))
                      (p))))                         
  :hints (("Goal" :use (decode3-sum-10 decode3-sum-11 decode3-sum-12)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd decode3-sum-14
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (zsum p1 p2) 2) (expt (lamsum p1 p2) 2)) (p))
                 (mod (expt (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)) 2) (p))))
  :hints (("Goal" :use (decode3-sum-13
                        (:instance frcp-cor (m (expt (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)) 2)) (n (expt (zsum p1 p2) 2))))
                  :in-theory (disable nary::mod-rules))))

(local-defthmd decode3-sum-15
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (* (expt (zsum p1 p2) 2) (+ (a) (dx p1) (dx p2)))
                 (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                    (expt (caddr p2) 2)
                    (+ (a) (f/ (car p1) 1) (f/ (car p2) (expt (caddr p2) 2))))))
  :hints (("Goal" :in-theory (enable zsum dx))))

(local-defthm natp-f/
  (implies (and (integerp m) (integerp n))
           (natp (f/ m n)))
  :rule-classes (:type-prescription :rewrite))

(local-defthmd decode3-sum-16
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                         (expt (caddr p2) 2)
                         (+ (a) (f/ (car p1) 1) (f/ (car p2) (expt (caddr p2) 2))))
                      (p))
                 (mod (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                         (expt (caddr p2) 2)
                         (mod (+ (a) (f/ (car p1) 1) (f/ (car p2) (expt (caddr p2) 2))) (p)))
                      (p))))
  :hints (("Goal" :in-theory (disable f/ mod*rewrite-3 NARY::MOD-*-CONGRUENCE)
                  :use ((:instance mod*rewrite-3 (a (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2))
                                                 (b (expt (caddr p2) 2))
                                                 (c (+ (a) (f/ (car p1) 1) (f/ (car p2) (expt (caddr p2) 2)))))))))

(local-defthmd decode3-sum-17
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (+ (a) (f/ (car p1) 1) (f/ (car p2) (expt (caddr p2) 2))) (p))
                 (mod (+ (a) (car p1) (* (car p2) (frcp (expt (caddr p2) 2)))) (p)))))

(local-defthmd decode3-sum-18
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                         (expt (caddr p2) 2)
                         (+ (a) (f/ (car p1) 1) (f/ (car p2) (expt (caddr p2) 2))))
                      (p))
                 (mod (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                         (expt (caddr p2) 2)
                         (mod (+ (a) (car p1) (* (car p2) (frcp (expt (caddr p2) 2)))) (p)))
                      (p))))
  :hints (("Goal" :use (decode3-sum-17 decode3-sum-16)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd decode3-sum-19
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                         (expt (caddr p2) 2)
                         (mod (+ (a) (car p1) (* (car p2) (frcp (expt (caddr p2) 2)))) (p)))
                      (p))
                 (mod (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                         (expt (caddr p2) 2)
                         (+ (a) (car p1) (* (car p2) (frcp (expt (caddr p2) 2)))))
                      (p))))
 :hints (("Goal" :in-theory (disable mod*rewrite-3 NARY::MOD-*-CONGRUENCE)
                  :use ((:instance mod*rewrite-3 (a (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2))
                                                 (b (expt (caddr p2) 2))
                                                 (c (+ (a) (car p1) (* (car p2) (frcp (expt (caddr p2) 2))))))))))

(local-defthmd decode3-sum-20
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (zsum p1 p2) 2) (+ (a) (dx p1) (dx p2))) (p))
                 (mod (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                         (expt (caddr p2) 2)
                         (+ (a) (car p1) (* (car p2) (frcp (expt (caddr p2) 2)))))
                      (p))))
 :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (decode3-sum-15 decode3-sum-16 decode3-sum-18 decode3-sum-19))))

(local-defthmd decode3-sum-21
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                         (expt (caddr p2) 2)
                         (+ (a) (car p1) (* (car p2) (frcp (expt (caddr p2) 2)))))
                      (p))
                 (mod (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                         (mod (* (expt (caddr p2) 2)
                                 (+ (a) (car p1) (* (car p2) (frcp (expt (caddr p2) 2)))))
                              (p)))
                      (p))))
 :hints (("Goal" :in-theory (disable mod*rewrite-2 NARY::MOD-*-CONGRUENCE)
                  :use ((:instance mod*rewrite-2 (a (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2))
                                                 (b (* (expt (caddr p2) 2)
                                                       (+ (a) (car p1) (* (car p2) (frcp (expt (caddr p2) 2)))))))))))

(local-defthmd decode3-sum-22
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (caddr p2) 2)
                         (+ (a) (car p1) (* (car p2) (frcp (expt (caddr p2) 2)))))
                      (p))
                 (mod (+ (* (expt (caddr p2) 2) (+ (a) (car p1)))
                         (mod (* (expt (caddr p2) 2) (car p2) (frcp (expt (caddr p2) 2))) (p)))
                      (p)))))

(local-defthmd decode3-sum-23
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (caddr p2) 2) (car p2) (frcp (expt (caddr p2) 2))) (p))
                 (mod (car p2) (p))))
  :hints (("Goal" :use ((:instance frcp-cor (m (car p2)) (n (expt (caddr p2) 2)))))))

(local-defthmd decode3-sum-24
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (caddr p2) 2)
                         (+ (a) (car p1) (* (car p2) (frcp (expt (caddr p2) 2)))))
                      (p))
                 (mod (+ (* (expt (caddr p2) 2) (+ (a) (car p1)))
                         (mod (car p2) (p)))
                      (p))))
  :hints (("Goal" :use (decode3-sum-22 decode3-sum-23))))

(local-defthmd decode3-sum-25
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (+ (* (expt (caddr p2) 2) (+ (a) (car p1)))
                         (mod (car p2) (p)))
                      (p))
                 (mod (+ (* (expt (caddr p2) 2) (+ (a) (car p1)))
                         (car p2))
                      (p)))))

(local-defthmd decode3-sum-26
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                         (expt (caddr p2) 2)
                         (+ (a) (car p1) (* (car p2) (frcp (expt (caddr p2) 2)))))
                      (p))
                 (mod (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                         (mod (+ (* (expt (caddr p2) 2) (+ (a) (car p1)))
                                 (car p2))
                              (p)))
                      (p))))
 :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (decode3-sum-21 decode3-sum-24 decode3-sum-25))))

(local-defthmd decode3-sum-27
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                         (mod (+ (* (expt (caddr p2) 2) (+ (a) (car p1)))
                                 (car p2))
                              (p)))
                      (p))
                 (mod (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                         (+ (* (expt (caddr p2) 2) (+ (a) (car p1)))
                            (car p2)))
                      (p))))
 :hints (("Goal" :in-theory (disable mod*rewrite-2 NARY::MOD-*-CONGRUENCE)
                  :use ((:instance mod*rewrite-2 (a (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2))
                                                 (b (+ (* (expt (caddr p2) 2) (+ (a) (car p1))) (car p2))))))))

(local-defthmd decode3-sum-28
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (zsum p1 p2) 2) (+ (a) (dx p1) (dx p2))) (p))
                 (mod (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                         (+ (* (expt (caddr p2) 2) (+ (a) (car p1)))
                            (car p2)))
                      (p))))
 :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (decode3-sum-20 decode3-sum-26 decode3-sum-27))))

(local-defthmd decode3-sum-29
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (xsum p1 p2) (expt (zsum p1 p2) 2)) (p))
                 (mod (- (mod (expt (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)) 2) (p))
                         (mod (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                                 (+ (* (expt (caddr p2) 2) (+ (a) (car p1)))
                                    (car p2)))
                              (p)))
                      (p))))
 :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (decode3-sum-9 decode3-sum-28 decode3-sum-14))))

(local-defthmd decode3-sum-30
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (- (mod (expt (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)) 2) (p))
                         (mod (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                                 (+ (* (expt (caddr p2) 2) (+ (a) (car p1)))
                                    (car p2)))
                              (p)))
                      (p))
                 (mod (- (mod (expt (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)) 2) (p))
                         (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                            (+ (* (expt (caddr p2) 2) (+ (a) (car p1)))
                               (car p2))))
                      (p))))
 :hints (("Goal" :in-theory (disable mod*rewrite-2 NARY::MOD-*-CONGRUENCE)
                  :use ((:instance mod-rewrite-2 (a (mod (expt (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)) 2) (p)))
                                                 (b (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                                                       (+ (* (expt (caddr p2) 2) (+ (a) (car p1))) (car p2)))))))))

(local-defthmd decode3-sum-31
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (- (mod (expt (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)) 2) (p))
                         (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                            (+ (* (expt (caddr p2) 2) (+ (a) (car p1)))
                               (car p2))))
                      (p))
                (mod (- (expt (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)) 2)
                        (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                           (+ (* (expt (caddr p2) 2) (+ (a) (car p1)))
                              (car p2))))
                      (p))))
 :hints (("Goal" :in-theory (disable mod*rewrite-1 NARY::MOD-*-CONGRUENCE)
                  :use ((:instance mod-rewrite-1 (a (expt (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)) 2))
                                                 (b (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                                                       (+ (* (expt (caddr p2) 2) (+ (a) (car p1))) (car p2)))))))))

(local-defthmd decode3-sum-32
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (xsum p1 p2) (expt (zsum p1 p2) 2)) (p))
                 (mod (- (expt (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)) 2)
                         (* (expt (- (* (car p1) (expt (caddr p2) 2)) (car p2)) 2)
                            (+ (* (expt (caddr p2) 2) (+ (a) (car p1)))
                               (car p2))))
                      (p))))
 :hints (("Goal" :in-theory (theory 'minimal-theory) :use (decode3-sum-29 decode3-sum-30 decode3-sum-31))))

(local-defthmd decode3-sum-33
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (xsum p1 p2) (expt (zsum p1 p2) 2)) (p))
                 (mod (usum p1 p2) (p))))
 :hints (("Goal" :in-theory (e/d (usum) (nary::mod-rules)) :use (decode3-sum-32))))

(local-defthmd decode3-sum-34
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (xsum p1 p2) (p))
                 (f/ (usum p1 p2) (expt (zsum p1 p2) 2))))
 :hints (("Goal" :in-theory (disable nary::mod-rules)
                 :use (decode3-sum-33
                       (:instance f*/ (m (usum p1 p2)) (a (expt (zsum p1 p2) 2)) (n (xsum p1 p2)))))))

(local-defthmd xsum-rewrite
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (xsum p1 p2)
                 (f/ (usum p1 p2) (expt (zsum p1 p2) 2))))
  :hints (("Goal" :use (decode3-sum-34) :in-theory (e/d (xsum) (nary::mod-rules)))))

(local-defthmd decode3-sum-36
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (ysum p1 p2) (expt (zsum p1 p2) 3)) (p))
                 (mod (- (mod (* (expt (zsum p1 p2) 3) (lamsum p1 p2) (dx p1)) (p))
                         (+ (mod (* (expt (zsum p1 p2) 3) (lamsum p1 p2) (xsum p1 p2))(p))
                            (mod (* (expt (zsum p1 p2) 3) (dy p1)) (p))))
                      (p))))
  :hints (("Goal" :in-theory (enable ysum))))

(local-defthmd decode3-sum-37
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
           (equal (dx p1)
                  (mod (car p1) (p))))
  :hints (("Goal" :in-theory (enable dx))))

(local-defthmd decode3-sum-38
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
           (equal (lamsum p1 p2)
                  (mod (* (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                          (frcp (zsum p1 p2)))
                       (p))))
  :hints (("Goal" :in-theory (enable decode3-sum-8))))

(local-defthmd decode3-sum-39
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (zsum p1 p2) 3) (lamsum p1 p2) (dx p1)) (p))
                 (mod (* (expt (zsum p1 p2) 3)
                         (mod (* (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                                 (frcp (zsum p1 p2)))
                              (p))
                         (mod (car p1) (p)))
                     (p))))
  :hints (("Goal" :in-theory '(decode3-sum-37 decode3-sum-38))))

(local-defthmd decode3-sum-40
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (zsum p1 p2) 3) (lamsum p1 p2) (dx p1)) (p))
                 (mod (* (expt (zsum p1 p2) 3)
                         (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                         (frcp (zsum p1 p2))
                         (mod (car p1) (p)))
                     (p))))
  :hints (("Goal" :in-theory (disable mod*rewrite-1 nary::mod-rules)
                  :use (decode3-sum-39
                        (:instance mod*rewrite-1 (a (* (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                                                       (frcp (zsum p1 p2))))
                                                 (b (* (expt (zsum p1 p2) 3)
                                                       (mod (car p1) (p)))))))))

(local-defthmd decode3-sum-41
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (zsum p1 p2) 3) (lamsum p1 p2) (dx p1)) (p))
                 (mod (* (expt (zsum p1 p2) 3)
                         (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                         (frcp (zsum p1 p2))
                         (car p1))
                     (p))))
  :hints (("Goal" :in-theory (disable mod*rewrite-1 nary::mod-rules)
                  :use (decode3-sum-40
                        (:instance mod*rewrite-1 (a (car p1))
                                                 (b (* (expt (zsum p1 p2) 3)
                                                       (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                                                       (frcp (zsum p1 p2)))))))))

(local-defthmd decode3-sum-42
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (zsum p1 p2) 3) (lamsum p1 p2) (dx p1)) (p))
                 (mod (* (expt (zsum p1 p2) 2)
                         (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                         (car p1))
                     (p))))
  :hints (("Goal" :in-theory (disable mod*rewrite-1 nary::mod-rules)
                  :use (decode3-sum-41
                        (:instance frcp-cor (m (* (expt (zsum p1 p2) 2)
                                                 (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                                                 (car p1)))
                                           (n (zsum p1 p2)))))))

(local-defthmd decode3-sum-44
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (zsum p1 p2) 3) (lamsum p1 p2) (xsum p1 p2))(p))
                 (mod (* (expt (zsum p1 p2) 3)
                         (mod (* (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                                 (frcp (zsum p1 p2)))
                              (p))
                         (xsum p1 p2))
                      (p))))
  :hints (("Goal" :in-theory (enable decode3-sum-38))))

(local-defthmd decode3-sum-45
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (zsum p1 p2) 3) (lamsum p1 p2) (xsum p1 p2))(p))
                 (mod (* (expt (zsum p1 p2) 3)
                         (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                         (frcp (zsum p1 p2))
                         (xsum p1 p2))
                      (p))))
  :hints (("Goal" :use (decode3-sum-44))))

(local-defthmd decode3-sum-46
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (zsum p1 p2) 3) (lamsum p1 p2) (xsum p1 p2))(p))
                 (mod (* (expt (zsum p1 p2) 2)
                         (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                         (xsum p1 p2))
                      (p))))
  :hints (("Goal" :use (decode3-sum-45
                        (:instance frcp-cor (m (* (expt (zsum p1 p2) 2)
                                                 (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                                                 (xsum p1 p2)))
                                           (n (zsum p1 p2)))))))

(local-defthmd decode3-sum-47
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (expt (zsum p1 p2) 3) (dy p1)) (p))
                 (mod (* (expt (zsum p1 p2) 3) (cadr p1)) (p))))
  :hints (("Goal" :in-theory (enable dy))))

(local-defthmd decode3-sum-48
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (ysum p1 p2) (expt (zsum p1 p2) 3)) (p))
                 (mod (- (mod (* (expt (zsum p1 p2) 2)
                                 (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                                 (car p1))
                              (p))
                         (+ (mod (* (expt (zsum p1 p2) 2)
                                    (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                                    (xsum p1 p2))
                                 (p))
                            (mod (* (expt (zsum p1 p2) 3) (cadr p1)) (p))))
                      (p))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (decode3-sum-36 decode3-sum-42 decode3-sum-46 decode3-sum-47))))

(local-defthmd decode3-sum-49
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
           (equal (mod (* (expt (zsum p1 p2) 2)
                          (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                          (xsum p1 p2))
                       (p))
                  (mod (* (mod (* (xsum p1 p2) (expt (zsum p1 p2) 2)) (p))
                          (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)))
                       (p)))))

(local-defthmd decode3-sum-50
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
           (equal (mod (* (expt (zsum p1 p2) 2)
                          (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                          (xsum p1 p2))
                       (p))
                  (mod (* (mod (usum p1 p2) (p))
                          (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)))
                       (p))))
  :hints (("Goal" :use (decode3-sum-49 decode3-sum-33))))

(local-defthmd decode3-sum-51
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
           (equal (mod (* (expt (zsum p1 p2) 2)
                          (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                          (xsum p1 p2))
                       (p))
                  (mod (* (usum p1 p2)
                          (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)))
                       (p))))
  :hints (("Goal" :use (decode3-sum-50))))

(local-defthmd decode3-sum-52
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (ysum p1 p2) (expt (zsum p1 p2) 3)) (p))
                 (mod (- (mod (* (expt (zsum p1 p2) 2)
                                 (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                                 (car p1))
                              (p))
                         (+ (mod (* (usum p1 p2)
                                    (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)))
                                 (p))
                            (mod (* (expt (zsum p1 p2) 3) (cadr p1)) (p))))
                      (p))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (decode3-sum-48 decode3-sum-51))))


(local-defthmd decode3-sum-53
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (ysum p1 p2) (expt (zsum p1 p2) 3)) (p))
                 (mod (- (* (expt (zsum p1 p2) 2)
                            (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                            (car p1))
                         (+ (mod (* (usum p1 p2)
                                    (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)))
                                 (p))
                            (mod (* (expt (zsum p1 p2) 3) (cadr p1)) (p))))
                      (p))))
  :hints (("Goal" :in-theory (disable mod-rewrite-1 nary::mod-rules)
                  :use (decode3-sum-52
                        (:instance mod-rewrite-1 (a (* (expt (zsum p1 p2) 2)
                                                       (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                                                       (car p1)))
                                                 (b (+ (mod (* (usum p1 p2)
                                                               (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)))
                                                            (p))
                                                       (mod (* (expt (zsum p1 p2) 3) (cadr p1)) (p)))))))))

(local-defthmd decode3-sum-54
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (ysum p1 p2) (expt (zsum p1 p2) 3)) (p))
                 (mod (- (* (expt (zsum p1 p2) 2)
                            (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                            (car p1))
                         (+ (* (usum p1 p2) (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)))
                            (mod (* (expt (zsum p1 p2) 3) (cadr p1)) (p))))
                      (p))))
  :hints (("Goal" :in-theory (disable mod-rewrite-2 nary::mod-rules)
                  :use (decode3-sum-53
                        (:instance mod-rewrite-2 (a (- (* (expt (zsum p1 p2) 2)
                                                          (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                                                          (car p1))
                                                       (mod (* (expt (zsum p1 p2) 3) (cadr p1)) (p))))
                                                 (b (* (usum p1 p2) (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)))))))))

(local-defthmd decode3-sum-55
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (ysum p1 p2) (expt (zsum p1 p2) 3)) (p))
                 (mod (- (* (expt (zsum p1 p2) 2)
                            (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                            (car p1))
                         (+ (* (usum p1 p2) (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)))
                            (* (expt (zsum p1 p2) 3) (cadr p1))))
                      (p))))
  :hints (("Goal" :in-theory (disable mod-rewrite-2 nary::mod-rules)
                  :use (decode3-sum-54
                        (:instance mod-rewrite-2 (a (- (* (expt (zsum p1 p2) 2)
                                                          (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2))
                                                          (car p1))
                                                       (* (usum p1 p2) (- (* (expt (caddr p2) 3) (cadr p1)) (cadr p2)))))
                                                 (b (* (expt (zsum p1 p2) 3) (cadr p1))))))))

(local-defthmd decode3-sum-56
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (* (ysum p1 p2) (expt (zsum p1 p2) 3)) (p))
                 (mod (vsum p1 p2) (p))))
  :hints (("Goal" :in-theory (e/d (vsum) (nary::mod-rules))
                  :use (decode3-sum-55))))

(local-defthmd decode3-sum-57
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (mod (ysum p1 p2) (p))
                 (f/ (vsum p1 p2) (expt (zsum p1 p2) 3))))
  :hints (("Goal" :in-theory (disable nary::mod-rules)
                  :use (decode3-sum-56
                       (:instance f*/ (m (vsum p1 p2)) (a (expt (zsum p1 p2) 3)) (n (ysum p1 p2)))))))

(local-defthmd ysum-rewrite
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
          (equal (ysum p1 p2)
                 (f/ (vsum p1 p2) (expt (zsum p1 p2) 3))))
  :hints (("Goal" :use (decode3-sum-57)  :in-theory (e/d (ysum) (nary::mod-rules)))))

(local-defthmd decode3-sum-59
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
           (equal (decode3 (sum p1 p2))
                  (cons (f/ (usum p1 p2) (expt (zsum p1 p2) 2))
                        (f/ (vsum p1 p2) (expt (zsum p1 p2) 3)))))
  :hints (("Goal" :in-theory (enable decode3 dx dy sum))))

(local-defthmd decode3-sum-60
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
           (equal (decode3 (sum p1 p2))
                  (cons (xsum p1 p2) (ysum p1 p2))))
  :hints (("Goal" :use (decode3-sum-59 ysum-rewrite xsum-rewrite))))

(defthmd sum-formula
  (implies (and (tripp p1)
                (tripp p2)
                (not (= (dx p2) (dx p1)))
                (= (caddr p1) 1))
            (equal (decode3 (sum p1 p2))
                  (ec+ (decode3 p1) (decode3 p2))))
  :hints (("Goal" :use (decode3-sum-4 decode3-sum-60) :in-theory (theory 'minimal-theory))))

