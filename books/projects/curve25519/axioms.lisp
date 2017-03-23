(in-package "RTL")

(include-book "terms")

;; move to ecp.lisp:

(defthmd ec-identity
  (implies (ecp p)
           (equal (ec+ (inf) p)
                  p))
  :hints (("Goal" :in-theory (enable ec+))))

(defthmd ec-inverse
  (implies (ecp p)
           (and (ecp (ec- p))
                (equal (ec+ (ec- p) p)
                       (inf))))
  :hints (("Goal" :use ((:instance ec-inverse-unique (r1 (ec- p)) (r2 p))
                        (:instance ec-- (r p))))))

;;move to terms.lisp:

(in-theory (disable (p0$) (p1$) (p2$)))

(in-theory (disable dbl$ sum$ neg$ eq$))

(in-theory (enable tripp$-dbl$))

(defthm tripp$p
  (and (tripp$ (p0$))
       (tripp$ (p1$))
       (tripp$ (p2$)))
  :hints (("Goal" :expand ((:free (x) (hide x))) :in-theory (enable evalp$ p0$ p1$ p2$ tripp$))))

(defthm caddr-p$
  (and (equal (caddr (p0$)) 1)
       (equal (caddr (p1$)) 1)
       (equal (caddr (p2$)) 1))
  :hints (("Goal" :in-theory (enable p0$ p1$ p2$))))

(defun neg$ (p)
  (list (car p) (list '- (cadr p)) (caddr p)))

(defthm caddr-neg$
  (equal (caddr (neg$ p))
         (caddr p))
  :hints (("Goal" :expand ((neg$ p)))))

(defthm tripp$-neg$
  (implies (and (tripp$ p)
                (ecp (decode3$ p)))
           (tripp$ (neg$ p)))
  :hints (("Goal" :expand ((neg$ p)) :in-theory (enable polyp$ tripp$))))

(defthm neg$-formula-1
  (equal (evalp$ (list '- x))
         (- (evalp$ x)))
  :hints (("Goal" :in-theory (enable evalp$ evalp))))

(defthmd neg$-formula
  (implies (and (tripp$ p)
                (ecp (decode3$ p)))
           (equal (decode3$ (neg$ p))
                  (ec- (decode3$ p))))
  :hints (("Goal" :in-theory (enable ec- decode3$ decode3 tripp$))
          ("Subgoal 3" :expand ((neg$ p)) :in-theory (enable dx))
          ("Subgoal 2" :in-theory (enable dy))
          ("Subgoal 1" :expand ((neg$ p)) :in-theory (enable dy))
          ("Subgoal 1'" :use ((:instance mod-rewrite-2 (a 0) (b (* (EVALP$ (CADR P)) (FRCP (EXPT (EVALP$ (CADDR P)) 3)))))))))

(in-theory (enable dbl$-formula sum$-formula neg$-formula))

(in-theory (disable p0 p1 p2 (p0) (p1) (p2)))

(in-theory (disable decode3$ ecp$))

(in-theory (enable ecp$ecp))

(defthm ecp-lemma
  (and (ecp (cons (x0) (y0)))
       (ecp (cons (x1) (y1)))
       (ecp (cons (x2) (y2))))
  :hints (("Goal" :in-theory (enable p0 p1 p2)
                  :use (ecp-assumption))))

(defthm ecp-cons
  (implies (and (ecp p) (not (equal p (inf))))
           (consp p))
  :hints (("Goal" :in-theory (enable ecp))))

(defthm ec-0-0
  (equal (ec- '(0 . 0)) '(0 . 0))
  :hints (("Goal" :in-theory (enable ec-))))

(defthm ec-0
  (equal (ec- (o)) (o))
  :hints (("Goal"  :in-theory (enable ec-))))

(defthmd ec-0-0-iff
  (implies (ecp p)
           (iff (equal p (o))
                (equal (ec- p) (o))))
  :hints (("Goal"  :in-theory (enable ecp ec-))))

(defthm ec+0-0
  (equal (ec+ '(0 . 0) '(0 . 0))
         (inf))
  :hints (("Goal"  :in-theory (enable ec- ec+))))

(defthm ec-inf
  (equal (ec- 'infinity) (inf))
  :hints (("Goal"  :in-theory (enable ec-))))

(defthm ec+inf
  (and (equal (ec+ 'infinity p) p)
       (equal (ec+ p 'infinity) p))
  :hints (("Goal"  :in-theory (enable ec+))))

(defthm x-ec-
  (equal (x (ec- p))
         (x p))
  :hints (("Goal" :in-theory (enable ec-))))

(defthmd ec+ec-
  (equal (ec+ p (ec- p))
         (inf))
  :hints (("Goal" :in-theory (enable ec+ ec-))))

(defthm ecp-consp
  (implies (and (ecp p) (atom p))
           (equal p (inf)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable ecp))))

(defthm ec+ec-2
  (implies (and (ecp p) (ecp q) (equal (ec+ p q) (inf)))
           (equal q (ec- p)))
  :rule-classes ()
  :hints (("Goal" :use (ecp-consp (:instance ecp-consp (p q)) (:instance ec+rewrite (r1 p) (r2 q))))))

(defthm p+q<>p-1
  (implies (and (ecp (cons a0 b0))
                (ecp (cons a1 b1)))
           (not (equal (ec+ (cons a0 b0) (cons a1 b1))
                       (cons a0 b0))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p0 p1)
                  :use (ecp-assumption
                        (:functional-instance p0+p1<>p0 (p0 (lambda () (if (ecp (cons a0 b0)) (cons a0 b0) (p0))))
                                                        (p1 (lambda () (if (ecp (cons a1 b1)) (cons a1 b1) (p1))))
                                                        (x0 (lambda () (if (ecp (cons a0 b0)) a0 (x0))))
                                                        (x1 (lambda () (if (ecp (cons a1 b1)) a1 (x1))))
                                                        (y0 (lambda () (if (ecp (cons a0 b0)) b0 (y0))))
                                                        (y1 (lambda () (if (ecp (cons a1 b1)) b1 (y1)))))))))

(defthm  p+q<>p
  (implies (and (ecp p)
                (ecp q)
                (not (equal q (inf))))
           (not (equal (ec+ p q) p)))
  :rule-classes ()
  :hints (("Goal" :use (ecp-consp
                        (:instance ecp-consp (p q))
                        (:instance p+q<>p-1 (a0 (car p)) (b0 (cdr p)) (a1 (car q)) (b1 (cdr q)))))))

(defthm p+q=p-q-1
  (implies (and (ecp (cons a0 b0))
                (ecp (cons a1 b1))
                (equal (ec+ (cons a0 b0) (cons a1 b1))
                       (ec+ (cons a0 b0) (ec- (cons a1 b1)))))
           (or (equal (cons a0 b0) (o))
               (equal (cons a1 b1) (o))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p0 p1)
                  :use (ecp-assumption
                        (:functional-instance p0+p1=p0-p1 (p0 (lambda () (if (ecp (cons a0 b0)) (cons a0 b0) (p0))))
                                                          (p1 (lambda () (if (ecp (cons a1 b1)) (cons a1 b1) (p1))))
                                                          (x0 (lambda () (if (ecp (cons a0 b0)) a0 (x0))))
                                                          (x1 (lambda () (if (ecp (cons a1 b1)) a1 (x1))))
                                                          (y0 (lambda () (if (ecp (cons a0 b0)) b0 (y0))))
                                                          (y1 (lambda () (if (ecp (cons a1 b1)) b1 (y1)))))))))

(defthm  p+q=p-q
  (implies (and (ecp p)
                (ecp q)
                (equal (ec+ p q) (ec+ p (ec- q))))
           (or (equal p (inf))
               (equal q (inf))
               (equal p (o))
               (equal q (o))))
  :rule-classes ()
  :hints (("Goal" :use (ecp-consp
                        (:instance ecp-consp (p q))
                        (:instance p+q=p-q-1 (a0 (car p)) (b0 (cdr p)) (a1 (car q)) (b1 (cdr q)))))))

(defund o$ () '(0 0 1))

(in-theory (disable (o$)))

(defthm caddr-o$
  (equal (caddr (o$)) 1)
  :hints (("Goal" :in-theory (enable o$))))

(defthm tripp$o$
  (tripp$ (o$))
  :hints (("Goal" :expand ((:free (x) (hide x))) :in-theory (enable evalp$ o$ tripp$))))

(defthm decode3$o$
  (equal (decode3$ (o$)) (o))
  :hints (("Goal" :in-theory (enable ecp vals dx dy vlist o$ decode3$ decode3 evalp$))))

(defthm ecp$p$
  (and (ecp$ (p0$))
       (ecp$ (p1$))
       (ecp$ (p2$))
       (ecp$ (o$)))
  :hints (("Goal" :in-theory (enable ecp$ p0$ p1$ p2$ o$))))


;;***********************************************************************
;;                              Closure
;;***********************************************************************

(defthm comp-1
  (and (ecp$ (dbl$ (p0$)))
       (ecp$ (sum$ (p0$) (p1$))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable ecp$ dbl$ sum$ p0$ p1$))))

;; [0.02 seconds]

(defthm closure-1
  (implies (not (equal (p0) (o)))
           (ecp (ec+ (p0) (p0))))
  :hints (("Goal" :use (comp-1
                        (:instance ecp$ecp (p (dbl$ (p0$))))))))

(defthm closure-2
  (ecp (ec+ (o) (o)))
  :hints (("Goal" :in-theory (enable ecp ec+ ec-))))

(defthm closure-3
  (ecp (ec+ (p0) (p0)))
  :hints (("Goal" :cases ((equal (p0) (o))))))

(defthm closure-4
  (implies (equal (p1) (ec- (p0)))
           (ecp (ec+ (p0) (p1))))
  :hints (("Goal" :in-theory (enable ecp ec+))))

(defthm ec-ec-
  (implies (and (ecp r1) (ecp r2))
           (iff (equal r1 (ec- r2))
                (equal r2 (ec- r1))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance ec-- (r r1))
                        (:instance ec-- (r r2))))))

(defthm closure-5
  (implies (equal (x (p0)) (x (p1)))
           (ecp (ec+ (p0) (p1))))
  :hints (("Goal" :use ((:instance ec-ec- (r1 (p0)) (r2 (p1)))
                        (:instance x= (r1 (p0)) (r2 (p1)))))))

(defthm closure-6
  (implies (not (equal (x (p0)) (x (p1))))
           (ecp (ec+ (p0) (p1))))
  :hints (("Goal" :use (comp-1
                        (:instance ecp$ecp (p (sum$ (p0$) (p1$))))))))

(defthm closure-7
  (ecp (ec+ (p0) (p1)))
  :hints (("Goal" :cases ((equal (x (p0)) (x (p1)))))))

(defthm closure-8
  (implies (and (ecp (cons a0 b0))
                (ecp (cons a1 b1)))
           (ecp (ec+ (cons a0 b0) (cons a1 b1))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p0 p1 p2)
                  :use (ecp-assumption
                        (:functional-instance closure-7 (p0 (lambda () (if (ecp (cons a0 b0)) (cons a0 b0) (p0))))
                                                        (p1 (lambda () (if (ecp (cons a1 b1)) (cons a1 b1) (p1))))
                                                        (p2 (lambda () (if (ecp (cons a2 b2)) (cons a2 b2) (p2))))
                                                        (x0 (lambda () (if (ecp (cons a0 b0)) a0 (x0))))
                                                        (x1 (lambda () (if (ecp (cons a1 b1)) a1 (x1))))
                                                        (x2 (lambda () (if (ecp (cons a2 b2)) a2 (x2))))
                                                        (y0 (lambda () (if (ecp (cons a0 b0)) b0 (y0))))
                                                        (y1 (lambda () (if (ecp (cons a1 b1)) b1 (y1))))
                                                        (y2 (lambda () (if (ecp (cons a2 b2)) b2 (y2)))))))))

(defthm ec-closure
  (implies (and (ecp p) (ecp q))
           (ecp (ec+ p q)))
  :hints (("Goal" :use ((:instance closure-8 (a0 (car p)) (b0 (cdr p)) (a1 (car q)) (b1 (cdr q))))
                  :in-theory (enable ec+))))

;;********************************************************************************
;;                               Commutativity
;;********************************************************************************

(defthm comp-2
  (eq$ (sum$ (p0$) (p1$))
       (sum$ (p1$) (p0$)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable eq$ sum$ p0$ p1$))))

;; [0.01 seconds]

(defthm commute-1
  (implies (not (equal (x (p0)) (x (p1))))
           (equal (ec+ (p0) (p1))
                  (ec+ (p1) (p0))))
  :hints (("Goal" :use (comp-2
                        (:instance eq$eq (p1 (sum$ (p0$) (p1$))) (p2 (sum$ (p1$) (p0$))))))))

(defthm commute-2
  (implies (equal (p0) (ec- (p1)))
           (equal (ec+ (p0) (p1))
                  (ec+ (p1) (p0))))
  :hints (("Goal" :use ((:instance ec-ec- (r1 (p0)) (r2 (p1))))
                  :in-theory (enable ec+))))

(defthm commute-3
  (equal (ec+ (p0) (p1))
         (ec+ (p1) (p0)))
  :hints (("Goal" :use (commute-1 commute-2
                        (:instance ec-ec- (r1 (p0)) (r2 (p1)))
                        (:instance x= (r1 (p0)) (r2 (p1)))))))

(defthm commute-4
  (implies (and (ecp (cons a0 b0))
                (ecp (cons a1 b1)))
           (equal (ec+ (cons a0 b0) (cons a1 b1))
                  (ec+ (cons a1 b1) (cons a0 b0))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p0 p1 p2)
                  :use (ecp-assumption
                        (:functional-instance commute-3 (p0 (lambda () (if (ecp (cons a0 b0)) (cons a0 b0) (p0))))
                                                        (p1 (lambda () (if (ecp (cons a1 b1)) (cons a1 b1) (p1))))
                                                        (p2 (lambda () (if (ecp (cons a2 b2)) (cons a2 b2) (p2))))
                                                        (x0 (lambda () (if (ecp (cons a0 b0)) a0 (x0))))
                                                        (x1 (lambda () (if (ecp (cons a1 b1)) a1 (x1))))
                                                        (x2 (lambda () (if (ecp (cons a2 b2)) a2 (x2))))
                                                        (y0 (lambda () (if (ecp (cons a0 b0)) b0 (y0))))
                                                        (y1 (lambda () (if (ecp (cons a1 b1)) b1 (y1))))
                                                        (y2 (lambda () (if (ecp (cons a2 b2)) b2 (y2)))))))))

(defthm ec-commutativity
  (implies (and (ecp p) (ecp q))
           (equal (ec+ p q) (ec+ q p)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance commute-4 (a0 (car p)) (b0 (cdr p)) (a1 (car q)) (b1 (cdr q))))
                  :in-theory (enable ec+))))

;;***********************************************************************
;;                          Associativity
;;***********************************************************************

;; (-P0) + (-P0) = -(P0 + P0)
;; (-P0) + (-P1) = -(P0 + P1)

(defthm comp-3
  (eq$ (dbl$ (neg$ (p0$)))
       (neg$ (dbl$ (p0$))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable eq$ dbl$ neg$ p0$))))

;; [0.01 seconds]

(defthm comp-4
  (eq$ (sum$ (neg$ (p0$)) (neg$ (p1$)))
       (neg$ (sum$ (p0$) (p1$))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable eq$ sum$ neg$ p0$ p1$))))

;; [0.01 seconds]

(in-theory (enable dbl$-formula sum$-formula neg$-formula))

(defthm lemma-15-1
  (implies (and (not (equal (p0) (o)))
                (not (equal (ec- (p0)) (o))))
           (equal (ec+ (ec- (p0)) (ec- (p0)))
                  (ec- (ec+ (p0) (p0)))))
  :hints (("Goal" :use (comp-3
                        (:instance eq$eq (p1 (dbl$ (neg$ (p0$)))) (p2 (neg$ (dbl$ (p0$)))))))))

(defthmd lemma-15-2
  (equal (ec+ (ec- (p0)) (ec- (p0)))
         (ec- (ec+ (p0) (p0))))
  :hints (("Goal" :use ((:instance ec-0-0-iff (p (p0)))) :cases ((equal (p0) (o))))))

(defthmd lemma-15-3
  (implies (not (equal (x (p0)) (x (p1))))
           (equal (ec+ (ec- (p0)) (ec- (p1)))
                  (ec- (ec+ (p0) (p1)))))
  :hints (("Goal" :use (comp-4
                        (:instance eq$eq (p1 (sum$ (neg$ (p0$)) (neg$ (p1$))))
                                         (p2 (neg$ (sum$ (p0$) (p1$)))))))))

(defthmd lemma-15-4
  (implies (equal (ec- (p0)) (p1))
           (equal (ec+ (ec- (p0)) (ec- (p1)))
                  (ec- (ec+ (p0) (p1)))))
  :hints (("Goal" :use (commute-3 
                        (:instance ec+ec- (p (p0)))
                        (:instance ec-ec- (r1 (p0)) (r2 (p1)))))))

(defthm lemma-15-5
  (equal (ec+ (ec- (p0)) (ec- (p1)))
         (ec- (ec+ (p0) (p1))))
  :hints (("Goal" :use (lemma-15-2 lemma-15-3 lemma-15-4 
                        (:instance ec-ec- (r1 (p0)) (r2 (p1)))
                        (:instance x= (r1 (p0)) (r2 (p1)))))))

(defthm lemma-15-6
  (implies (and (ecp (cons a0 b0))
                (ecp (cons a1 b1)))
           (equal (ec+ (ec- (cons a0 b0)) (ec- (cons a1 b1)))
                  (ec- (ec+ (cons a0 b0) (cons a1 b1)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p0 p1)
                  :use (ecp-assumption
                        (:functional-instance lemma-15-5 (p0 (lambda () (if (ecp (cons a0 b0)) (cons a0 b0) (p0))))
                                                      (p1 (lambda () (if (ecp (cons a1 b1)) (cons a1 b1) (p1))))
                                                      (x0 (lambda () (if (ecp (cons a0 b0)) a0 (x0))))
                                                      (x1 (lambda () (if (ecp (cons a1 b1)) a1 (x1))))
                                                      (y0 (lambda () (if (ecp (cons a0 b0)) b0 (y0))))
                                                      (y1 (lambda () (if (ecp (cons a1 b1)) b1 (y1)))))))))

(defthm lemma-15
  (implies (and (ecp p) (ecp q))
           (equal (ec+ (ec- p) (ec- q))
                  (ec- (ec+ p q))))
  :rule-classes ()
  :hints (("Goal" :use (ecp-consp ec-commutativity
                        (:instance ecp-consp (p q))
                        (:instance lemma-15-6 (a0 (car p)) (b0 (cdr p)) (a1 (car q)) (b1 (cdr q)))))))


;; P0 + P0 <> -P0 => (-P0) + (P0 + P0) = P0
;; P0 <> +-P1 and P0 + P1 <> -P0 => (-P0) + (P0 + P1) = P1

(defthm comp-5
  (eq$ (sum$ (neg$ (p0$))
             (dbl$ (p0$)))
       (p0$))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable eq$ dbl$ sum$ neg$ p0$))))

;; [0.01 seconds]

(defthm comp-6
  (eq$ (sum$ (neg$ (p0$))
             (sum$ (p0$) (p1$)))
       (p1$))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable eq$ sum$ neg$ p0$ p1$))))

;; [0.04 seconds]

(defthmd lemma-16-1
  (implies (and (not (equal (p0) (o)))
                (not (equal (x (p0)) (x (ec+ (p0) (p0))))))
           (equal (ec+ (ec- (p0)) (ec+ (p0) (p0)))
                  (p0)))
  :hints (("Goal" :use (comp-5
                        (:instance eq$eq (p1 (sum$ (neg$ (p0$)) (dbl$ (p0$)))) (p2 (p0$)))))))

(defthm lemma-16-2
  (implies (not (equal (ec+ (p0) (p0)) (ec- (p0))))
           (equal (ec+ (ec- (p0)) (ec+ (p0) (p0)))
                  (p0)))
  :hints (("Goal" :use (lemma-16-1
                        (:instance p+q<>p (p (p0)) (q (p0)))
                        (:instance x= (r1 (ec+ (p0) (p0))) (r2 (p0)))))))

(defthmd lemma-16-3
  (implies (and (not (equal (x (p0)) (x (p1))))
                (not (equal (x (p0)) (x (ec+ (p0) (p1))))))
           (equal (ec+ (ec- (p0)) (ec+ (p0) (p1)))
                  (p1)))
  :hints (("Goal" :use (comp-6
                        (:instance eq$eq (p1 (sum$ (neg$ (p0$)) (sum$ (p0$) (p1$)))) (p2 (p1$)))))))

(defthmd lemma-16-4
  (implies (and (not (equal (p0) (p1)))
                (not (equal (ec+ (p0) (p1)) (ec- (p0)))))
           (equal (ec+ (ec- (p0)) (ec+ (p0) (p1)))
                  (p1)))
  :hints (("Goal" :use (lemma-16-3
                        (:instance ec+ec- (p (p0)))
                        (:instance p+q<>p (p (p0)) (q (p1)))
                        (:instance x= (r1 (p1)) (r2 (p0)))
                        (:instance x= (r1 (ec+ (p0) (p1))) (r2 (p0)))))))

(defthm lemma-16-5
  (implies (not (equal (ec+ (p0) (p1)) (ec- (p0))))
           (equal (ec+ (ec- (p0)) (ec+ (p0) (p1)))
                  (p1)))
  :hints (("Goal" :use (lemma-16-2 lemma-16-4))))

(defthm lemma-16-6
  (implies (and (ecp (cons a0 b0))
                (ecp (cons a1 b1))
                (not (equal (ec+ (cons a0 b0) (cons a1 b1)) (ec- (cons a0 b0))))) 
           (equal (ec+ (ec- (cons a0 b0)) (ec+ (cons a0 b0) (cons a1 b1)))
                  (cons a1 b1)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p0 p1 p2)
                  :use (ecp-assumption
                        (:functional-instance lemma-16-5 (p0 (lambda () (if (ecp (cons a0 b0)) (cons a0 b0) (p0))))
                                                      (p1 (lambda () (if (ecp (cons a1 b1)) (cons a1 b1) (p1))))
                                                      (x0 (lambda () (if (ecp (cons a0 b0)) a0 (x0))))
                                                      (x1 (lambda () (if (ecp (cons a1 b1)) a1 (x1))))
                                                      (y0 (lambda () (if (ecp (cons a0 b0)) b0 (y0))))
                                                      (y1 (lambda () (if (ecp (cons a1 b1)) b1 (y1)))))))))

(defthm lemma-16
  (implies (and (ecp p) (ecp q)
                (not (equal (ec+ p q) (ec- p))))
           (equal (ec+ (ec- p) (ec+ p q))
                  q))
  :rule-classes ()
  :hints (("Goal" :use (ecp-consp ec+ec-
                        (:instance ec-commutativity (q (ec- p)))
                        (:instance ecp-consp (p q))
                        (:instance lemma-16-6 (a0 (car p)) (b0 (cdr p)) (a1 (car q)) (b1 (cdr q)))))))

;; (P0 + O) + (P0 + O) = P0 + (O + (P0 + O))

(defthm comp-12
  (eq$ (dbl$ (sum$ (p0$) (o$)))
       (dbl$ (p0$)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable eq$ dbl$ sum$ p0$ o$))))

;; [0.01 seconds]

(defthm comp-13
  (eq$ (sum$ (o$) (sum$ (p0$) (o$)))
       (p0$))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable eq$ sum$ p0$ o$))))

;; [0.00 seconds]

(defthm ecp-x-0
  (implies (and (ecp p) (consp p) (= (car p) 0))
           (= (cdr p) 0))
  :hints (("Goal" :in-theory (enable ecp)
                  :use ((:instance mod-expt-0 (p (p)) (n (cdr p)) (k 2))))))

(defthmd lemma-17b-1
  (not (equal (ec+ (p0) (o))
              (o)))
  :hints (("Goal" :use ((:instance p+q<>p (p (o)) (q (p0)))
                        (:instance ec-commutativity (p (o)) (q (p0)))))))

(defthmd lemma-17b-2
  (ecp (cons (car (p0)) (cdr (p0))))
  :hints (("Goal" :in-theory (e/d (p0) (ecp-assumption)) :use (ecp-assumption))))

(defthmd lemma-17b-3
  (implies (equal (cdr (p0)) 0)
           (ecp (cons (car (p0)) 0)))
  :hints (("Goal" :use (lemma-17b-2))))

(defthmd lemma-17b-4
  (equal (ec+ (ec+ (p0) (o))
              (ec+ (p0) (o)))
         (ec+ (p0) (p0)))
  :hints (("Goal" :cases ((equal (p0) (o))) 
                  :use (comp-12 lemma-17b-1 lemma-17b-3
                        (:instance ec-x-0 (x (car (p0))))
                        (:instance ecp-x-0 (p (p0)))
                        (:instance eq$eq (p1 (dbl$ (sum$ (p0$) (o$))))
                                         (p2 (dbl$ (p0$))))))))

(defthmd lemma-17b-5
  (implies (not (equal (p0) (o)))
           (not (= (car (p0)) 0)))
  :hints (("Goal" :use ((:instance ecp-x-0 (p (p0)))))))

(defthm lemma-17b-6
  (implies (and (equal (car x) 0)
                (equal (cdr x) 0))
           (equal x (o)))
  :rule-classes ())

(defthmd lemma-17b-7
  (not (= (car (ec+ (o) (p0))) 0))
  :hints (("Goal" :use ((:instance ecp-x-0 (p (ec+ (o) (p0))))
                        (:instance ec-x-0 (x (car (ec+ (o) (p0)))))
                        (:instance lemma-17b-6 (x (ec+ (o) (p0))))
                        (:instance p+q<>p (p (o)) (q (p0)))))))

(defthmd lemma-17b-8
  (not (= (car (ec+ (p0) (o))) 0))
  :hints (("Goal" :use (lemma-17b-7
                        (:instance ec-commutativity (p (p0)) (q (o)))))))

(defthmd lemma-17b-9
  (equal (ec+ (o) (ec+ (p0) (o)))
         (p0))
  :hints (("Goal" :cases ((equal (p0) (o))) 
                  :use (comp-13 lemma-17b-1 lemma-17b-5 lemma-17b-8
                        (:instance eq$eq (p1 (sum$ (o$) (sum$ (p0$) (o$))))
                                         (p2 (p0$)))))))

(defthm lemma-17b-10
  (implies (ecp (cons a0 b0))
           (equal (ec+ (o) (ec+ (cons a0 b0) (o)))
                  (cons a0 b0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p0)
                  :use (ecp-assumption
                        (:functional-instance lemma-17b-9 (p0 (lambda () (if (ecp (cons a0 b0)) (cons a0 b0) (p0))))
                                                         (x0 (lambda () (if (ecp (cons a0 b0)) a0 (x0))))
                                                         (y0 (lambda () (if (ecp (cons a0 b0)) b0 (y0)))))))))

(defthm lemma-17b
  (implies (ecp p)
           (equal (ec+ (o) (ec+ p (o)))
                  p))
  :rule-classes ()
  :hints (("Goal" :use (ecp-consp
                        (:instance lemma-17b-10 (a0 (car p)) (b0 (cdr p)))))))


(defthmd lemma-22-1
  (equal (ec+ (ec+ (p0) (o))
              (ec+ (p0) (o)))
         (ec+ (p0) (ec+ (o) (ec+ (p0) (o)))))
  :hints (("Goal" :use (lemma-17b-4 lemma-17b-9))))

(defthm lemma-22-2
  (implies (ecp (cons a0 b0))
           (equal (ec+ (ec+ (cons a0 b0) (o))
                       (ec+ (cons a0 b0) (o)))
                  (ec+ (cons a0 b0) (ec+ (o) (ec+ (cons a0 b0) (o))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p0)
                  :use (ecp-assumption
                        (:functional-instance lemma-22-1 (p0 (lambda () (if (ecp (cons a0 b0)) (cons a0 b0) (p0))))
                                                          (x0 (lambda () (if (ecp (cons a0 b0)) a0 (x0))))
                                                          (y0 (lambda () (if (ecp (cons a0 b0)) b0 (y0)))))))))

(defthm lemma-22
  (implies (ecp p)
           (equal (ec+ (ec+ p (o))
                       (ec+ p (o)))
                  (ec+ p (ec+ (o) (ec+ p (o))))))
  :rule-classes ()
  :hints (("Goal" :use (ecp-consp
                        (:instance lemma-22-2 (a0 (car p)) (b0 (cdr p)))))))

;; P0 <> +-P1 and P0 + P1 <> +-P2 and P0 <> +-P2 and P0 + P2 <> +-P1 => P2 + (P0 + P1) = P1 + (P0 + P2)

(defthm comp-7
  (eq$ (sum$ (p2$) (sum$ (p0$) (p1$)))             
       (sum$ (p1$) (sum$ (p0$) (p2$))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable eq$ sum$ p0$ p1$ p2$))))

;; [3.94 seconds]

(defthmd lemma-17-1
  (implies (and (not (equal (x (p0)) (x (p1))))
                (not (equal (x (p0)) (x (p2))))
                (not (equal (x (p2)) (x (ec+ (p0) (p1)))))
                (not (equal (x (p1)) (x (ec+ (p0) (p2))))))
           (equal (ec+ (p2) (ec+ (p0) (p1)))
                  (ec+ (p1) (ec+ (p0) (p2)))))
  :hints (("Goal" :use (comp-7
                        (:instance eq$eq (p1 (sum$ (p2$) (sum$ (p0$) (p1$))))
                                         (p2 (sum$ (p1$) (sum$ (p0$) (p2$)))))))))

(defthmd lemma-17-2
  (implies (and (not (equal (p0) (p1)))
                (not (equal (p0) (ec- (p1))))
                (not (equal (p0) (p2)))
                (not (equal (p0) (ec- (p2))))
                (not (equal (ec+ (p0) (p1)) (p2)))
                (not (equal (ec+ (p0) (p1)) (ec- (p2))))
                (not (equal (ec+ (p0) (p2)) (p1)))
                (not (equal (ec+ (p0) (p2)) (ec- (p1)))))
           (equal (ec+ (p2) (ec+ (p0) (p1)))
                  (ec+ (p1) (ec+ (p0) (p2)))))
  :hints (("Goal" :use (lemma-17-1
                        (:instance x= (r1 (p0)) (r2 (p1)))
                        (:instance x= (r1 (p0)) (r2 (p2)))
                        (:instance x= (r1 (ec+ (p0) (p1))) (r2 (p2)))
                        (:instance x= (r1 (ec+ (p0) (p2))) (r2 (p1)))))))

(defthmd lemma-17-3
  (implies (and (equal (p0) (ec- (p1)))
                (not (equal (ec+ (p0) (p2)) (p1))))
           (equal (ec+ (p2) (ec+ (p0) (p1)))
                  (ec+ (p1) (ec+ (p0) (p2)))))
  :hints (("Goal" :use ((:instance lemma-16 (p (p0)) (q (p2)))
                        (:instance ec-inverse-unique (r1 (p0)) (r2 (p1)))
                        (:instance ec-- (r (p1)))))))

(defthmd lemma-17-4
  (implies (and (equal (p0) (ec- (p2)))
                (not (equal (ec+ (p0) (p1)) (p2))))
           (equal (ec+ (p2) (ec+ (p0) (p1)))
                  (ec+ (p1) (ec+ (p0) (p2)))))
  :hints (("Goal" :use ((:instance lemma-16 (p (p0)) (q (p1)))
                        (:instance ec-inverse-unique (r1 (p0)) (r2 (p2)))
                        (:instance ec-- (r (p2)))))))

(defthmd lemma-17-5
  (implies (and (not (equal (p0) (p1)))
                (not (equal (p0) (p2)))
                (not (equal (ec+ (p0) (p1)) (p2)))
                (not (equal (ec+ (p0) (p1)) (ec- (p2))))
                (not (equal (ec+ (p0) (p2)) (p1)))
                (not (equal (ec+ (p0) (p2)) (ec- (p1)))))
           (equal (ec+ (p2) (ec+ (p0) (p1)))
                  (ec+ (p1) (ec+ (p0) (p2)))))
  :hints (("Goal" :use (lemma-17-2 lemma-17-3 lemma-17-4))))

(defthm lemma-17-6
  (implies (and (ecp (cons a0 b0))
                (ecp (cons a1 b1))
                (ecp (cons a2 b2))
                (not (equal (cons a0 b0) (cons a1 b1)))
                (not (equal (cons a0 b0) (cons a2 b2)))
                (not (equal (ec+ (cons a0 b0) (cons a1 b1)) (cons a2 b2)))
                (not (equal (ec+ (cons a0 b0) (cons a1 b1)) (ec- (cons a2 b2))))
                (not (equal (ec+ (cons a0 b0) (cons a2 b2)) (cons a1 b1)))
                (not (equal (ec+ (cons a0 b0) (cons a2 b2)) (ec- (cons a1 b1)))))
           (equal (ec+ (cons a2 b2) (ec+ (cons a0 b0) (cons a1 b1)))
                  (ec+ (cons a1 b1) (ec+ (cons a0 b0) (cons a2 b2)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p0 p1 p2)
                  :use (ecp-assumption
                        (:functional-instance lemma-17-5 (p0 (lambda () (if (ecp (cons a0 b0)) (cons a0 b0) (p0))))
                                                         (p1 (lambda () (if (ecp (cons a1 b1)) (cons a1 b1) (p1))))
                                                         (p2 (lambda () (if (ecp (cons a2 b2)) (cons a2 b2) (p2))))
                                                         (x0 (lambda () (if (ecp (cons a0 b0)) a0 (x0))))
                                                         (x1 (lambda () (if (ecp (cons a1 b1)) a1 (x1))))
                                                         (x2 (lambda () (if (ecp (cons a2 b2)) a2 (x2))))
                                                         (y0 (lambda () (if (ecp (cons a0 b0)) b0 (y0))))
                                                         (y1 (lambda () (if (ecp (cons a1 b1)) b1 (y1))))
                                                         (y2 (lambda () (if (ecp (cons a2 b2)) b2 (y2)))))))))

(defthm lemma-17-7
  (implies (and (ecp p) (ecp q) (ecp r)
                (not (equal p q))
                (not (equal p r))
                (not (equal (ec+ p q) r))
                (not (equal (ec+ p q) (ec- r)))
                (not (equal (ec+ p r) q))
                (not (equal (ec+ p r) (ec- q))))
           (equal (ec+ r (ec+ p q))
                  (ec+ q (ec+ p r))))
  :rule-classes ()
  :hints (("Goal" :use (ecp-consp ec-commutativity
                        (:instance ec-commutativity (q r))
                        (:instance ec-commutativity (p r))
                        (:instance ecp-consp (p q))
                        (:instance ecp-consp (p r))
                        (:instance lemma-17-6 (a0 (car p)) (b0 (cdr p)) (a1 (car q)) (b1 (cdr q)) (a2 (car r)) (b2 (cdr r)))))))

;; P0 <> +-P1 and P0 + P0 <> +-P1 and P0 + P1 <> -P0 => P1 + (P0 + P0) = P0 + (P0 + P1)

(defthm comp-8
  (eq$ (sum$ (p1$) (dbl$ (p0$)))
       (sum$ (p0$) (sum$ (p0$) (p1$))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable eq$ dbl$ sum$ p0$ p1$))))

;; [0.36 seconds}

(defthmd lemma-17-8
  (implies (and (not (equal (x (p0)) (x (p1))))
                (not (equal (x (p0)) (x (ec+ (p0) (p1)))))
                (not (equal (x (p1)) (x (ec+ (p0) (p0)))))
                (not (equal (p0) (o))))
           (equal (ec+ (p1) (ec+ (p0) (p0)))
                  (ec+ (p0) (ec+ (p0) (p1)))))
  :hints (("Goal" :use (comp-8
                        (:instance eq$eq (p1 (sum$ (p1$) (dbl$ (p0$))))
                                         (p2 (sum$ (p0$) (sum$ (p0$) (p1$)))))))))

(defthmd lemma-17-9
  (implies (and (not (equal (p0) (p1)))
                (not (equal (p0) (ec- (p1))))
                (not (equal (ec- (p0)) (ec+ (p0) (p1))))
                (not (equal (ec+ (p0) (p0)) (p1)))
                (not (equal (ec+ (p0) (p0)) (ec- (p1))))
                (not (equal (p0) (o))))
           (equal (ec+ (p1) (ec+ (p0) (p0)))
                  (ec+ (p0) (ec+ (p0) (p1)))))
  :hints (("Goal" :use (lemma-17-8
                        (:instance ec+ec-2 (p (p1)) (q (p0)))
                        (:instance ec+ec-2 (p (p0)) (q (p0)))
                        (:instance p+q<>p (p (p0)) (q (p1)))
                        (:instance x= (r1 (p0)) (r2 (p1)))
                        (:instance x= (r1 (ec+ (p0) (p1))) (r2 (p0)))
                        (:instance x= (r1 (ec+ (p0) (p0))) (r2 (p1)))))))

(defthmd lemma-17-10
  (implies (equal (p0) (o))
           (equal (ec+ (p1) (ec+ (p0) (p0)))
                  (ec+ (p0) (ec+ (p0) (p1)))))
  :hints (("Goal" :use (lemma-16-5
                        (:instance p+q<>p (p (p0)) (q (p1)))))))

(defthmd lemma-17-11
  (implies (and (not (equal (p0) (p1)))
                (not (equal (p0) (ec- (p1))))
                (not (equal (ec- (p0)) (ec+ (p0) (p1))))
                (not (equal (ec+ (p0) (p0)) (p1)))
                (not (equal (ec+ (p0) (p0)) (ec- (p1)))))
           (equal (ec+ (p1) (ec+ (p0) (p0)))
                  (ec+ (p0) (ec+ (p0) (p1)))))
  :hints (("Goal" :use (lemma-17-9 lemma-17-10))))

(defthm lemma-17-12
  (implies (and (ecp (cons a0 b0))
                (ecp (cons a1 b1))
                (not (equal (cons a0 b0) (cons a1 b1)))
                (not (equal (cons a0 b0) (ec- (cons a1 b1))))
                (not (equal (ec- (cons a0 b0)) (ec+ (cons a0 b0) (cons a1 b1))))
                (not (equal (ec+ (cons a0 b0) (cons a0 b0)) (cons a1 b1)))
                (not (equal (ec+ (cons a0 b0) (cons a0 b0)) (ec- (cons a1 b1)))))
           (equal (ec+ (cons a1 b1) (ec+ (cons a0 b0) (cons a0 b0)))
                  (ec+ (cons a0 b0) (ec+ (cons a0 b0) (cons a1 b1)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p0 p1 p2)
                  :use (ecp-assumption
                        (:functional-instance lemma-17-11 (p0 (lambda () (if (ecp (cons a0 b0)) (cons a0 b0) (p0))))
                                                      (p1 (lambda () (if (ecp (cons a1 b1)) (cons a1 b1) (p1))))
                                                      (p2 (lambda () (if (ecp (cons a2 b2)) (cons a2 b2) (p2))))
                                                      (x0 (lambda () (if (ecp (cons a0 b0)) a0 (x0))))
                                                      (x1 (lambda () (if (ecp (cons a1 b1)) a1 (x1))))
                                                      (x2 (lambda () (if (ecp (cons a2 b2)) a2 (x2))))
                                                      (y0 (lambda () (if (ecp (cons a0 b0)) b0 (y0))))
                                                      (y1 (lambda () (if (ecp (cons a1 b1)) b1 (y1))))
                                                      (y2 (lambda () (if (ecp (cons a2 b2)) b2 (y2)))))))))

(defthm lemma-17-13
  (implies (and (ecp p)
                (ecp q)
                (not (equal p (ec- q)))
                (not (equal (ec- p) (ec+ p q)))
                (not (equal (ec+ p p) q))
                (not (equal (ec+ p p) (ec- q))))
           (equal (ec+ q (ec+ p p))
                  (ec+ p (ec+ p q))))
  :rule-classes ()
  :hints (("Goal" :use (ecp-consp ec-commutativity 
                        (:instance ecp-consp (p q))
                        (:instance lemma-17-12 (a0 (car p)) (b0 (cdr p)) (a1 (car q)) (b1 (cdr q)))))))

(defthm lemma-17-14
  (implies (and (ecp p)
                (ecp q)
                (equal p (ec- q))
                (not (equal (ec+ p p) q)))
           (equal (ec+ q (ec+ p p))
                  (ec+ p (ec+ p q))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance ec-- (r q))
                        (:instance lemma-16 (q p))
                        (:instance ec-inverse-unique (r1 p) (r2 q))))))

(defthm lemma-17-15
  (implies (and (ecp p)
                (ecp q)
                (not (equal (ec- p) (ec+ p q)))
                (not (equal (ec+ p p) q))
                (not (equal (ec+ p p) (ec- q))))
           (equal (ec+ q (ec+ p p))
                  (ec+ p (ec+ p q))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-17-13 lemma-17-14))))

(defthm lemma-17
  (implies (and (ecp p) (ecp q) (ecp r)
                (not (equal (ec+ p q) r))
                (not (equal (ec+ p q) (ec- r)))
                (not (equal (ec+ p r) q))
                (not (equal (ec+ p r) (ec- q))))
           (equal (ec+ r (ec+ p q))
                  (ec+ q (ec+ p r))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-17-7 lemma-17-15 (:instance lemma-17-15 (q r))))))

;; (P0 + P0 <> -P0 and (P0 + P0) + P0 <> -P0 => (P0 + P0) + (P0 + P0) = P0 + (P0 + (P0 + P0))

(defthm comp-9
  (eq$ (dbl$ (dbl$ (p0$)))
       (sum$ (p0$) (sum$ (p0$) (dbl$ (p0$)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable eq$ dbl$ sum$ p0$ p1$))))

;; [0.22 seconds]

(defthmd lemma-18-1
  (implies (and (not (equal (ec+ (p0) (p0)) (o)))
                (not (equal (x (p0)) (x (ec+ (p0) (p0)))))
                (not (equal (x (p0)) (x (ec+ (p0) (ec+ (p0) (p0)))))))
           (equal (ec+ (ec+ (p0) (p0)) (ec+ (p0) (p0)))
                  (ec+ (p0) (ec+ (p0) (ec+ (p0) (p0))))))
  :hints (("Goal" :cases ((equal (p0) (o)))
                  :use (comp-9
                        (:instance eq$eq (p1 (dbl$ (dbl$ (p0$))))
                                         (p2 (sum$ (p0$) (sum$ (p0$) (dbl$ (p0$))))))))))


;; P0 <> +-P1 and (P0 + P1 <> -P0 and (P0 + P1) + P0 <> +-P1 => (P0 + P1) + (P0 + P1) = P0 + (P1 + (P0 + P1))

(defthm comp-10
  (eq$ (dbl$ (sum$ (p0$) (p1$)))
       (sum$ (p0$) (sum$ (p1$) (sum$ (p0$) (p1$)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable eq$ dbl$ sum$ p0$ p1$))))

;; [26.23 seconds}

(defthmd lemma-18-2
  (implies (and (not (equal (x (p0)) (x (p1))))
                (not (equal (ec+ (p0) (p1)) (o)))
                (not (equal (x (p1)) (x (ec+ (p0) (p1)))))
                (not (equal (x (p0)) (x (ec+ (p1) (ec+ (p0) (p1)))))))
           (equal (ec+ (ec+ (p0) (p1)) (ec+ (p0) (p1)))
                  (ec+ (p0) (ec+ (p1) (ec+ (p0) (p1))))))
  :hints (("Goal" :use (comp-10
                        (:instance eq$eq (p1 (dbl$ (sum$ (p0$) (p1$))))
                                         (p2 (sum$ (p0$) (sum$ (p1$) (sum$ (p0$) (p1$))))))))))

(defthmd lemma-18-3
  (equal (ec+ (ec+ (p0) (ec- (p0))) (ec+ (p0) (ec- (p0))))
         (ec+ (p0) (ec+ (ec- (p0)) (ec+ (p0) (ec- (p0))))))
  :hints (("Goal" :use ((:instance ec-inverse-unique (r1 (p0)) (r2 (ec- (p0))))))))

(defthmd lemma-18-4
  (implies (and (not (equal (p0) (p1)))
                (not (equal (ec+ (p0) (p1)) (o)))
                (not (equal (x (p1)) (x (ec+ (p0) (p1)))))
                (not (equal (x (p0)) (x (ec+ (p1) (ec+ (p0) (p1)))))))
           (equal (ec+ (ec+ (p0) (p1)) (ec+ (p0) (p1)))
                  (ec+ (p0) (ec+ (p1) (ec+ (p0) (p1))))))
  :hints (("Goal" :use (lemma-18-2 lemma-18-3
                        (:instance ec-- (r (p1)))
                        (:instance x= (r1 (p0)) (r2 (p1)))))))

(defthmd lemma-18-5
  (implies (and (not (equal (ec+ (p0) (p1)) (o)))
                (not (equal (x (p1)) (x (ec+ (p0) (p1)))))
                (not (equal (x (p0)) (x (ec+ (p1) (ec+ (p0) (p1)))))))
           (equal (ec+ (ec+ (p0) (p1)) (ec+ (p0) (p1)))
                  (ec+ (p0) (ec+ (p1) (ec+ (p0) (p1))))))
  :hints (("Goal" :use (lemma-18-4 lemma-18-1))))

(defthm lemma-18-6
  (implies (and (ecp (cons a0 b0))
                (ecp (cons a1 b1))
                (not (equal (ec+ (cons a0 b0) (cons a1 b1)) (o)))
                (not (equal (x (cons a1 b1)) (x (ec+ (cons a0 b0) (cons a1 b1)))))
                (not (equal (x (cons a0 b0)) (x (ec+ (cons a1 b1) (ec+ (cons a0 b0) (cons a1 b1)))))))
           (equal (ec+ (ec+ (cons a0 b0) (cons a1 b1)) (ec+ (cons a0 b0) (cons a1 b1)))
                  (ec+ (cons a0 b0) (ec+ (cons a1 b1) (ec+ (cons a0 b0) (cons a1 b1))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p0 p1 p2)
                  :use (ecp-assumption
                        (:functional-instance lemma-18-5 (p0 (lambda () (if (ecp (cons a0 b0)) (cons a0 b0) (p0))))
                                                      (p1 (lambda () (if (ecp (cons a1 b1)) (cons a1 b1) (p1))))
                                                      (x0 (lambda () (if (ecp (cons a0 b0)) a0 (x0))))
                                                      (x1 (lambda () (if (ecp (cons a1 b1)) a1 (x1))))
                                                      (y0 (lambda () (if (ecp (cons a0 b0)) b0 (y0))))
                                                      (y1 (lambda () (if (ecp (cons a1 b1)) b1 (y1)))))))))

(defthm lemma-18-7
  (implies (and (ecp p) (ecp q)
                (not (equal (ec+ p q) (o)))
                (not (equal (x q) (x (ec+ p q))))
                (not (equal (x p) (x (ec+ q (ec+ p q))))))
           (equal (ec+ (ec+ p q) (ec+ p q))
                  (ec+ p (ec+ q (ec+ p q)))))
  :rule-classes ()
  :hints (("Goal" :use (ecp-consp
                        (:instance ecp-consp (p q))
                        (:instance lemma-18-6 (a0 (car p)) (b0 (cdr p)) (a1 (car q)) (b1 (cdr q)))))))

(defthmd lemma-18-8
  (implies (and (ecp p) (ecp q) (consp p) (consp q)
                (equal (ec+ p q) (o)))
           (not (equal p (o))))
  :hints (("Goal" :use (p+q<>p))))

(defthmd lemma-18-9
  (implies (and (ecp p) (ecp q) (consp p) (consp q)
                (equal (ec+ p q) (o)))
           (not (equal (ec- p) (o))))
  :hints (("Goal" :use (lemma-18-8 (:instance ec-- (r p))))))

(defthm lemma-18-10
  (implies (and (ecp p) (ecp q) (consp p) (consp q)
                (equal (ec+ p q) (o)))
           (equal q (ec+ (ec- p) (o))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-18-9 lemma-16))))

(defthmd lemma-18-11
  (implies (and (ecp p) (ecp q) (consp p) (consp q)
                (equal (ec+ p q) (o)))
           (equal (ec+ (o) q)
                  (ec- p)))
  :hints (("Goal" :use (lemma-18-10 (:instance lemma-17b (p (ec- p)))))))

(defthmd lemma-18-12
  (implies (and (ecp p) (ecp q) (consp p) (consp q)
                (equal (ec+ p q) (o)))
           (equal (ec+ p (ec+ (o) q))
                  (inf)))
  :hints (("Goal" :use (lemma-18-11 (:instance ec-inverse-unique (r1 p) (r2 (ec+ (o) q)))))))

(defthmd lemma-18-13
  (implies (and (ecp p) (ecp q)
                (equal (ec+ p q) (o)))
           (equal (ec+ p (ec+ (o) q))
                  (inf)))
  :hints (("Goal" :in-theory (enable ecp) :use (lemma-18-12))))

(defthm lemma-18-14
  (implies (and (ecp p) (ecp q)
                (equal (ec+ p q) (o)))
           (equal (ec+ (ec+ p q) (ec+ p q))
                  (ec+ p (ec+ q (ec+ p q)))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-18-13
                        (:instance ec-commutativity (p (o)))))))

(defthm lemma-18-15
  (implies (and (ecp p) (ecp q)
                (not (equal (x q) (x (ec+ p q))))
                (not (equal (x p) (x (ec+ q (ec+ p q))))))
           (equal (ec+ (ec+ p q) (ec+ p q))
                  (ec+ p (ec+ q (ec+ p q)))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-18-7 lemma-18-14))))

(defthm lemma-18-16
  (implies (and (ecp p) (ecp q)
                (not (equal (ec+ p q) q))
                (not (equal (ec+ p q) (ec- q)))
                (not (equal (ec+ q (ec+ p q)) p))
                (not (equal (ec+ q (ec+ p q)) (ec- p))))
           (equal (ec+ (ec+ p q) (ec+ p q))
                  (ec+ p (ec+ q (ec+ p q)))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-18-15
                        (:instance x= (r2 q) (r1 (ec+ p q)))
                        (:instance x= (r2 p) (r1 (ec+ q (ec+ p q))))))))

(defthm lemma-18-17
  (implies (and (ecp p) (ecp q)
                (equal p (inf)))
           (equal (ec+ (ec+ p q) (ec+ p q))
                  (ec+ p (ec+ q (ec+ p q)))))
  :rule-classes ())

(defthm lemma-18-18
  (implies (and (ecp p) (ecp q)
                (not (equal p (inf))))
           (not (equal (ec+ p q) q)))
  :rule-classes ()
  :hints (("Goal" :use (ec-commutativity (:instance p+q<>p (p q) (q p))))))

(defthm lemma-18
  (implies (and (ecp p) (ecp q)
                (not (equal (ec+ p q) (ec- q)))
                (not (equal (ec+ q (ec+ p q)) p))
                (not (equal (ec+ q (ec+ p q)) (ec- p))))
           (equal (ec+ (ec+ p q) (ec+ p q))
                  (ec+ p (ec+ q (ec+ p q)))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-18-16 lemma-18-17 lemma-18-18))))


;; P0 + P1 = -P0 => P1 = -(P0 + P0)

(defun phi ()
  (let* ((s (sum$ (p0$) (p1$)))
         (u (car s))
         (z (caddr s)))
    `(- (expt (+ (- ,u (* x0 (expt ,z 2)))
                 (* 2 (* y0 y1)))
              2)
        (expt (* 2 (* y0 y1)) 2))))

(defun psi ()
  (let* ((s (sum$ (p0$) (p1$)))
         (d (dbl$ (p0$)))
         (zs (caddr s))
         (ud (car d))
         (zd (caddr d)))
    `(* (- ,ud (* x1 (expt ,zd 2)))
        (expt ,zs 2))))

(defthm comp-11
  (equal (reduce$ (phi))
         (reduce$ (psi)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable dbl$ sum$ p0$ p1$))))

;; [0.01 seconds}

(defthmd lemma-19-1
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (equal (p0) (p1)))
           (equal (p1) (ec- (ec+ (p0) (p1)))))
  :hints (("Goal" :use ((:instance ec-- (r (p0)))))))

(defthmd lemma-19-2
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (equal (p0) (ec- (p1))))
           (equal (ec- (p0)) (inf)))
  :hints (("Goal" :use ((:instance ec-inverse-unique (r1 (ec- (p1))) (r2 (p1)))
                        (:instance ec-- (r (p1)))))))

(defthmd lemma-19-3
  (implies (equal (ec+ (p0) (p1)) (ec- (p0)))
           (not (equal (p0) (ec- (p1)))))
  :hints (("Goal" :use (lemma-19-2
                        (:instance ec-- (r (p0)))))))

(defthmd lemma-19-4
  (implies (equal (ec+ (p0) (p1)) (ec- (p0)))
           (not (equal (p0) (o))))
  :hints (("Goal" :use ((:instance p+q<>p (p (p0)) (q (p1)))))))

(defthmd lemma-19-5
  (implies (equal (ec+ (p0) (p1)) (ec- (p0)))
           (not (equal (car (p0)) 0)))
  :hints (("Goal" :use (lemma-19-4 (:instance ecp-x-0 (p (p0)))))))

(defthmd lemma-19-6
  (implies (equal (cdr (p0)) 0)
           (equal (car (p0)) 0))
  :hints (("Goal" :in-theory (e/d (p0) (ecp-lemma ecp-assumption))
                  :use (ecp-assumption (:instance ec-x-0 (x (car (p0))))))))

(defthmd lemma-19-7
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (and (not (= (x0) (x1)))
                (not (= (x0) 0))
                (not (= (y0) 0))))
  :hints (("Goal" :in-theory (enable p0 p1)
                  :use (lemma-19-3 lemma-19-5 lemma-19-6
                        (:instance x= (r2 (p1)) (r1 (p0)))))))

(defun us$ () (car (sum$ (p0$) (p1$))))
(defun vs$ () (cadr (sum$ (p0$) (p1$))))
(defun zs$ () (caddr (sum$ (p0$) (p1$))))
(defun ud$ () (car (dbl$ (p0$))))
(defun vd$ () (cadr (dbl$ (p0$))))
(defun zd$ () (caddr (dbl$ (p0$))))

(defun ms () (evalp$ (us$)))
(defun ns () (evalp$ (vs$)))
(defun zs () (evalp$ (zs$)))
(defun md () (evalp$ (ud$)))
(defun nd () (evalp$ (vd$)))
(defun zd () (evalp$ (zd$)))

(local-defthmd car-cons-open
  (equal (car (cons x y)) x))

(local-defthmd cdr-cons-open
  (equal (cdr (cons x y)) y))

(local (deftheory theory$
  (union-theories '(car-cons-open cdr-cons-open vlist assoc-equal vars vals pairlis$ phi psi eval3$ evalp$ evalp us$ vs$ zs$ ud$ vd$ zd$ ms ns zs md nd zd)
                  (theory 'minimal-theory))))

(defthm evalp$phi
  (equal (evalp$ (phi))
         (- (expt (+ (- (ms) (* (x0) (expt (zs) 2)))
                     (* 2 (* (y0) (y1))))
                  2)
            (expt (* 2 (* (y0) (y1))) 2)))
  :hints (("Goal" :in-theory (theory 'theory$))))

(defthm evalp$psi
  (equal (evalp$ (psi))
         (* (- (md) (* (x1) (expt (zd) 2)))
            (expt (zs) 2)))
  :hints (("Goal" :in-theory (theory 'theory$))))

(defthmd lemma-19-8
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (not (equal (car (p0)) (car (p1)))))
  :hints (("Goal" :use (lemma-19-7) :in-theory (enable p0 p1))))

(defthmd lemma-19-9
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (tripp$ (sum$ (p0$) (p1$))))
  :hints (("Goal" :use (lemma-19-8))))

(defthmd lemma-19-10
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (equal (decode3$ (sum$ (p0$) (p1$)))
                  (ec- (p0))))
  :hints (("Goal" :use (lemma-19-8))))

(defthmd lemma-19-11
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (equal (car (decode3$ (sum$ (p0$) (p1$))))
                  (x0)))
  :hints (("Goal" :in-theory (enable ec- p0) :use (lemma-19-10))))

(in-theory (disable (us$) (vs$) (zs$) (ud$) (vd$) (zd$)))

(defthmd lemma-19-12
  (implies (tripp$ (sum$ (p0$) (p1$)))
           (equal (car (decode3$ (sum$ (p0$) (p1$))))
                  (f/ (ms) (expt (zs) 2))))
  :hints (("Goal" :in-theory (enable tripp$ decode3$ decode3 dx))))

(defthmd lemma-19-13
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (equal (mod (* (ms) (frcp (expt (zs) 2))) (p))
                  (x0)))
  :hints (("Goal" :use (lemma-19-11 lemma-19-12 lemma-19-9))))

(defthmd lemma-19-14
  (implies (and (tripp$ (sum$ (p0$) (p1$)))
                (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (equal (mod (* (ms) (frcp (expt (zs) 2)) (expt (zs) 2)) (p))
                  (mod (* (x0) (expt (zs) 2)) (p))))
  :hints (("Goal" :in-theory (enable tripp$)
                  :use (lemma-19-13
                        (:instance mod-times-mod (a (* (ms) (frcp (expt (zs) 2)))) (b (x0)) (c (expt (zs) 2)) (n (p)))))))

(defthmd lemma-19-15
  (implies (and (tripp$ (sum$ (p0$) (p1$)))
                (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (equal (mod (* (ms) (frcp (expt (zs) 2)) (expt (zs) 2)) (p))
                  (mod (ms) (p))))
  :hints (("Goal" :in-theory (enable tripp$)
                  :use ((:instance frcp-cor (m (ms)) (n (expt (zs) 2)))
                        (:instance mod-expt-0 (n (zs)) (k 2) (p (p)))))))

(defthmd lemma-19-16
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (equal (mod (ms) (p))
                  (mod (* (x0) (expt (zs) 2)) (p))))
  :hints (("Goal" :use (lemma-19-14 lemma-19-15 lemma-19-9))))

(defthm lemma-19-17
  (implies (and (integerp a) (integerp b) (= (mod a (p)) 0))
           (= (mod (- (expt (+ a b) 2) (expt b 2)) (p)) 0))
  :rule-classes ())

(defthm lemma-19-18
  (implies (and (integerp a) (integerp b))
           (= (mod (- a b) (p))
              (mod (- (mod a (p)) (mod b (p))) (p))))
  :rule-classes ())

(defthm lemma-19-19
  (implies (and (integerp a) (integerp b) (integerp c) (= (mod a (p)) (mod b (p))))
           (= (mod (- (expt (+ (- a b) c) 2) (expt c 2)) (p)) 0))
  :rule-classes ()
  :hints (("Goal" :use (lemma-19-18 (:instance lemma-19-17 (a (- a b)) (b c))))))

(in-theory (disable (phi) phi))

(defthmd lemma-19-20
  (implies (and (tripp$ (sum$ (p0$) (p1$)))
                (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (equal (mod (evalp$ (phi)) (p))
                  0))
  :hints (("Goal" :use (lemma-19-16
                        (:instance lemma-19-19 (a (ms)) (b (* (x0) (expt (zs) 2))) (c (* 2 (* (y0) (y1))))))
                  :in-theory (enable tripp$))))

(defthm lemma-19-21
  (implies (tripp$ (sum$ (p0$) (p1$)))
           (polyp$ (phi)))
  :hints (("Goal" :in-theory (enable tripp$ phi) :expand (:free (x) (polyp$ x)))))

(defthm lemma-19-22
  (implies (tripp$ (sum$ (p0$) (p1$)))
           (polyp$ (psi)))
  :hints (("Goal" :in-theory (enable tripp$ psi) :expand (:free (x) (polyp$ x)))))

(in-theory (disable (polyp$) (reduce$) evalp$phi evalp$psi (psi) psi))

(defthmd lemma-19-23
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (equal (mod (evalp$ (psi)) (p))
                  0))
  :hints (("Goal" :use (comp-11
                        (:instance reduce$-correct (x (psi)))
                        (:instance reduce$-correct (x (phi))))
                  :in-theory (enable lemma-19-9 lemma-19-20))))

(defthmd lemma-19-24
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (not (= (mod (expt (zs) 2) (p))
                   0)))
  :hints (("Goal" :use (lemma-19-9
                        (:instance mod-expt-0 (n (zs)) (k 2) (p (p))))
                  :in-theory (enable tripp$))))

(defthmd lemma-19-25
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (not (equal (p0) (o))))
  :hints (("Goal" :use ((:instance ec-commutativity (p (o)) (q (p1)))
                        (:instance p+q<>p (p (o)) (q (p1))))
                  :in-theory (enable ec-))))

(defthmd lemma-19-26
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (tripp$ (dbl$ (p0$))))
  :hints (("Goal" :use (lemma-19-25))))

(defthmd lemma-19-27
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (= (mod (- (md) (* (x1) (expt (zd) 2))) (p))
                   0))
  :hints (("Goal" :use (lemma-19-9 lemma-19-23 lemma-19-24 lemma-19-26
                        (:instance mod*0 (n (- (md) (* (x1) (expt (zd) 2)))) (m (expt (zs) 2))))
                  :in-theory (enable evalp$psi tripp$))))

(defthmd lemma-19-28
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (= (mod (md) (p))
              (mod (* (x1) (expt (zd) 2)) (p))))
  :hints (("Goal" :use (lemma-19-9 lemma-19-27 lemma-19-26
                        (:instance mod-equal-0 (a (md)) (n (p)) (b (* (x1) (expt (zd) 2)))))
                  :in-theory (enable tripp$))))

(defthmd lemma-19-29
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (= (mod (* (md) (frcp (expt (zd) 2))) (p))
              (mod (* (x1) (expt (zd) 2) (frcp (expt (zd) 2))) (p))))
  :hints (("Goal" :use (lemma-19-9 lemma-19-28 lemma-19-26
                        (:instance mod-times-mod (a (md)) (b (* (x1) (expt (zd) 2))) (c (frcp (expt (zd) 2))) (n (p))))
                  :in-theory (enable tripp$))))

(defthmd lemma-19-30
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (= (mod (x1) (p))
              (mod (* (x1) (expt (zd) 2) (frcp (expt (zd) 2))) (p))))
  :hints (("Goal" :use (lemma-19-9 lemma-19-26
                        (:instance frcp-cor (m (x1)) (n (expt (zd) 2)))
                        (:instance mod-expt-0 (n (zd)) (k 2) (p (p))))
                  :in-theory (enable tripp$))))

(defthmd lemma-19-31
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (= (mod (* (md) (frcp (expt (zd) 2))) (p))
              (x1)))
  :hints (("Goal" :use (lemma-19-29 lemma-19-30))))

(defthmd lemma-19-32
  (implies (tripp$ (dbl$ (p0$)))
           (equal (car (decode3$ (dbl$ (p0$))))
                  (mod (* (md) (frcp (expt (zd) 2))) (p))))
  :hints (("Goal" :in-theory (enable tripp$ decode3$ decode3 dx))))

(defthmd lemma-19-33
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (equal (car (decode3$ (dbl$ (p0$))))
                  (x1)))
  :hints (("Goal" :in-theory (enable p1) :use (lemma-19-26 lemma-19-31 lemma-19-32))))

(defthmd lemma-19-33
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (equal (car (decode3$ (dbl$ (p0$))))
                  (x1)))
  :hints (("Goal" :in-theory (enable p1) :use (lemma-19-26 lemma-19-31 lemma-19-32))))

(defthmd lemma-19-34
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (equal (car (ec+ (p0) (p0)))
                  (x1)))
  :hints (("Goal" :use (lemma-19-25 lemma-19-33))))

(defthmd lemma-19-35
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (equal (car (ec+ (p0) (p0)))
                  (car (p1))))
  :hints (("Goal" :use (lemma-19-34) :in-theory (enable p1))))

(defthm lemma-19-36
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1))))
           (or (equal (ec+ (p0) (p0)) (p1))
               (equal (ec+ (p0) (p0)) (ec- (p1)))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-19-35
                        (:instance x= (r1 (ec+ (p0) (p0))) (r2 (p1)))))))

(defthm lemma-19-37
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1)))
                (equal (ec+ (p0) (p0)) (p1)))
           (equal (ec+ (ec- (p0)) (ec+ (p0) (p0)))
                  (p0)))                  
  :rule-classes ()
  :hints (("Goal" :use (lemma-19-3
                        (:instance ec-- (r (p0)))
                        (:instance lemma-16 (p (p0)) (q (p0)))))))

(defthm lemma-19-38
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1)))
                (equal (ec+ (p0) (p0)) (p1)))
           (equal (ec+ (p1) (ec- (p0)))
                  (p0)))                  
  :rule-classes ()
  :hints (("Goal" :use (lemma-19-37
                        (:instance ec-commutativity (q (p1)) (p (ec- (p0))))))))

(defthm lemma-19-39
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1)))
                (equal (ec+ (p0) (p0)) (p1)))
           (equal (ec+ (p0) (ec- (p1)))
                  (ec- (ec+ (ec- (p0)) (p1)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance lemma-15 (p (ec- (p0))) (q (p1)))
                        (:instance ec-- (r (p0)))
                        (:instance ec-- (r (p1)))))))

(defthm lemma-19-40
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1)))
                (equal (ec+ (p0) (p0)) (p1)))
           (equal (ec+ (ec- (p0)) (p1))
                  (p0)))                  
  :rule-classes ()
  :hints (("Goal" :use (lemma-19-38
                        (:instance ec-commutativity (q (p1)) (p (ec- (p0))))))))

(defthm lemma-19-41
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1)))
                (equal (ec+ (p0) (p0)) (p1)))
           (equal (ec+ (p0) (ec- (p1)))
                  (ec+ (p0) (p1))))
  :rule-classes ()
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use (lemma-19-39 lemma-19-40))))

(defthm lemma-19-42
  (implies (and (equal (ec+ (p0) (p1)) (ec- (p0)))
                (not (equal (p0) (p1)))
                (equal (ec+ (p0) (p0)) (p1)))
           (equal (p1) (ec- (p1))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-19-25 lemma-19-41 (:instance p+q=p-q (p (p0)) (q (p1)))))))

(defthm lemma-19-43
  (implies (equal (ec+ (p0) (p1)) (ec- (p0)))
           (equal (p1) (ec- (ec+ (p0) (p0)))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-19-1 lemma-19-36 lemma-19-42 (:instance ec-- (r (p1)))))))

(defthm lemma-19-44
  (implies (and (ecp (cons a0 b0))
                (ecp (cons a1 b1))
                (equal (ec+ (cons a0 b0) (cons a1 b1)) (ec- (cons a0 b0))))
           (equal (cons a1 b1) (ec- (ec+ (cons a0 b0) (cons a0 b0)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable p0 p1)
                  :use (ecp-assumption
                        (:functional-instance lemma-19-43 (p0 (lambda () (if (ecp (cons a0 b0)) (cons a0 b0) (p0))))
                                                      (p1 (lambda () (if (ecp (cons a1 b1)) (cons a1 b1) (p1))))
                                                      (x0 (lambda () (if (ecp (cons a0 b0)) a0 (x0))))
                                                      (x1 (lambda () (if (ecp (cons a1 b1)) a1 (x1))))
                                                      (y0 (lambda () (if (ecp (cons a0 b0)) b0 (y0))))
                                                      (y1 (lambda () (if (ecp (cons a1 b1)) b1 (y1)))))))))
(defthm lemma-19
  (implies (and (ecp p) (ecp q)
                (equal (ec+ p q) (ec- p)))
           (equal q (ec- (ec+ p p))))
  :rule-classes ()
  :hints (("Goal" :use (ecp-consp
                        (:instance ecp-consp (p q))
                        (:instance ec-inverse-unique (r1 p) (r2 (ec- p)))
                        (:instance lemma-19-44 (a0 (car p)) (b0 (cdr p)) (a1 (car q)) (b1 (cdr q)))))))

(defthmd lemma-20-1
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ p q) (ec- r)))
           (equal (ec+ (ec+ p q) r)
                  (inf)))
  :hints (("Goal" :use ((:instance ec-inverse-unique (r2 (ec+ p q)) (r1 r))
                        (:instance ec-commutativity (p r) (q (ec- r)))))))

(defthmd lemma-20-2
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ p q) (ec- r)))
           (equal (ec+ p (ec+ q r))
                  (ec+ p (ec+ q (ec+ (ec- p) (ec- q))))))
  :hints (("Goal" :use (lemma-15 ec--))))

(defthm lemma-20-3
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ p q) (ec- r))
                (not (equal q (ec+ (ec- p) (ec- q)))))
           (equal (ec+ q (ec+ (ec- p) (ec- q)))
                  (ec- p)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance lemma-16 (p (ec- q)) (q (ec- p)))
                        (:instance ec-- (r q))
                        (:instance ec-commutativity (p (ec- p)) (q (ec- q)))))))

(defthm lemma-20-4
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ p q) (ec- r))
                (equal q (ec+ (ec- p) (ec- q))))
           (equal (ec- p)
                  (ec- (ec+ (ec- q) (ec- q)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance lemma-19 (p (ec- q)) (q (ec- p)))
                        (:instance ec-- (r p))
                        (:instance ec-- (r q))
                        (:instance ec-commutativity (p (ec- p)) (q (ec- q)))))))

(defthm lemma-20-5
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ p q) (ec- r))
                (equal q (ec+ (ec- p) (ec- q))))
           (equal (ec- p)
                  (ec+ q (ec+ (ec- p) (ec- q)))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-20-4
                        (:instance lemma-15 (p (ec- q)) (q (ec- q)))
                        (:instance ec-- (r p))
                        (:instance ec-- (r q))))))

(defthm lemma-20-6
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ p q) (ec- r)))
           (equal (ec- p)
                  (ec+ q (ec+ (ec- p) (ec- q)))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-20-3 lemma-20-5))))

(defthm lemma-20-7
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ p q) (ec- r)))
           (equal (ec+ p (ec+ q (ec+ (ec- p) (ec- q))))
                  (inf)))
  :rule-classes ()
  :hints (("Goal" :use (lemma-20-6
                        (:instance ec-inverse-unique (r1 p) (r2 (ec- p)))
                        (:instance ec-inverse-unique (r2 p) (r1 (ec+ q (ec+ (ec- p) (ec- q)))))))))

(defthm lemma-20
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ p q) (ec- r)))
           (equal (ec+ (ec+ p q) r)
                  (ec+ p (ec+ q r))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-20-1 lemma-20-2 lemma-20-7))))

(defthm lemma-21-1
  (implies (and (ecp p) (ecp q)
                (= (ec+ p p) (ec- q)))
           (equal (ec+ (ec+ p p) q)
                  (ec+ p (ec+ p q))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance lemma-20 (q p) (r q))))))

(defthm lemma-21-2
  (implies (and (ecp p) (ecp q)
                (= (ec+ p q) (ec- p)))
           (equal (ec+ (ec+ p q) p)
                  (ec+ q (ec+ p p))))
  :rule-classes ()
  :hints (("Goal" :use (ec-commutativity (:instance lemma-20 (p q) (q p) (r p))))))

(defthm lemma-21-3
  (implies (and (ecp p) (ecp q)
                (= (ec+ p q) (ec- p)))
           (equal (ec+ (ec+ p p) q)
                  (ec+ p (ec+ p q))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-21-2
                        (:instance ec-commutativity (q (ec+ p q)))
                        (:instance ec-commutativity (p (ec+ p p)))))))

(defthm lemma-21-4
  (implies (and (ecp p) (ecp q)
                (not (equal (ec+ p p) q))
                (not (equal (ec+ p p) (ec- q)))
                (not (equal (ec+ p q) p))
                (not (equal (ec+ p q) (ec- p))))
           (equal (ec+ q (ec+ p p))
                  (ec+ p (ec+ p q))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance lemma-17 (q p) (r q))
                        (:instance ec-commutativity (p (ec+ p p)))))))

(defthm lemma-21-5
  (implies (and (ecp p) (ecp q)
                (not (equal (ec+ p p) q)))
           (equal (ec+ (ec+ p p) q)
                  (ec+ p (ec+ p q))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-21-4 lemma-21-1 lemma-21-3 p+q<>p
                        (:instance ec-commutativity (p (ec+ p p)))))))

(defthm lemma-21-6
  (implies (and (ecp p)
                (equal (ec+ p p) q)
                (not (equal q (ec- p)))
                (not (equal (ec+ p q) p))
                (not (equal (ec+ p q) (ec- p))))
           (equal (ec+ q (ec+ p p))
                  (ec+ p (ec+ p q))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance lemma-18 (q p))))))

(defthm lemma-21-7
  (implies (and (ecp p) (ecp q)
                (equal (ec+ p p) q)
                (not (equal q (ec- p))))
           (equal (ec+ (ec+ p p) q)
                  (ec+ p (ec+ p q))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-21-2 lemma-21-6 p+q<>p
                       (:instance ec-commutativity (p (ec+ p p)))
                       (:instance ec-commutativity (q (ec+ p q)))))))

(defthm lemma-21-8
  (implies (and (ecp p) (ecp q)
                (equal (ec+ p p) q)
                (equal q (ec- p)))
           (equal (ec+ (ec+ p p) q)
                  (ec- q)))
  :rule-classes ()
  :hints (("Goal" :use (lemma-21-7
                        (:instance lemma-15 (q p))))))

(defthm lemma-21-9
  (implies (and (ecp p) (ecp q)
                (equal (ec+ p p) q)
                (equal q (ec- p)))
           (equal (ec+ (ec+ p p) q)
                  p))
  :rule-classes ()
  :hints (("Goal" :use (lemma-21-8
                        (:instance ec-- (r p))))))

(defthm lemma-21-10
  (implies (and (ecp p) (ecp q)
                (equal q (ec- p)))
           (equal (ec+ p (ec+ p q))
                  p))
  :rule-classes ()
  :hints (("Goal" :use ((:instance ec-inverse-unique (r1 p) (r2 q))))))

(defthm lemma-21
  (implies (and (ecp p) (ecp q))
           (equal (ec+ (ec+ p p) q)
                  (ec+ p (ec+ p q))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-21-5 lemma-21-7 lemma-21-9 lemma-21-10))))

(defthm lemma-24-1
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ r q) (ec- p)))
           (equal (ec+ (ec+ r q) p)
                  (ec+ r (ec+ q p))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance lemma-20 (p r) (r p))))))

(defthm lemma-24-2
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ q r) (ec- p)))
           (equal (ec+ p (ec+ q r))
                  (ec+ (ec+ p q) r)))
  :rule-classes ()
  :hints (("Goal" :use (lemma-24-1 ec-commutativity
                        (:instance ec-commutativity (p r))
                        (:instance ec-commutativity (q (ec+ q r)))
                        (:instance ec-commutativity (p r) (q (ec+ p q)))))))

(defthm lemma-24-3
  (implies (and (ecp p) (ecp q) (ecp r)
                (not (equal (ec+ q p) r))
                (not (equal (ec+ q p) (ec- r)))
                (not (equal (ec+ q r) p))
                (not (equal (ec+ q r) (ec- p))))
           (equal (ec+ r (ec+ q p))
                  (ec+ p (ec+ q r))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance lemma-17 (p q) (q p))))))

(defthm lemma-24-4
  (implies (and (ecp p) (ecp q) (ecp r)
                (not (equal (ec+ p q) r))
                (not (equal (ec+ p q) (ec- r)))
                (not (equal (ec+ q r) p))
                (not (equal (ec+ q r) (ec- p))))
           (equal (ec+ (ec+ p q) r)
                  (ec+ p (ec+ q r))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-24-3 ec-commutativity
                        (:instance ec-commutativity (p r) (q (ec+ p q)))))))

(defthm lemma-24-5
  (implies (and (ecp p) (ecp q) (ecp r)
                (not (equal (ec+ p q) r))
                (not (equal (ec+ q r) p)))
           (equal (ec+ (ec+ p q) r)
                  (ec+ p (ec+ q r))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-20 lemma-24-4 lemma-24-2))))

(defthm lemma-24-6
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ p q) r)
                (not (equal (ec+ p q) (ec- q)))
                (not (equal (ec+ q r) p)))
           (equal (ec+ (ec+ p q) r)
                  (ec+ p (ec+ q r))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-18 lemma-24-2))))

(defthm lemma-24-7
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ p q) r)
                (equal (ec+ p q) (ec- q)))
           (equal (ec+ p (ec+ q r))
                  p))
  :rule-classes ()
  :hints (("Goal" :use ((:instance ec-inverse-unique (r1 q) (r2 r))))))

(defthm lemma-24-8
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ p q) r)
                (equal (ec+ p q) (ec- q)))
           (equal (ec+ (ec+ p q) r)
                  (ec- (ec+ q q))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance lemma-15 (p q))))))

(defthm lemma-24-9
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ p q) r)
                (equal (ec+ p q) (ec- q)))
           (equal (ec+ (ec+ p q) r)
                  p))
  :rule-classes ()
  :hints (("Goal" :use (lemma-24-8 ec-commutativity (:instance lemma-19 (p q) (q p))))))

(defthm lemma-24-10
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ p q) r)
                (equal (ec+ p q) (ec- q)))
           (equal (ec+ p (ec+ q r))
                  (ec+ (ec+ p q) r)))
  :rule-classes ()
  :hints (("Goal" :use (lemma-24-7 lemma-24-9))))

(defthm lemma-24-11
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ p q) r)
                (equal (ec+ q r) p))
           (equal (ec+ (ec+ q q) p) p))
  :rule-classes ()
  :hints (("Goal" :use (ec-commutativity (:instance lemma-21 (p q) (q p))))))

(defthm lemma-24-12
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ p q) r)
                (equal (ec+ q r) p))
           (equal (ec+ q q) (inf)))
  :rule-classes ()
  :hints (("Goal" :use (lemma-24-11
                        (:instance p+q<>p (q (ec+ q q)))
                        (:instance ec-commutativity (q (ec+ q q)))))))

(defthm lemma-24-13
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ p q) r)
                (equal (ec+ q r) p))
           (or (equal q (inf)) (equal q (cons 0 0))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-24-12
                        (:instance r=-r (r q))
                        (:instance ec-inverse-unique (r1 q) (r2 q))))))

(defthm lemma-24-14
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ p q) r)
                (equal (ec+ q r) p))
           (equal (ec+ (ec+ p q) r)
                  (ec+ p (ec+ q r))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-24-13 lemma-22))))

(defthm lemma-24-15
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ p q) r))
           (equal (ec+ (ec+ p q) r)
                  (ec+ p (ec+ q r))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-24-14 lemma-24-10 lemma-24-6))))

(defthm lemma-24-16
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ r q) p))
           (equal (ec+ (ec+ r q) p)
                  (ec+ r (ec+ q p))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance lemma-24-15 (p r) (r p))))))

(defthm lemma-24-17
  (implies (and (ecp p) (ecp q) (ecp r)
                (equal (ec+ q r) p))
           (equal (ec+ p (ec+ q r))
                  (ec+ (ec+ p q) r)))
  :rule-classes ()
  :hints (("Goal" :use (lemma-24-16 ec-commutativity
                        (:instance ec-commutativity (p r))
                        (:instance ec-commutativity (q (ec+ q r)))
                        (:instance ec-commutativity (p r) (q (ec+ p q)))))))

(defthm ec-associativity
  (implies (and (ecp p) (ecp q) (ecp r))
           (equal (ec+ (ec+ p q) r)
                  (ec+ p (ec+ q r))))
  :rule-classes ()
  :hints (("Goal" :use (lemma-24-5 lemma-24-17 lemma-24-15))))


