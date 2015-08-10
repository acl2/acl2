(in-package "ACL2")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund relative-err (x true-val)
  (abs (/ (- x true-val) true-val)))


(defund less_equal_than_with_hints (x d hints)
  (declare (ignore hints))
  (<= x d))

(defund less_equal_than (x d)
  (<= x d))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defun upper-bound-const-or-var (c_or_var bindings)
  (if (acl2-numberp c_or_var)
      (abs c_or_var)
    (if (symbolp c_or_var)
         (cdr (assoc-equal c_or_var bindings))
      (hard-error 'upper-bound-const-or-var
                  "Syntax error: binding not found for ~p0~%"
                  c_or_var))))



(defun upper-bound-expr (expr bindings)
  (cond
   ((not (consp expr))
    (prog2$ (cw "VAR ~p0~%" expr)
            (upper-bound-const-or-var expr bindings)))

   ((equal (car expr) 'quote)
    (prog2$ (cw "CONSTANT ~p0~%" expr)
            (upper-bound-const-or-var (cadr expr) bindings)))

   ((equal (car expr) 'binary-*)
    (prog2$ (cw "MULT ~p0~%" expr)
            (* (upper-bound-expr (cadr expr) bindings)
               (upper-bound-expr (caddr expr) bindings))))

   ((equal (car expr) 'binary-+)
    (prog2$ (cw "ADD ~p0~%" expr)
            (+ (upper-bound-expr (cadr expr) bindings)
               (upper-bound-expr (caddr expr) bindings))))

   ((equal (car expr) 'unary--)
    (prog2$ (cw "UNARY-- ~p0~%" expr)
            (abs (upper-bound-expr (cadr expr) bindings))))

   ((assoc-equal expr bindings)
    (prog2$ (cw "KNOWN ~p0~%" expr)
            (cdr (assoc-equal expr bindings))))

   (t (prog2$ (cw "~p0~%" expr)
              (hard-error 'UPPER-BOUND-EXPR
                          "Syntax error: ~p0~%"
                          expr)))))

(defun bind-d1-with-hints (term hints)
  (list (cons 'd1 (list 'quote (upper-bound-expr term (cadr hints))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (Matt K., 10/2013: Changed rel8 to rel9.)
(include-book "rtl/rel9/arithmetic/top" :dir :system)

(defthmd over-estimate-rule-var-leaf
  (implies (and (syntaxp (symbolp x))
                (bind-free (bind-d1-with-hints x hints) (d1))
                (less_equal_than (abs x) d1)
                (<= d1 d2))
           (less_equal_than_with_hints (abs x) d2 hints))
  :hints (("Goal" :in-theory (enable less_equal_than less_equal_than_with_hints))))




(defthmd over-estimate-rule-const-leaf
  (implies (and (syntaxp (and (consp x)
                              (equal (car x) 'quote)
                              (acl2-numberp (cadr x))))
                (<= (abs x) d2))
           (less_equal_than_with_hints (abs x) d2 hints))
  :hints (("Goal" :in-theory (enable less_equal_than_with_hints))))

;;; not really necessary, we can use the executible counter-part result.


(encapsulate ()
             (local
              (defthmd over-estimate-rule-prod-1
                (implies (and (rationalp x)
                              (rationalp y))
                         (equal (abs (* x y))
                                (* (abs x) (abs y))))))


             (local
              (defthmd over-estimate-rule-prod-2
                (implies (and (syntaxp (and (quotep x)
                                            (rationalp (cadr x))
                                            (quotep d2)
                                            (rationalp (cadr d2))))
                              (rationalp x)
                              (rationalp y)
                              (not (equal x 0))
                              (>= y 0)
                              ;(> d2 0)
                              ;(rationalp d2)
                              (less_equal_than_with_hints y (* d2 (/ (abs x))) hints))
                         (less_equal_than_with_hints (* x y) d2 hints))
                :hints (("Goal" :cases ((not (>= x 0)))
                         :in-theory (enable less_equal_than_with_hints))
                        ("Subgoal 1" :cases ((not (>= y 0)))))))


             (local
              (defthmd over-estimate-rule-prod-3
                (implies (and (syntaxp (and (symbolp x)
                                            (quotep d2)
                                            (rationalp (cadr d2))))
                              (bind-free (bind-d1-with-hints x hints) (d1))
                              (less_equal_than_with_hints (abs x) d1 hints)
                              (rationalp x)
                              (rationalp y)
                              ;(rationalp d1)
                              ;(rationalp d2)
                              ;(> d1 0)
                              ;(> d2 0)
                              (>= y 0)
                              (less_equal_than_with_hints (* d1 y) d2 hints))
                         (less_equal_than_with_hints (* (abs x) y) d2 hints))
                :hints (("Goal" :in-theory (enable less_equal_than_with_hints)
                         :cases ((not (> y 0)))))))



             (local
              (defthmd over-estimate-rule-prod-3-short-cut
                (implies (and (syntaxp (and (or (symbolp x)
                                                (assoc-equal x (cadr hints)))
                                            (quotep d2)
                                            (rationalp (cadr d2))))
                              (bind-free (bind-d1-with-hints x hints) (d1))
                              (less_equal_than_with_hints (abs x) d1 hints)
                              (less_equal_than_with_hints  y (* d2 (/ d1)) hints)
                              (rationalp x)
                              (rationalp y)
                              (rationalp d1)
                              (>= d2 0)
                              (>= y 0))
                         (less_equal_than_with_hints (* (abs x) y) d2 hints))
                :hints (("Goal" :in-theory (enable less_equal_than_with_hints
                                                   over-estimate-rule-prod-3
                                                   over-estimate-rule-prod-2)
                         :cases ((not (> y 0)))))))




    (defthmd over-estimate-rule-prod
      (implies (and (bind-free (bind-d1-with-hints x hints) (d1))
                    (rationalp d1)
                    (rationalp d2)
                    (>= d2 0)
                    (force (rationalp x))
                    (force (rationalp y))
                    (less_equal_than_with_hints (abs x) d1 hints)
                    (less_equal_than_with_hints (abs y) (* (/ d1) d2) hints))
               (less_equal_than_with_hints (abs (* x y)) d2 hints))
      :hints (("Goal" :in-theory (e/d (over-estimate-rule-prod-1
                                       (abs)))
               :use ((:instance over-estimate-rule-prod-3-short-cut
                                (y (abs y)))))))


             )




(defthmd over-estimate-rule-add
  (implies (and (bind-free (bind-d1-with-hints x hints) (d1))
                (less_equal_than_with_hints (abs x) d1 hints)
                (less_equal_than_with_hints (abs y) (+ (- d1) d2) hints))
           (less_equal_than_with_hints (abs (+ x y)) d2 hints))
  :hints (("Goal" :in-theory (enable less_equal_than_with_hints))))





(defthmd over-estimate-rule-unary
  (implies (and (bind-free (bind-d1-with-hints x hints) (d1))
                (rationalp d1)
                (rationalp d2)
                (<= d1 d2)
                (less_equal_than_with_hints (abs x) d1 hints))
           (less_equal_than_with_hints (abs (unary-- x)) d2 hints))
  :hints (("Goal" :in-theory (enable less_equal_than_with_hints))))




(local
 (defthmd numeric-fact
   (implies (and (less_equal_than (abs e) (expt 2 -14))
                 (less_equal_than (abs rne2) (expt 2 -64))
                 (less_equal_than (abs rne3) (expt 2 -64))
                 (rationalp e)
                 (rationalp rne2)
                 (rationalp rne3))
            (less_equal_than_with_hints (abs (* -1 e))
                                  2
                                  '((e . 1/16384)
                                    (rne2 . 1/18446744073709551616)
                                    (rne3 . 1/18446744073709551616))))
   :hints (("Goal" :in-theory
            (e/d (over-estimate-rule-add
                  over-estimate-rule-prod
                  over-estimate-rule-var-leaf
                  over-estimate-rule-const-leaf
                  over-estimate-rule-unary)
                 (abs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;


(include-book "mylet")

;; Algorithm 8.8: single precision division algorithm
;; from "IA-64 and Elementary Functions: speed and precisioin"
;; by Peter Markstein.


;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (1) y0 := 1/b * (1+e), |e| <= 2^-m, m >= 14

(defund y0 (b e)
  (* (/ b) (+ 1 e)))


; (2) e0 := rn(1-b*y, 64)

(defund e0 (b y0 rne2)
  (* (+ 1 (* -1 b y0))
     (+ 1 rne2)))


; (3) y1 := rn(y0 + y0*e0, 64)

(defund y1 (e0 y0 rne3)
  (* (+ y0 (* y0 e0))
     (+ 1 rne3)))

; (4) y2 :=rn(y1+y1*e0, 64)

(defund y2 (e0 y0 y1 rne4)
  (* (+ y0 (* y1 e0))
     (+ 1 rne4)))

; (5) q0u := a*y2

(defund q0u (a y2)
  (* a y2))

;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm q0u-relative-error-bounded
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp e)
                (not (equal b 0))
                (not (equal a 0))
                (less_equal_than (abs e) (expt 2 -14))
                (rationalp rne2)
                (less_equal_than (abs rne2) (expt 2 -64))
                (rationalp rne3)
                (less_equal_than (abs rne3) (expt 2 -64))
                (rationalp rne4)
                (less_equal_than (abs rne4) (expt 2 -64)))
           (less_equal_than_with_hints
            (relative-err (mylet* ((y0 (y0 b e))
                                   (e0 (e0 b y0 rne2))
                                   (y1 (y1 e0 y0 rne3))
                                   (y2 (y2 e0 y0 y1 rne4))
                                   (q0u (q0u a y2)))
                                  q0u)
                          (* a (/ b)))
            (expt 2 -41)
            '((e . 1/16384)
              (rne2 . 1/18446744073709551616)
              (rne3 . 1/18446744073709551616)
              (rne4 . 1/18446744073709551616))))
  :hints (("Goal" :in-theory (e/d (over-estimate-rule-unary
                                   over-estimate-rule-add
                                   over-estimate-rule-prod
                                   over-estimate-rule-var-leaf
                                   over-estimate-rule-const-leaf
                                   relative-err
                                   y0 e0 y1 y2 q0u)
                                  (abs)))))


