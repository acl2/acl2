; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; collect.lisp
;;;
;;; This book contains the rules used to collect like terms,
;;; after things have been prepared by the bind-free rules.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "../pass1/top"))

(local (include-book "basic-helper"))

(local
 (defthm hack516
     (equal (EXPT X (- M))
            (/ (EXPT X M)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; These next two sections of rules do the actual work of combining
;;; "like" terms for the rules in normalize.

(defthm |(+ c (+ d x))|
  (implies (and (syntaxp (quotep c))
		(syntaxp (quotep d)))
	   (equal (+ c (+ d x))
		  (+ (+ c d) x))))

(defun collect-+ (x y)
  (declare (xargs :guard (and (acl2-numberp x)
                              (acl2-numberp y))))
  (+ x y))

(defthm collect-+-problem-finder
    (implies (equal x x)
             (equal (collect-+ x y)
                    (+ x y))))

(in-theory (disable collect-+-problem-finder))

(theory-invariant (not (active-runep '(:rewrite collect-+-problem-finder)))
                  :error nil)

(defthm |(+ x x)|
    (equal (collect-+ x x)
           (* 2 x)))

(defthm |(+ x (- x))|
    (equal (collect-+ x (- x))
           0))

(defthm |(+ x (* c x))|
    (implies (syntaxp (quotep c))
             (equal (collect-+ x (* c x))
                    (* (+ c 1) x))))


(defthm |(+ (- x) (* c x))|
    (implies (syntaxp (quotep c))
             (equal (collect-+ (- x) (* c x))
                    (* (- c 1) x))))

(defthm |(+ (* c x) (* d x))|
    (implies (and (syntaxp (quotep c))
                  (syntaxp (quotep d)))
             (equal (collect-+ (* c x) (* d x))
                    (* (+ c d) x))))

(defthm |(collect-+ y x)|
    (equal (collect-+ y x)
           (collect-+ x y)))

(theory-invariant (or (not (active-runep '(:rewrite collect-+)))
                      (and (active-runep '(:rewrite |(collect-+ y x)|))
                           (active-runep '(:rewrite |(+ x x)|))
                           (active-runep '(:rewrite |(+ x (- x))|))
                           (active-runep '(:rewrite |(+ x (* c x))|))
                           (active-runep '(:rewrite |(+ (- x) (* c x))|))
                           (active-runep '(:rewrite |(+ (* c x) (* d x))|))))
                  :error nil)

(in-theory (disable collect-+))

(theory-invariant (not (active-runep '(:definition collect-+)))
                  :error nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm |(* c (* d x))|
  (implies (and (syntaxp (quotep c))
		(syntaxp (quotep d)))
	   (equal (* c (* d x))
		  (* (* c d) x))))

(defun collect-* (x y)
  (declare (xargs :guard (and (acl2-numberp x)
                              (acl2-numberp y))))
  (* x y))

(defthm collect-*-problem-finder
    (implies (equal x x)
             (equal (collect-* x y)
                    (* x y))))

(in-theory (disable collect-*-problem-finder))

(theory-invariant (not (active-runep '(:rewrite collect-*-problem-finder)))
                  :error nil)

(defthm |(* (expt x n) (expt y n))|
    (implies (integerp n)
             (equal (collect-* (expt x n) (expt y n))
                    (expt (* x y) n))))

(defthm |(* x x)|
    (equal (collect-* x x)
           (expt x 2)))

(defthm |(* x (/ x))|
    (equal (collect-* x (/ x))
           (if (equal (fix x) 0)
               0
             1)))

(defthm |(* x (expt x n))|
    (implies (integerp n)
             (equal (collect-* x (expt x n))
                    (if (equal (fix x) 0)
                        0
                      (expt x (+ n 1))))))

;; RBK: !!! Missing (* (- x) (expt x n))

(defthm |(* x (expt (- x) n))|
    (implies (integerp n)
             (equal (collect-* x (expt (- x) n))
                    (cond ((equal (fix x) 0)
                           0)
                          ((evenp n)
                           (expt x (+ n 1)))
                          (t
                           (- (expt x (+ n 1))))))))

(defthm |(* x (/ (expt x n)))|
    (implies (integerp n)
             (equal (collect-* x (/ (expt x n)))
                    (if (equal (fix x) 0)
                        0
                      (/ (expt x (- n 1)))))))

(defthm |(* x (/ (expt (- x) n)))|
    (implies (integerp n)
             (equal (collect-* x (/ (expt (- x) n)))
                    (cond ((equal (fix x) 0)
                           0)
                          ((evenp n)
                           (/ (expt x (- n 1))))
                          (t
                           (- (/ (expt x (- n 1)))))))))

(defthm |(* (/ x) (expt x n))|
    (implies (integerp n)
             (equal (collect-* (/ x) (expt x n))
                    (if (equal (fix x) 0)
                        0
                      (expt x (- n 1))))))

; (Matt K., Nov. 2006) The following new rule (after ACL 3.0.1) has slowed down
; books/workshops/2004/legato/support/proof-by-generalization-mult.lisp from
; 103.33s to 150.21s (with proof inhibited).  Although that seemed to be the
; only noticeable slowdown it caused in the regression suite, we were tempted
; to leave it disabled by default.  But instead we are taking Robert Krug's
; advice to leave it enabled, since otherwise collect-* expressions won't be
; reduced.

(defthm |(* (/ x) (/ (expt x n)))|
  (implies (integerp n)
           (equal (collect-* (/ x) (/ (expt x n)))
                  (if (equal (fix x) 0)
                      0
                    (/ (expt x (+ n 1)))))))

(defthm |(* (/ x) (expt (- x) n))|
    (implies (integerp n)
             (equal (collect-* (/ x) (expt (- x) n))
                    (cond ((equal (fix x) 0)
                           0)
                          ((evenp n)
                           (expt x (- n 1)))
                          (t
                           (- (expt x (- n 1))))))))

(defthm |(* (expt x m) (expt x n))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (collect-* (expt x m) (expt x n))
                    (if (and (equal (fix x) 0)
                             (not (equal m 0))
                             (not (equal n 0)))
                        0
                      (expt x (+ m n))))))

(defthm |(* (expt (- x) m) (expt x n))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (collect-* (expt (- x) m) (expt x n))
                    (cond ((and (equal (fix x) 0)
                                (not (equal m 0))
                                (not (equal n 0)))
                           0)
                          ((evenp m)
                           (expt x (+ m n)))
                          (t
                           (- (expt x (+ m n))))))))

(defthm |(* (expt x m) (expt (- x) n))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (collect-* (expt x m) (expt (- x) n))
                    (cond ((and (equal (fix x) 0)
                                (not (equal m 0))
                                (not (equal n 0)))
                           0)
                          ((evenp n)
                           (expt x (+ m n)))
                          (t
                           (- (expt x (+ m n))))))))

(defthm |(* (/ (expt x m)) (expt x n))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (collect-* (/ (expt x m)) (expt x n))
                    (if (and (equal (fix x) 0)
                             (not (equal m 0))
                             (not (equal n 0)))
                        0
                      (expt x (- n m))))))

(defthm |(* (/ (expt (- x) m)) (expt x n))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (collect-* (/ (expt (- x) m)) (expt x n))
                    (cond ((and (equal (fix x) 0)
                                (not (equal m 0))
                                (not (equal n 0)))
                           0)
                          ((evenp m)
                           (expt x (- n m)))
                          (t
                           (- (expt x (- n m))))))))

(defthm |(* (/ (expt x m)) (expt (- x) n))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (collect-* (/ (expt x m)) (expt (- x) n))
                    (cond ((and (equal (fix x) 0)
                                (not (equal m 0))
                                (not (equal n 0)))
                           0)
                          ((evenp n)
                           (expt x (- n m)))
                          (t
                           (- (expt x (- n m))))))))

(defthm |(* (expt x m) (/ (expt x n)))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (collect-* (expt x m) (/ (expt x n)))
                    (if (and (equal (fix x) 0)
                             (not (equal m 0))
                             (not (equal n 0)))
                        0
                      (expt x (- m n))))))

(defthm |(* (expt (- x) m) (/ (expt x n)))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (collect-* (expt (- x) m) (/ (expt x n)))
                    (cond ((and (equal (fix x) 0)
                                (not (equal m 0))
                                (not (equal n 0)))
                           0)
                          ((evenp m)
                           (expt x (- m n)))
                          (t
                           (- (expt x (- m n))))))))

(defthm |(* (expt x m) (/ (expt (- x) n)))|
    (implies (and (integerp m)
                  (integerp n))
             (equal (collect-* (expt x m) (/ (expt (- x) n)))
                    (cond ((and (equal (fix x) 0)
                                (not (equal m 0))
                                (not (equal n 0)))
                           0)
                          ((evenp n)
                           (expt x (- m n)))
                          (t
                           (- (expt x (- m n))))))))



;; [Jared]: removing this rule:
;;
;; (defthm |(* (expt c n) (expt d n))|
;;     (implies (and (integerp n)
;;                   (syntaxp (quotep c))
;;                   (syntaxp (quotep d)))
;;              (equal (collect-* (expt c n) (expt d n))
;;                     (expt (* c d) n))))
;;
;; Because above we have the same thing without syntaxp hyps, except with
;; slightly different names:
;;
;; (defthm |(* (expt x n) (expt y n))|
;;   (implies (integerp n)
;;            (equal (collect-* (expt x n) (expt y n))
;;                   (expt (* x y) n))))

(defthm |(collect-* y x)|
    (equal (collect-* y x)
           (collect-* x y)))

(theory-invariant
 (or (not (active-runep '(:rewrite collect-*)))
     (and (active-runep '(:rewrite |(collect-* y x)|))
          (active-runep '(:rewrite |(* (expt x n) (expt y n))|))
          (active-runep '(:rewrite |(* x x)|))
          (active-runep '(:rewrite |(* x (/ x))|))
          (active-runep '(:rewrite |(* x (expt x n))|))
          (active-runep '(:rewrite |(* x (expt (- x) n))|))
          (active-runep '(:rewrite |(* x (/ (expt x n)))|))
          (active-runep '(:rewrite |(* x (/ (expt (- x) n)))|))
          (active-runep '(:rewrite |(* (/ x) (expt x n))|))
          (active-runep '(:rewrite |(* (/ x) (expt (- x) n))|))
          (active-runep '(:rewrite |(* (expt x m) (expt x n))|))
          (active-runep '(:rewrite |(* (expt (- x) m) (expt x n))|))
          (active-runep '(:rewrite |(* (expt x m) (expt (- x) n))|))
          (active-runep '(:rewrite |(* (/ (expt x m)) (expt x n))|))
          (active-runep '(:rewrite |(* (/ (expt (- x) m)) (expt x n))|))
          (active-runep '(:rewrite |(* (/ (expt x m)) (expt (- x) n))|))
          (active-runep '(:rewrite |(* (expt x m) (/ (expt x n)))|))
          (active-runep '(:rewrite |(* (expt (- x) m) (/ (expt x n)))|))
          (active-runep '(:rewrite |(* (expt x m) (/ (expt (- x) n)))|))))
 :error nil)

(in-theory (disable collect-*))

(theory-invariant (not (active-runep '(:definition collect-*)))
                  :error nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This set of commutative rules puts terms into a proper form
;;; for the above two sets of rules to fire.  They are needed by
;;; the rules in normaize.

(local
 (in-theory (enable collect-+ collect-*)))

(defun bubble-down (x match)
  (declare (xargs :guard t))
  (declare (ignore match))
  x)

(defthm bubble-down-+-problem-finder
    (implies (equal x x)
             (equal (+ (bubble-down x match) y)
                    (+ x y))))

(in-theory (disable bubble-down-+-problem-finder))

(theory-invariant
 (not (active-runep '(:rewrite bubble-down-+-problem-finder)))
 :error nil)

(defthm bubble-down-+-bubble-down
    (equal (+ (bubble-down x match) y z)
           (+ y (bubble-down x match) z)))

(defthm bubble-down-+-match-1
    (implies (syntaxp (equal match y))
             (equal (+ (bubble-down x match) y)
                    (collect-+ x y))))

(defthm bubble-down-+-match-2
    (implies (syntaxp (equal match y))
             (equal (+ y (bubble-down x match))
                    (collect-+ x y))))

(defthm bubble-down-+-match-3
    (implies (syntaxp (equal match y))
             (equal (+ (bubble-down x match) y z)
                    (+ (collect-+ x y) z))))

(theory-invariant
 (or (not (active-runep '(:rewrite bubble-down)))
     (and (active-runep '(:rewrite bubble-down-+-bubble-down))
          (active-runep '(:rewrite bubble-down-+-match-1))
          (active-runep '(:rewrite bubble-down-+-match-2))
          (active-runep '(:rewrite bubble-down-+-match-3))))
 :error nil)

(defthm bubble-down-*-problem-finder
    (implies (equal x x)
             (equal (* (bubble-down x match) y)
                    (* x y))))

(in-theory (disable bubble-down-*-problem-finder))

(theory-invariant
 (not (active-runep '(:rewrite bubble-down-*-problem-finder)))
 :error nil)

(defthm bubble-down-*-bubble-down
    (equal (* (bubble-down x match) y z)
           (* y (bubble-down x match) z)))

(defthm bubble-down-*-match-1
    (implies (syntaxp (equal match y))
             (equal (* (bubble-down x match) y)
                    (collect-* x y))))

(defthm bubble-down-*-match-2
    (implies (syntaxp (equal match y))
             (equal (* y (bubble-down x match))
                    (collect-* x y))))

(defthm bubble-down-*-match-3
    (implies (syntaxp (equal match y))
             (equal (* (bubble-down x match) y z)
                    (* (collect-* x y) z))))

(theory-invariant
 (or (not (active-runep '(:rewrite bubble-down)))
     (and (active-runep '(:rewrite bubble-down-*-bubble-down))
          (active-runep '(:rewrite bubble-down-*-match-1))
          (active-runep '(:rewrite bubble-down-*-match-2))
          (active-runep '(:rewrite bubble-down-*-match-3))))
 :error nil)

(in-theory (disable bubble-down (:executable-counterpart bubble-down)))

(theory-invariant
 (and (not (active-runep '(:rewrite bubble-down)))
      (not (active-runep '(:executable-counterpart bubble-down))))
 :error nil)
