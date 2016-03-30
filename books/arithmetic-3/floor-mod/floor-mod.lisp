; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; floor-mod.lisp
;;;
;;; This is a start at a book for reasoning about floor and mod.
;;; Most of what is here came from the IHS books and modified.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; RBK:!!! Separate rules into units --- i.e. no multiple corr.s

;; (equal (equal (floor a (expt 2 i)) (floor b (expt 2 j))
;;        (equal (floor a (expt (...)) b)))

#|
(defthm thm-1
    (implies (and (integerp a)
                  (integerp b)
                  (integerp n))
             (equal (MOD (+ (* B (FIBONACCI (+ -2 N)))
                            (* (FIBONACCI (+ -2 N))
                               (MOD (+ A B) 4294967296))
                            (* (FIBONACCI (+ -3 N))
                               (MOD (+ A B) 4294967296)))
                         4294967296)
                    (MOD (+ (* A (FIBONACCI (+ -2 N)))
                            (* A (FIBONACCI (+ -3 N)))
                            (* B (FIBONACCI (+ -3 N)))
                            (* 2 B (FIBONACCI (+ -2 N))))
                         4294967296)))
  :hints (("Goal" :in-theory (enable mod))))
|#


#|
; Something like the following rule is missing from my library.
; The version below does not seem particularly good, but I have
; not given it much thought yet.

(defthm foo
  (implies (and (integerp x)
                (<= 0 x)
                (rationalp r)
                (<= 0 r)
                (< r 1)
                (integerp i)
                (< 0 i))
           (equal (floor (+ x r) i)
                  (floor x i))))
|#

;;-----------------------------------------------------------------
;;
;; Definitions
;;
;;-----------------------------------------------------------------

(IN-PACKAGE "ACL2")


(table acl2-defaults-table :state-ok t)

;; I used to do the below include-book locally, but when I added the
;; set-defaults-hint this caused problems.  The set-defaults-hint
;; could not be done locally, and then this caused nonlinearp-default-hint
;; to be undefined.  I need to straighten all this out someday.

(include-book "../bind-free/top")

(set-default-hints '((nonlinearp-default-hint stable-under-simplificationp
                                              hist pspv)))

(include-book "../bind-free/building-blocks")

(defun rationalp-guard-fn (args)
  (if (endp (cdr args))
      `((rationalp ,(car args)))
    (cons `(rationalp ,(car args))
          (rationalp-guard-fn (cdr args)))))

(defmacro rationalp-guard (&rest args)
  (if (endp (cdr args))
      `(rationalp ,(car args))
    (cons 'and
          (rationalp-guard-fn args))))

(local
 (defthm niq-bounds
   (implies (and (integerp i)
		 (<= 0 i)
		 (integerp j)
		 (< 0 j))
	    (and (<= (nonnegative-integer-quotient i j)
		     (/ i j))
		 (< (+ (/ i j) -1)
		    (nonnegative-integer-quotient i j))))
   :rule-classes ((:linear
		   :trigger-terms ((nonnegative-integer-quotient i j))))))

;;-----------------------------------------------------------------
;;
;; Rules to rewrite truncate and friends to floor and mod
;;
;;-----------------------------------------------------------------

(defthm truncate-to-floor
  (implies (and (rationalp x)
                (rationalp y))
           (equal (truncate x y)
                  (cond ((integerp (/ x y))
                         (/ x y))
                        ((and (< 0 x) (< 0 y))
                         (floor x y))
                        ((and (< x 0) (< y 0))
                         (floor x y))
                        (t
                         (+ 1 (floor x y))))))
  :hints (("Goal" :in-theory (e/d (floor) (nonnegative-integer-quotient)))))

(defthm rem-to-mod
  (implies (and (rationalp x)
                (rationalp y))
           (equal (rem x y)
                  (cond ((integerp (/ x y))
                         (if (equal y 0)
                             x
                           0))
                        ((and (< 0 x) (< 0 y))
                         (mod x y))
                        ((and (< x 0) (< y 0))
                         (mod x y))
                        (t
                         (- (mod x y) y)))))
  :hints (("Goal" :in-theory (e/d (mod) (truncate)))))

(defthm ceiling-to-floor
  (implies (and (rationalp x)
                (rationalp y))
           (equal (ceiling x y)
                  (if (integerp (/ x y))
                      (/ x y)
                    (+ 1 (floor x y)))))
  :hints (("Goal" :in-theory (e/d (floor) (nonnegative-integer-quotient)))))

(defthm round-to-floor
  (implies (and (rationalp x)
                (rationalp y))
           (equal (round x y)
                  (cond ((< (mod (/ x y) 1) 1/2)
                         (floor x y))
                        ((< 1/2 (mod (/ x y) 1))
                         (+ 1 (floor x y)))
                        (t
                         (if (evenp (floor x y))
                             (floor x y)
                           (+ 1 (floor x y)))))))
  :hints (("Goal" :in-theory (e/d (floor mod) (nonnegative-integer-quotient)))))

; The following rule is in the spirit of the ones just above, but since ash
; already has a simple definition in terms of floor, we choose to leave this
; rule disabled and leave ash enabled.
(defthmd ash-to-floor
  (implies (and (rationalp i)
		(rationalp n))
	   (equal (ash i n)
		  (cond ((and (integerp i)
			      (integerp n))
			 (floor i (expt 2 (- n))))
			((integerp i)
			 (floor i 1))
			(t
			 0))))
  :hints (("Goal" :in-theory (e/d (floor) (nonnegative-integer-quotient)))))

(in-theory (disable truncate rem ceiling round))


;;-----------------------------------------------------------------
;;
;; Basic definitions and lemmatta
;;
;;-----------------------------------------------------------------

;;(defthm floor-integerp
;;  (integerp (floor x y)))

(defthm integerp-mod
    (implies (and (integerp m)
		  (integerp n))
	     (integerp (mod m n)))
  :rule-classes (:rewrite :type-prescription))

(defthm rationalp-mod
  (implies (and (rationalp x)
                #+:non-standard-analysis (rationalp y))
           (rationalp (mod x y)))
  :hints (("Goal" :cases ((rationalp y))))
  :rule-classes (:rewrite :type-prescription))

#+:non-standard-analysis
(defthm realp-mod
  (implies (and (realp x)
		(realp y))
	   (realp (mod x y)))
  :rule-classes :type-prescription)

(defthm floor-completion
  (implies (or (not (acl2-numberp x))
	       (not (acl2-numberp y)))
	   (equal (floor x y)
		  0)))

(local
 (defthm floor-0-local
     (and (equal (floor x 0)
                 0)
          (equal (floor 0 y)
                 0))))

(defthm mod-completion
  (and (implies (not (acl2-numberp x))
		(equal (mod x y)
		       0))
       (implies (not (acl2-numberp y))
		(equal (mod x y)
		       (fix x)))))

(local
 (defthm mod-0-local
     (and (equal (mod 0 y)
                 0)
          (equal (mod x 0)
                 (fix x)))))

(local
 (defthm floor-x-1-local
     (implies (integerp x)
              (equal (floor x 1)
                     x))))

(local
 (defthm mod-x-1-local
     (implies (integerp x)
              (equal (mod x 1)
                     0))))

; Name changed 3/15/2016 by Matt K. to avoid name clash with lemma
; floor-mod-elim in ihs/quotient-remainder-lemmas.
(defthm floor-mod-elim-weak
  (implies (rationalp-guard x y)
	   (equal (+ (mod x y)
		     (* y (floor x y)))
		  x))
  :hints (("Goal" :in-theory (disable floor)))
  :rule-classes ((:rewrite)
		 (:elim)))

; The following is an improvement of the above, but during development after
; Version_3.0.1 release, it was found to ruin the proof of
; wp-zcoef-loop-invariant in
; books/workshops/2004/legato/support/generic-theory-loop-invariant-mult.lisp.
; Rather than investigate, we will just keep the rule above, which isn't too
; bad.

; (defthm floor-mod-elim
;   (implies (force (acl2-numberp x))
;            (equal (+ (mod x y) (* y (floor x y))) x))
;   :rule-classes (:rewrite :elim)
;   :hints (("Goal" :in-theory (enable mod))))


;;-----------------------------------------------------------------
;;
;; alternate, recursive, definitions.
;;
;;-----------------------------------------------------------------

(defun floor-induct-fn (x y)
  (declare (xargs :measure (abs (floor x y))))
    (cond ((not (rationalp x))
	   t)
	  ((not (rationalp y))
	   t)
	  ((equal y 0)
	   t)
	  ((< y 0)
	   (cond ((< 0 x)
		  (1- (floor-induct-fn (+ x y) y)))
		 ((< y x)
		  t)
		 (t
		  (1+ (floor-induct-fn (- x y) y)))))
	  (t  ;; (< 0 y)
	   (cond ((< x 0)
		  (1- (floor-induct-fn (+ x y) y)))
		 ((< x y)
		  t)
		 (t
		  (1+ (floor-induct-fn (- x y) y)))))))

(defun mod-induct-fn (x y)
  (declare (xargs :measure (abs (floor x y))))
    (cond ((not (rationalp x))
	   t)
	  ((not (rationalp y))
	   t)
	  ((equal y 0)
	   t)
	  ((< y 0)
	   (cond ((< 0 x)
		  (mod-induct-fn (+ x y) y))
		 ((< y x)
		  t)
		 (t
		  (mod-induct-fn (- x y) y))))
	  (t  ;; (< 0 y)
	   (cond ((< x 0)
		  (mod-induct-fn (+ x y) y))
		 ((< x y)
		  t)
		 (t
		  (mod-induct-fn (- x y) y))))))

(defthm floor-ind
  t
  :rule-classes ((:induction :pattern (floor x y)
			     :scheme (floor-induct-fn x y))))

(defthm mod-ind
  t
  :rule-classes ((:induction :pattern (mod x y)
			     :scheme (mod-induct-fn x y))))

(in-theory (disable floor-ind mod-ind))

;;-----------------------------------------------------------------
;;
;; Simple bounds.
;;
;;-----------------------------------------------------------------

(defthm floor-bounds-1
  (implies (rationalp-guard x y)
	   (and (< (+ (/ x y) -1)
		   (floor x y))
		(<= (floor x y)
		    (/ x y))))
  :rule-classes ((:generalize)
		 (:linear :trigger-terms ((floor x y)))))

(defthm floor-bounds-2
  (implies (and (rationalp-guard x y)
		(integerp (/ x y)))
	   (equal (floor x y)
		  (/ x y)))
  :rule-classes ((:generalize)
		 (:linear :trigger-terms ((floor x y)))))

(defthm floor-bounds-3
  (implies (and (rationalp-guard x y)
		(not (integerp (/ x y))))
	   (< (floor x y)
	      (/ x y)))
  :rule-classes ((:generalize)
		 (:linear :trigger-terms ((floor x y)))))

(defthm mod-bounds-1
  (implies (and (rationalp-guard x y)
		(< 0 y))
	   (and (<= 0 (mod x y))
		(< (mod x y) y)))
  :rule-classes ((:generalize)
		 (:linear)))

(defthm mod-bounds-2
  (implies (and (rationalp-guard x y)
		(< y 0))
	   (and (<= (mod x y) 0)
		(< y (mod x y))))
  :rule-classes ((:generalize)
		 (:linear)))

(defthm mod-bounds-3
  (implies (and (rationalp-guard x y)
                (not (equal y 0))
		(integerp (/ x y)))
	   (equal 0 (mod x y)))
  :rule-classes ((:generalize)
		 (:linear)))

(deftheory floor-bounds
    '((:linear floor-bounds-1)
      (:linear floor-bounds-2)
      (:linear floor-bounds-1)))

(deftheory mod-bounds
    '((:linear mod-bounds-1)
      (:linear mod-bounds-2)
      (:linear mod-bounds-3)))

(deftheory floor-mod-bounds
    '((:linear floor-bounds-1)
      (:linear floor-bounds-2)
      (:linear floor-bounds-1)
      (:linear mod-bounds-1)
      (:linear mod-bounds-2)
      (:linear mod-bounds-3)))

;;-----------------------------------------------------------------
;;
;; Type-prescription and linear rules.
;;
;;-----------------------------------------------------------------

(in-theory (disable floor mod))

(defthm floor-nonnegative-1
  (implies (and (rationalp-guard x y)
		(<= 0 y)
                (<= 0 x))
	   (<= 0 (floor x y)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)
		 (:type-prescription)))

(defthm floor-nonnegative-2
  (implies (and (rationalp-guard x y)
                (<= y 0)
                (<= x 0))
	   (<= 0 (floor x y)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)
		 (:type-prescription)))

(defthm floor-nonpositive-1
  (implies (and (rationalp-guard x y)
                (<= 0 y)
                (<= x 0))
	   (<= (floor x y) 0))
  :rule-classes ((:rewrite :backchain-limit-lst 1)
		 (:type-prescription)))

(defthm floor-nonpositive-2
  (implies (and (rationalp-guard x y)
                (<= y 0)
                (<= 0 x))
	   (<= (floor x y) 0))
  :rule-classes ((:rewrite :backchain-limit-lst 1)
		 (:type-prescription)))

(defthm floor-positive
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                (rationalp-guard x y))
           (equal (< 0 (floor x y))
                  (or (and (< 0 y)
                           (<= y x))
                      (and (< y 0)
                           (<= x y)))))
  :rule-classes ((:rewrite)
		 (:type-prescription
                  :corollary
                  (implies (and (rationalp-guard x y)
                                (< 0 y)
                                (<= y x))
                           (< 0 (floor x y))))
		 (:type-prescription
                  :corollary
                  (implies (and (rationalp-guard x y)
                                (< y 0)
                                (<= x y))
                           (< 0 (floor x y))))
		 (:rewrite
                  :backchain-limit-lst 1
		  :corollary
		  (implies (and (syntaxp
                                 (not (rewriting-goal-literal x mfc state)))
                                (rationalp-guard x y)
                                (< 0 y)
                                (<= y x))
                           (< 0 (floor x y))))
		 (:rewrite
                  :backchain-limit-lst 1
		  :corollary
		  (implies (and (syntaxp
                                 (not (rewriting-goal-literal x mfc state)))
                                (rationalp-guard x y)
                                (< y 0)
                                (<= x y))
                  (< 0 (floor x y))))))

(defthm floor-negative
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                (rationalp-guard x y))
           (equal (< (floor x y) 0)
                  (or (and (< 0 x)
                           (< y 0))
                      (and (< x 0)
                           (< 0 y)))))
  :rule-classes ((:rewrite)
		 (:type-prescription
                  :corollary
                  (implies (and (rationalp-guard x y)
                                (< 0 x)
                                (< y 0))
                           (< (floor x y) 0)))
		 (:type-prescription
                  :corollary
                  (implies (and (rationalp-guard x y)
                                (< x 0)
                                (< 0 y))
                           (< (floor x y) 0)))
		 (:rewrite
                  :backchain-limit-lst 1
		  :corollary
		  (implies (and (syntaxp
                                 (not (rewriting-goal-literal x mfc state)))
                                (rationalp-guard x y)
                                (< 0 x)
                                (< y 0))
                           (< (floor x y) 0)))
		 (:rewrite
                  :backchain-limit-lst 1
		  :corollary
		  (implies (and (syntaxp
                                 (not (rewriting-goal-literal x mfc state)))
                                (rationalp-guard x y)
                                (< x 0)
                                (< 0 y))
                           (< (floor x y) 0)))))

(defthm floor-zero
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                (rationalp-guard x y))
           (equal (equal (floor x y) 0)
                  (or (equal y 0)
                      (and (<= 0 x)
                           (< x y))
                      (and (<= x 0)
                           (< y x)))))
  :rule-classes ((:rewrite)
                 (:type-prescription
                  :corollary
                  (implies (and (rationalp-guard x y)
                                (equal y 0))
                           (equal (floor x y) 0)))
                 (:type-prescription
                  :corollary
                  (implies (and (rationalp-guard x y)
                                (<= 0 x)
                                (< x y))
                           (equal (floor x y) 0)))
                 (:type-prescription
                  :corollary
                  (implies (and (rationalp-guard x y)
                                (<= x 0)
                                (< y x))
                           (equal (floor x y) 0)))
                 (:rewrite
                  :backchain-limit-lst 1
                  :corollary
                  (implies (and (rationalp-guard x y)
                                (equal y 0))
                           (equal (floor x y) 0)))
                 (:rewrite
                  :backchain-limit-lst 1
                  :corollary
                  (implies (and (rationalp-guard x y)
                                (<= 0 x)
                                (< x y))
                           (equal (floor x y) 0)))
                 (:rewrite
                  :backchain-limit-lst 1
                  :corollary
                  (implies (and (rationalp-guard x y)
                                (<= x 0)
                                (< y x))
                           (equal (floor x y) 0)))))

(defthm floor-=-x/y-1
  (implies (rationalp-guard x y)
	   (equal (equal (floor x y) (* x (/ y)))
                  (integerp (/ x y)))))

(defthm floor-=-x/y-2
  (implies (rationalp-guard x y)
	   (equal (equal (floor x y) (* (/ y) x))
                  (integerp (/ x y)))))

(defthm mod-nonnegative
  (implies (and (rationalp-guard x y)
		(< 0 y))
	   (<= 0 (mod x y)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)
		 (:type-prescription)))

(defthm mod-nonpositive
  (implies (and (rationalp-guard x y)
		(< y 0))
	   (<= (mod x y) 0))
  :rule-classes ((:rewrite :backchain-limit-lst 1)
		 (:type-prescription)))

(defthm mod-positive
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                  (rationalp-guard x y))
             (equal (< 0 (mod x y))
                    (or (and (equal y 0)
                             (< 0 x))
                        (and (< 0 y)
                             (not (integerp (/ x y)))))))
  :rule-classes ((:rewrite)
                 (:type-prescription
		  :corollary
		   (implies (and (rationalp-guard x y)
                                 (equal y 0)
                                 (< 0 x))
                            (< 0 (mod x y))))
                 (:type-prescription
		  :corollary
		   (implies (and (rationalp-guard x y)
                                 (< 0 y)
                                 (not (integerp (/ x y))))
                            (< 0 (mod x y))))
                 (:rewrite
                  :backchain-limit-lst 1
		  :corollary
		   (implies (and (syntaxp
                                  (not (rewriting-goal-literal x mfc state)))
                                 (rationalp-guard x y)
                                 (equal y 0)
                                 (< 0 x))
                            (< 0 (mod x y))))
                 (:rewrite
                  :backchain-limit-lst 1
		  :corollary
		   (implies (and (syntaxp
                                  (not (rewriting-goal-literal x mfc state)))
                                 (rationalp-guard x y)
                                 (< 0 y)
                                 (not (integerp (/ x y))))
                            (< 0 (mod x y))))))

(defthm mod-negative
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                  (rationalp-guard x y))
             (equal (< (mod x y) 0)
                    (or (and (equal y 0)
                             (< x 0))
                        (and (< y 0)
                             (not (integerp (/ x y)))))))
  :rule-classes ((:rewrite)
                 (:type-prescription
		  :corollary
		   (implies (and (rationalp-guard x y)
                                 (equal y 0)
                                 (< x 0))
                            (< (mod x y) 0)))
                 (:type-prescription
		  :corollary
		   (implies (and (rationalp-guard x y)
                                 (< y 0)
                                 (not (integerp (/ x y))))
                            (< (mod x y) 0)))
                 (:rewrite
                  :backchain-limit-lst 1
		  :corollary
		   (implies (and (syntaxp
                                  (not (rewriting-goal-literal x mfc state)))
                                 (rationalp-guard x y)
                                 (equal y 0)
                                 (< x 0))
                            (< (mod x y) 0)))
                 (:rewrite
                  :backchain-limit-lst 1
		  :corollary
		   (implies (and (syntaxp
                                  (not (rewriting-goal-literal x mfc state)))
                                 (rationalp-guard x y)
                                 (< y 0)
                                 (not (integerp (/ x y))))
                            (< (mod x y) 0)))))


;;; This is a bad rule, as a rewrite rule.  I should not
;;; move mods to integerp.

(defthm mod-zero
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                (rationalp-guard x y))
           (equal (equal (mod x y) 0)
                  (or (equal x 0)
                      (and (not (equal y 0))
                           (integerp (/ x y))))))
  :rule-classes ((:rewrite)   ;;; Bad part.
                 (:type-prescription
                  :corollary
                  (implies (and (rationalp-guard x y)
                                (not (equal y 0))
                                (integerp (/ x y)))
                           (equal (mod x y) 0)))
                 (:type-prescription
                  :corollary
                  (implies (and (rationalp-guard x y)
                                (equal x 0))
                           (equal (mod x y) 0)))
                 (:rewrite
                  :backchain-limit-lst 1
                  :corollary
                  (implies (and (rationalp-guard x y)
                                (not (equal y 0))
                                (integerp (/ x y)))
                           (equal (mod x y) 0)))
                 (:rewrite
                  :backchain-limit-lst 1
                  :corollary
                  (implies (and (rationalp-guard x y)
                                (equal x 0))
                           (equal (mod x y) 0)))))

(defthm mod-x-y-=-x
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                  (rationalp-guard x y))
             (equal (equal (mod x y) x)
                    (or (equal y 0)
                        (and (<= 0 x)
                             (< x y))
                        (and (<= x 0)
                             (< y x)))))
  :rule-classes ((:rewrite)
                 (:rewrite
                  :backchain-limit-lst 1
                  :corollary
                  (implies (and (syntaxp
                                 (not (rewriting-goal-literal x mfc state)))
                                (rationalp-guard x y)
                                (equal y 0))
                           (equal (mod x y) x)))
                 (:rewrite
                  :backchain-limit-lst 1
                  :corollary
                  (implies (and (rationalp-guard x y)
                                (<= 0 x)
                                (< x y))
                           (equal (mod x y) x)))
                 (:rewrite
                  :backchain-limit-lst 1
                  :corollary
                  (implies (and (rationalp-guard x y)
                                (<= x 0)
                                (< y x))
                           (equal (mod x y) x)))))

;;-----------------------------------------------------------------
;;
;; ???
;;
;;-----------------------------------------------------------------

(defthm justify-floor-recursion
  (and (implies (and (integerp x)
		     (< 0 x)
		     (integerp y)
		     (< 1 y))
		(< (floor x y) x))
       (implies (and (integerp x)
		     (< x -1)
		     (integerp y)
		     (<= 2 y))
		(< x (floor x y)))))

;;-----------------------------------------------------------------
;;
;; Simple reductions
;;
;;-----------------------------------------------------------------

; Name changed 3/15/2016 by Matt K. to avoid name clash with lemma
; floor-+ in ihs/quotient-remainder-lemmas.
(defthmd floor-+-weak
  (implies (and (rationalp-guard x y z)
                (syntaxp (not (equal (fn-symb x) 'MOD)))
                (syntaxp (not (equal (fn-symb x) 'MOD))))
	   (equal (floor (+ x y) z)
		  (+ (floor (+ (mod x z) (mod y z)) z)
		     (+ (floor x z) (floor y z))))))

; Name changed 3/15/2016 by Matt K. to avoid name clash with lemma
; mod-+ in ihs/quotient-remainder-lemmas.
(defthmd mod-+-weak
  (implies (and (rationalp-guard x y z)
                (syntaxp (not (equal (fn-symb x) 'MOD)))
                (syntaxp (not (equal (fn-symb x) 'MOD))))
	   (equal (mod (+ x y) z)
		  (mod (+ (mod x z) (mod y z)) z)))
  :hints (("Goal" :in-theory (enable mod))))

;; This rule below should probably be used to ``normalize''
;; expressions such as
;; (equal (floor (+ (floor a 2) (* f2 (expt 2 i)))
;;              (expt 2 (* 2 i)))
;;       (floor (+ f2
;;                 (floor (mod (floor a (expt 2 i)) (expt 2 i)) 2)
;;                 (* (expt 2 (1- i)) (floor a (expt 2 (* 2 i)))))
;;              (expt 2 i)))
;; to make the ``denominators'' equal.

;; Add other direction of the next two rules, or generalize them.

; Name changed 3/15/2016 by Matt K. to avoid name clash with lemma
; rewrite-floor-x*y-z-right in ihs/quotient-remainder-lemmas.
(defthmd rewrite-floor-x*y-z-right-weak
  (implies (rationalp-guard x y z)
	   (equal (floor (* x y) z)
		  (floor x (/ z y)))))

(defthmd rewrite-mod-x*y-z-right
  (implies (rationalp-guard x y z)
	   (equal (mod (* x y) z)
		  (* y (mod x (/ z y)))))
  :hints (("Goal" :in-theory (enable mod))))

; Name changed 3/15/2016 by Matt K. to avoid name clash with lemma
; floor-minus in ihs/quotient-remainder-lemmas.
(defthm floor-minus-weak
  (implies (and (rationalp-guard x y)
                (syntaxp (negative-addends-p x)))
           (equal (floor x y)
                  (if (integerp (* x (/ y)))
                      (- (floor (- x) y))
                    (+ (- (floor (- x) y)) -1)))))

(defthm floor-minus-2
  (implies (and (rationalp-guard x y)
                (syntaxp (negative-addends-p y)))
	    (equal (floor x y)
		   (if (integerp (* x (/ y)))
		       (- (floor x (- y)))
		     (+ (- (floor x (- y))) -1)))))

;renamed to avoid conflict with rtl/rel5
(defthm mod-neg
  (implies (and (rationalp-guard x y)
                (syntaxp (negative-addends-p x)))
	   (equal (mod x y)
		  (if (and (not (equal y 0))
                           (integerp (/ x y)))
		      0
		    (- y (mod (- x) y)))))
  :hints (("Goal" :in-theory (enable mod))))

(defthm mod-minus-2
  (implies (and (rationalp-guard x y)
                (syntaxp (negative-addends-p y)))
	   (equal (mod x y)
		  (if (and (not (equal y 0))
                           (integerp (/ x y)))
		      0
		    (- (mod x (- y)) (- y)))))
  :hints (("Goal" :in-theory (enable mod))))

; Name changed 3/15/2016 by Matt K. to avoid name clash with lemma
; rewrite-floor-mod in ihs/quotient-remainder-lemmas.
(defthm rewrite-floor-mod-weak
  (implies (and (rationalp-guard x y z)
		(equal i (/ y z))
		(integerp i))
	   (equal (floor (mod x y) z)
		  (- (floor x z) (* i (floor x y))))))

; Name changed 3/15/2016 by Matt K. to avoid name clash with lemma
; rewrite-mod-mod in ihs/quotient-remainder-lemmas.
(defthm rewrite-mod-mod-weak
  (implies (and (rationalp-guard x y z)
                (not (equal z 0))
		(equal i (/ y z))
		(integerp i))
	   (equal (mod (mod x y) z)
		  (mod x z)))
  :hints (("Goal" :in-theory (enable mod-+-weak)
                  :cases ((equal (floor x y) 0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun mod-+-cancel-0-fn-1 (x z)
  (declare (xargs :guard (and (pseudo-termp x)
                              (eq (fn-symb x) 'BINARY-+))))
  (cond ((equal (fargn x 1) z)
         t)
        ((eq (fn-symb (fargn x 2)) 'BINARY-+)
         (mod-+-cancel-0-fn-1 (fargn x 2) z))
        ((equal (fargn x 2) z)
         t)
        (t
         nil)))

(defun mod-+-cancel-0-fn (x z)
  (declare (xargs :guard (pseudo-termp x)))
  (if (and (eq (fn-symb x) 'BINARY-+)
           (not (eq (fn-symb z) 'BINARY-+)))
      (mod-+-cancel-0-fn-1 x z)
    nil))

(local
 (defthm local-mod-+-cancel-0
     (implies (rationalp-guard x y z)
              (equal (equal (mod (+ x y) z) x)
                     (and (equal (mod y z) 0)
                          (equal (mod x z) x))))
   :hints (("Goal" :cases ((< 0 z) (< z 0) (equal z 0)))
           ("Subgoal 3.10" :in-theory (enable mod))
           ("Subgoal 3.4" :in-theory (enable mod-+-weak))
           ("Subgoal 2.5" :in-theory (enable mod))
           ("Subgoal 2.2" :in-theory (enable mod-+-weak)))
   :rule-classes nil))

; Name changed 3/15/2016 by Matt K. to avoid name clash with lemma
; mod-+-cancel-0 in ihs/quotient-remainder-lemmas.
(defthm mod-+-cancel-0-weak
    (implies (and (rationalp-guard x y z)
                  (syntaxp (mod-+-cancel-0-fn x z)))
             (equal (equal (mod x y) z)
                    (and (equal (mod (- x z) y) 0)
                         (equal (mod z y) z))))
  :hints (("Goal" :use ((:instance local-mod-+-cancel-0
                                   (x z)
                                   (z y)
                                   (y (- x z)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun factors-ccc (product)
  (declare (xargs :guard (pseudo-termp product)))
  (if (eq (fn-symb product) 'BINARY-*)
      (cons (fargn product 1)
            (factors-ccc (fargn product 2)))
    (list product)))

(defun non-zero-intersection-equal (x y mfc state)
  (declare (xargs :guard (and (pseudo-term-listp x)
                              (pseudo-term-listp y))))
  (cond ((endp x)
         nil)
        ((and (member-equal (car x) y)
              (proveably-non-zero-rational (car x) mfc state))
         (cons (car x) (non-zero-intersection-equal (cdr x) y mfc state)))
        (t
         (non-zero-intersection-equal (cdr x) y mfc state))))

(defun make-product-ccc (factors)
  (declare (xargs :guard (true-listp factors)))
  (cond ((null factors)
         ''1)
        ((null (cdr factors))
         (car factors))
        ((null (cddr factors))
         (list 'BINARY-* (car factors) (cadr factors)))
        (t
         (list 'BINARY-* (car factors) (make-product-ccc (cdr factors))))))

(defun find-common-factors (x y mfc state)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y))))
  (let* ((x-factors (factors-ccc x))
         (y-factors (factors-ccc y))
         (common-factors (non-zero-intersection-equal x-factors y-factors
                                                      mfc state)))
    (if common-factors
        (list (cons 'common-factors (make-product-ccc common-factors)))
      nil)))

; Name changed 3/15/2016 by Matt K. to avoid name clash with lemma
; floor-cancel-* in ihs/quotient-remainder-lemmas.
(defthm floor-cancel-*-weak
    (implies (and (rationalp-guard x y)
                  (bind-free
                   (find-common-factors x y mfc state)
                   (common-factors))
                  (rationalp common-factors)
                  (not (equal common-factors 0)))
             (equal (floor x y)
                    (floor (* x (/ common-factors)) (* y (/ common-factors))))))

(defthm mod-cancel-*
    (implies (and (rationalp-guard x y)
                  (bind-free
                   (find-common-factors x y mfc state)
                   (common-factors))
                  (rationalp common-factors)
                  (not (equal common-factors 0)))
             (equal (mod x y)
                    (* common-factors
                       (mod (* x (/ common-factors)) (* y (/ common-factors))))))
  :hints (("Goal" :in-theory (enable mod))))

;;-----------------------------------------------------------------
;;
;; Cancellation
;;
;;-----------------------------------------------------------------

(defun find-cancelling-addends (x y mfc state)
  (declare (xargs :guard (pseudo-termp x)))
  (cond ((eq (fn-symb x) 'BINARY-+)
         (cond ((proveably-integer
                 `(BINARY-* ,(fargn x 1) (UNARY-/ ,y))
                 mfc state)
                (list (cons 'addend (fargn x 1))))
               ((eq (fn-symb (fargn x 2)) 'BINARY-+)
                (find-cancelling-addends (fargn x 2) y mfc state))
               ((proveably-integer
                 `(BINARY-* ,(fargn x 2) (UNARY-/ ,y))
                 mfc state)
                (list (cons 'addend (fargn x 2))))
               (t
                nil)))
        ((proveably-integer
          `(BINARY-* ,x (UNARY-/ ,y))
          mfc state)
         (list (cons 'addend x)))
        (t
         nil)))

(defthm cancel-floor-+
    (implies (and (bind-free
                   (find-cancelling-addends x y mfc state)
                   (addend))
                  (rationalp-guard x y addend)
                  (equal i (/ addend y))
                  (integerp i))
             (equal (floor x y)
                    (+ i (floor (- x addend) y)))))

(defthm cancel-mod-+
    (implies (and (not (equal y 0))
                  (bind-free
                   (find-cancelling-addends x y mfc state)
                   (addend))
                  (rationalp-guard x y addend)
                  (equal i (/ addend y))
                  (integerp i))
             (equal (mod x y)
                    (mod (- x addend) y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun simplify-mod-+-mod-fn (x y mfc state)
  (declare (xargs :guard (pseudo-termp x)))
  (cond ((eq (fn-symb x) 'BINARY-+)
         (let ((arg1 (fargn x 1))
               (arg2 (fargn x 2)))
           (cond ((and (eq (fn-symb arg1) 'MOD)
                       (proveably-integer
                        `(BINARY-* ,(fargn arg1 2) (UNARY-/ ,y))
                        mfc state))
                  (list (cons 'w (fargn arg1 1))
                        (cons 'z (fargn arg1 2))))
                 ((eq (fn-symb arg2) 'BINARY-+)
                  (simplify-mod-+-mod-fn arg2 y mfc state))
                 ((and (eq (fn-symb arg2) 'MOD)
                       (proveably-integer
                        `(BINARY-* ,(fargn arg2 2) (UNARY-/ ,y))
                        mfc state))
                  (list (cons 'w (fargn arg2 1))
                        (cons 'z (fargn arg2 2))))
                 (t
                  nil))))
        ((and (eq (fn-symb x) 'MOD)
              (proveably-integer
               `(BINARY-* ,(fargn x 2) (UNARY-/ ,y))
               mfc state))
         (list (cons 'w (fargn x 1))
               (cons 'z (fargn x 2))))
        (t
         nil)))

; Name changed 3/15/2016 by Matt K. to avoid name clash with lemma
; simplify-mod-+-mod in ihs/quotient-remainder-lemmas.
(defthm simplify-mod-+-mod-weak
    (implies (and (not (equal y 0))
                  (bind-free
                   (simplify-mod-+-mod-fn x y mfc state)
                   (w z))
                  (rationalp-guard w x y z)
                  (integerp (/ z y)))
             (equal (mod x y)
                    (mod (+ x w (- (mod w z))) y))))

(defun simplify-mod-+-minus-mod-fn (x y mfc state)
  (declare (xargs :guard (pseudo-termp x)))
  (cond ((eq (fn-symb x) 'BINARY-+)
         (let ((arg1 (fargn x 1))
               (arg2 (fargn x 2)))
           (cond ((and (eq (fn-symb arg1) 'UNARY--)
                       (eq (fn-symb (fargn arg1 1)) 'MOD)
                       (proveably-integer
                        `(BINARY-* ,(fargn (fargn arg1 1) 2) (UNARY-/ ,y))
                        mfc state))
                  (list (cons 'w (fargn (fargn arg1 1) 1))
                        (cons 'z (fargn (fargn arg1 1) 2))))
                 ((eq (fn-symb arg2) 'BINARY-+)
                  (simplify-mod-+-minus-mod-fn arg2 y mfc state))
                 ((and (eq (fn-symb arg2) 'UNARY--)
                       (eq (fn-symb (fargn arg2 1)) 'MOD)
                       (proveably-integer
                        `(BINARY-* ,(fargn (fargn arg2 1) 2) (UNARY-/ ,y))
                        mfc state))
                  (list (cons 'w (fargn (fargn arg2 1) 1))
                        (cons 'z (fargn (fargn arg2 1) 2))))
                 (t
                  nil))))
         ((and (eq (fn-symb x) 'UNARY--)
               (eq (fn-symb (fargn x 1)) 'MOD)
              (proveably-integer
               `(BINARY-* ,(fargn (fargn x 1) 2) (UNARY-/ ,y))
               mfc state))
         (list (cons 'w (fargn (fargn x 1) 1))
               (cons 'z (fargn (fargn x 1) 2))))
        (t
         nil)))

(defthm simplify-mod-+-minus-mod
    (implies (and (not (equal y 0))
                  (bind-free
                   (simplify-mod-+-minus-mod-fn x y mfc state)
                   (w z))
                  (rationalp-guard w x y z)
                  (integerp (/ z y)))
             (equal (mod x y)
                    (mod (+ x (- w) (mod w z)) y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
(thm
 (implies (and (integerp a)
               (integerp b)
               (integerp y)
               (not (equal 0 y))
               (integerp z)
               (not (equal 0 z))
               (integerp (/ y z)))
          (equal (mod (* a (mod b y)) z)
                 (mod (* a b) z))))|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm floor-0-local-2
  (equal (floor 0 x)
         0)))

; Name changed 3/15/2016 by Matt K. to avoid name clash with lemma
; floor-floor-integer in ihs/quotient-remainder-lemmas.  (Interestingly, other
; than the use of real-rationalp in that other lemma, the lemma below is the
; stronger of the two.)
(defthm floor-floor-integer-alt
    (implies (and (rationalp x)
                  (integerp i)
                  (integerp j)
                  (<= 0 j))
             (equal (floor (floor x i) j)
                    (floor x (* i j)))))

;;-----------------------------------------------------------------
;;
;; Simple reductions
;;
;;-----------------------------------------------------------------

(defthm mod-two
  (implies (integerp x)
	   (or (equal (mod x 2) 0)
	       (equal (mod x 2) 1)))
  :rule-classes ((:forward-chaining
		  :corollary
		  (implies (integerp x)
			   (and (<= 0 (mod x 2))
				(< (mod x 2) 2)))
		  :trigger-terms ((mod x 2)))
		 (:generalize)))

(defthm floor-0
    (and (equal (floor x 0)
                0)
         (equal (floor 0 y)
                0)))

(defthm mod-0
    (and (equal (mod 0 y)
                0)
         (equal (mod x 0)
                (fix x))))

(defthm floor-x-1
    (implies (integerp x)
             (equal (floor x 1)
                    x)))

(defthm mod-x-1
    (implies (integerp x)
             (equal (mod x 1)
                    0)))
