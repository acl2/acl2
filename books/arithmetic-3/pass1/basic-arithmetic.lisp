; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

;;
;; basic-arithmetic.lisp
;;

(in-package "ACL2")


(local (include-book "basic-arithmetic-helper"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Extra
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We include this definition here.  It will be used in
; inequalities and prefer-times.

(defun nonlinearp-default-hint-pass1 (stable-under-simplificationp hist pspv)
  (cond (stable-under-simplificationp
         (if (access rewrite-constant
                     (access prove-spec-var pspv :rewrite-constant)
                     :nonlinearp)
             nil
           '(:computed-hint-replacement t
                                        :nonlinearp t)))
        ((access rewrite-constant
                 (access prove-spec-var pspv :rewrite-constant)
                 :nonlinearp)
         (if (equal (caar hist) 'SETTLED-DOWN-CLAUSE)
             nil
           '(:computed-hint-replacement t
                                        :nonlinearp nil)))
        (t
         nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Facts about + (and -)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm commutativity-2-of-+
  (equal (+ x (+ y z))
         (+ y (+ x z))))

(defthm functional-self-inversion-of-minus
  (equal (- (- x))
         (fix x)))

(defthm distributivity-of-minus-over-+
  (equal (- (+ x y))
         (+ (- x) (- y))))

(defthm minus-cancellation-on-right
  (equal (+ x y (- x))
         (fix y)))

(defthm minus-cancellation-on-left
  (equal (+ x (- x) y)
         (fix y)))

; Note that the cancellation rules below (and similarly for *) aren't
; complete, in the sense that the element to cancel could be on the
; left side of one expression and the right side of the other.  But
; perhaps those situations rarely arise in practice.  (?)

(defthm right-cancellation-for-+
  (equal (equal (+ x z)
                (+ y z))
         (equal (fix x) (fix y))))

(defthm left-cancellation-for-+
  (equal (equal (+ x y)
                (+ x z))
         (equal (fix y) (fix z))))

(defthm equal-minus-0
  (equal (equal (- x) 0)
         (equal (fix x) 0)))

;; This rule causes trouble occasionally.  So I restrict its usage
;; to the simple case of two things being added by the syntaxp
;; hypothesis.

(defthm equal-+-x-y-0
  (implies (syntaxp (not (and (consp y)
			      (equal (car y) 'binary-+))))
	   (equal (equal (+ x y) 0)
		  (and (equal (fix x) (- y))
		       (equal (- x) (fix y))))))

(defthm equal-+-x-y-x
  (equal (equal (+ x y) x)
         (and (acl2-numberp x)
	      (equal (fix y) 0))))

(defthm equal-+-x-y-y
  (equal (equal (+ x y) y)
	 (and (acl2-numberp y)
	      (equal (fix x) 0))))

(defthm equal-minus-minus
  (equal (equal (- a) (- b))
         (equal (fix a) (fix b))))

(defthm fold-consts-in-+
  (implies (and (syntaxp (quotep x))
		(syntaxp (quotep y)))
	   (equal (+ x (+ y z))
		  (+ (+ x y) z))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Facts about * (and /)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Some of the following are actually proved in basics.lisp.

(defthm commutativity-2-of-*
   (equal (* x (* y z))
          (* y (* x z))))

(defthm functional-self-inversion-of-/
  (equal (/ (/ x)) (fix x)))

(defthm distributivity-of-/-over-*
  (equal (/ (* x y))
	 (* (/ x) (/ y))))

(defthm /-cancellation-on-right
  (equal (* y x (/ y))
	 (if (not (equal (fix y) 0))
	     (fix x)
	     0)))

(defthm /-cancellation-on-left
  (equal (* y (/ y) x)
	 (if (not (equal (fix y) 0))
	     (fix x)
	     0)))

(defthm right-cancellation-for-*
  (equal (equal (* x z) (* y z))
	 (or (equal 0 (fix z))
	     (equal (fix x) (fix y)))))

(defthm left-cancellation-for-*
  (equal (equal (* z x) (* z y))
         (or (equal 0 (fix z))
             (equal (fix x) (fix y)))))

(defthm equal-/-0
  (equal (equal (/ x) 0)
	 (equal (fix x) 0)))

(defthm equal-*-x-y-0
  (equal (equal (* x y) 0)
	 (or (equal (fix x) 0)
	     (equal (fix y) 0))))

(defthm equal-*-x-y-x
  (equal (equal (* x y) x)
	 (and (acl2-numberp x)
	      (or (equal x 0)
		  (equal y 1))))
  :hints (("Goal" :use
           ((:instance right-cancellation-for-*
                       (z x)
                       (x y)
                       (y 1))))))

(defthm equal-*-y-x-x
  (equal (equal (* y x) x)
	 (and (acl2-numberp x)
	      (or (equal x 0)
		  (equal y 1)))))

(defthm equal-/-/
  (equal (equal (/ a) (/ b))
	 (equal (fix a) (fix b))))

(defthm fold-consts-in-*
  (implies (and (syntaxp (quotep x))
		(syntaxp (quotep y)))
	   (equal (* x (* y z))
		  (* (* x y) z))))

;; Note that the inverse rule can also be usefull.
;; We cannot include both of them though since this
;; may cause looping.  The inverse rule:
;;
;; (defthm Uniqueness-of-*-inverses
;;   (equal (equal (* x y)
;; 		   1)
;; 	    (and (not (equal (fix x) 0))
;;	         (equal y (/ x))))
;;
;; is included in mini-theories.

(defthm equal-/
  (equal (equal (/ x) y)
	 (if (not (equal (fix x) 0))
	     (equal 1 (* x y))
	     (equal y 0))))

; The following hack helps in the application of equal-/ when
; forcing is turned off.

(defthm numerator-nonzero-forward
  (implies (not (equal (numerator r) 0))
           (and (not (equal r 0))
                (acl2-numberp r)))
  :rule-classes
  ((:forward-chaining :trigger-terms
                      ((numerator r)))))

;; We could prove an analogous rule about non-numeric coefficients, but
;; this one has efficiency advantages:  it doesn't match too often, it has
;; no hypothesis, and also we know that the 0 is the first argument so we
;; don't need two versions.  Besides, we won't need this too often; it's
;; a type-reasoning fact.  But it did seem useful in the proof of a meta
;; lemma about times cancellation, so we include it here.

(defthm times-zero
  (equal (* 0 x) 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Facts about + (or -) and * (or /) together
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm functional-commutativity-of-minus-*-right
  (implies (syntaxp (not (quotep y)))
           (equal (* x (- y))
                  (- (* x y)))))

(defthm functional-commutativity-of-minus-*-left
  (implies (syntaxp (not (quotep x)))
           (equal (* (- x) y)
                  (- (* x y)))))

(defthm reciprocal-minus-a
  (equal (/ (- x))
         (- (/ x))))
