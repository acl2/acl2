; See the top-level arithmetic-2 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; post.lisp
;;;
;;;
;;;
;;; This is the last book to be loaded.  The capitalized rules
;;; analogues of rules from axioms.lisp which are disabled.
;;; We do it this way so that the rules will be seen before
;;; any of the meta-rules, rather than afterwards as it would
;;; be otherwise.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "../pass1/top"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defthm |(+ (+ x y) z)|   ; Associativity-of-+
  (equal (+ (+ x y) z)
         (+ x (+ y z))))

(defthm |(+ 0 x)|   ; Unicity-of-0
  (equal (+ 0 x)
         (fix x)))

(defthm |(+ x 0)|   ; Unicity-of-0
  (equal (+ x 0)
         (fix x)))

(defthm |(+ c (+ d x))|
  (implies (and (syntaxp (quotep c))
		(syntaxp (quotep d)))
	   (equal (+ c (+ d x))
		  (+ (+ c d) x))))

(defthm |(- (- x))|
  (equal (- (- x))
         (fix x)))

(defthm |(- (+ x y))|
  (equal (- (+ x y))
         (+ (- x) (- y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm |(* (* x y) z)|   ; Associativity-of-*
  (equal (* (* x y) z)
         (* x (* y z))))

(defthm |(* 1 x)|   ; Unicity-of-1
  (equal (* 1 x)
         (fix x)))

(defthm |(* x 1)|   ; Unicity-of-1
  (equal (* x 1)
         (fix x)))

(defthm |(* 0 x)|
  (equal (* 0 x)
         0))

(defthm |(* x 0)|
  (equal (* x 0)
         0))

(defthm |(* -1 x)|
  (equal (* -1 x)
         (- x)))

(defthm |(* x -1)|
  (equal (* x -1)
         (- x)))

(defthm |(* c (* d x))|
  (implies (and (syntaxp (quotep c))
		(syntaxp (quotep d)))
	   (equal (* c (* d x))
		  (* (* c d) x))))

(defthm |(/ (/ x))|
  (equal (/ (/ x))
         (fix x)))

(defthm |(/ (* x y))|
  (equal (/ (* x y))
	 (* (/ x) (/ y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm |(* x (+ y z))|
  (equal (* x (+ y z))
         (+ (* x y) (* x z))))

(local
 (in-theory (disable distributivity)))

(defthm |(* (+ x y) z)|
  (equal (* (+ x y) z)
	 (+ (* x z) (* y z))))

(defthm |(* x (- y))|
  (implies (syntaxp (not (and (consp y)
			      (fquotep y)
			      (acl2-numberp (cadr y)))))
	   (equal (* x (- y))
		  (- (* x y)))))

(defthm |(* (- x) y)|
  (implies (syntaxp (not (and (consp x)
			      (fquotep x)
			      (acl2-numberp (cadr x)))))
	   (equal (* (- x) y)
		  (- (* x y)))))

(defthm |(- (* c x))|
  (implies (syntaxp (and (consp c)
			 (fquotep c)
			 (acl2-numberp (cadr c))))
	   (equal (- (* c x))
		  (* (- c) x))))

(defthm |(/ (- x))|
  (implies (syntaxp (not (and (consp x)
			      (fquotep x)
			      (acl2-numberp (cadr x)))))
  (equal (/ (- x))
         (- (/ x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We take care of a few of the simple, and exceptional, cases
; here, rather than worry about them in the meta-rules.

(defthm |(equal (/ x) 0)|
  (equal (equal (/ x) 0)
	 (equal (fix x) 0)))

(defthm |(equal (- x) 0)|
  (equal (equal (- x) 0)
	 (equal (fix x) 0)))

(defthm |(equal (/ x) (/ y))|
  (equal (equal (/ x) (/ y))
	 (equal (fix x) (fix y))))

(defthm |(equal (- x) (- y))|
  (equal (equal (- x) (- y))
	 (equal (fix x) (fix y))))

(defthm |(< (/ x) 0)|
  (implies (real/rationalp x)
	   (equal (< (/ x) 0)
		  (< (fix x) 0))))

(defthm |(< 0 (/ x))|
  (implies (real/rationalp x)
	   (equal (< 0 (/ x))
		  (< 0 (fix x)))))

(defthm |(< (- x) 0)|
  (equal (< (- x) 0)
	 (< 0 (fix x))))

(defthm |(< 0 (- x))|
  (equal (< 0 (- x))
	 (< (fix x) 0)))

(defthm |(< (- x) (- y))|
  (equal (< (- x) (- y))
	 (< (fix y) (fix x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; Finally, a few if normalization rules.

(defthm |(+ (if x y z) w)|
  (equal (+ (if x y z) w)
	 (if x (+ y w) (+ z w))))

(defthm |(+ w (if x y z))|
  (equal (+ w (if x y z))
	 (if x (+ w y) (+ w z))))

(defthm |(- (if x y z))|
  (equal (- (if x y z))
	 (if x (- y) (- z))))

(defthm |(* (if x y z) w)|
  (equal (* (if x y z) w)
	 (if x (* y w) (* z w))))

(defthm |(* w (if x y z))|
  (equal (* w (if x y z))
	 (if x (* w y) (* w z))))

(defthm |(/ (if x y z))|
  (equal (/ (if x y z))
	 (if x (/ y) (/ z))))

(defthm |(expt (if x y z) w)|
  (equal (expt (if x y z) w)
	 (if x (expt y w) (expt z w))))

(defthm |(expt w (if x y z))|
  (equal (expt w (if x y z))
	 (if x (expt w y) (expt w z))))

(defthm |(equal w (if x y z))|
  (equal (equal w (if x y z))
	 (if x (equal w y) (equal w z))))

(defthm |(equal (if x y z) w)|
  (equal (equal (if x y z) w)
	 (if x (equal y w) (equal z w))))

(defthm |(< w (if x y z))|
  (equal (< w (if x y z))
	 (if x (< w y) (< w z))))

(defthm |(< (if x y z) w)|
  (equal (< (if x y z) w)
	 (if x (< y w) (< z w))))
