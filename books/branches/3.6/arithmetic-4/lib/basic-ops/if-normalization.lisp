
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; if-normalization.lisp
;;;
;;; We have found it useful to normalize if expressions involving
;;; arithmetic operators.
;;;
;;; I probably shouldn't be calling this normalization, since all we
;;; are really doing is lifting if expressions over certain arithmetic
;;; expressions.  Perhaps in some future cleanup I will rename this
;;; file.
;;;
;;; Note: Some documentation on just how this is useful would be nice.
;;; Where (when) do if expressions get introduced?  Why does this
;;; lifting help?  What fails if this is disabled?
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "building-blocks")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm |(+ (if a b c) x)|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (+ (if a b c) x)
		  (if a (+ b x) (+ c x)))))

(defthm |(+ x (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (+ x (if a b c))
		  (if a (+ x b) (+ x c)))))

(defthm |(- (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (- (if a b c))
		  (if a (- b) (- c)))))

(defthm |(* (if a b c) x)|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (* (if a b c) x)
		  (if a (* b x) (* c x)))))

(defthm |(* x (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (* x (if a b c))
		  (if a (* x b) (* x c)))))

(defthm |(/ (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (/ (if a b c))
		  (if a (/ b) (/ c)))))

(defthm |(expt (if a b c) x)|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (expt (if a b c) x)
		  (if a (expt b x) (expt c x)))))

(defthm |(expt x (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (expt x (if a b c))
		  (if a (expt x b) (expt x c)))))

(defthm |(equal x (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (equal x (if a b c))
		  (if a (equal x b) (equal x c)))))

(defthm |(equal (if a b c) x)|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (equal (if a b c) x)
		  (if a (equal b x) (equal c x)))))

(defthm |(< x (if a b c))|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (< x (if a b c))
		  (if a (< x b) (< x c)))))

(defthm |(< (if a b c) x)|
  (implies (syntaxp (ok-to-lift-p a))
	   (equal (< (if a b c) x)
		  (if a (< b x) (< c x)))))
