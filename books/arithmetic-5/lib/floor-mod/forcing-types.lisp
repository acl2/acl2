; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; forcing-types.lisp
;;;
;;; We want to ensure that the arguments to arithmetic functions are
;;; known to be of the appropriate type.
;;;
;;; See the comments in ../basic-ops/forcing-types.lisp
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "../basic-ops/building-blocks")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm default-floor-ratio
  (implies (syntaxp (not (proveably-real/rational '(BINARY-* x (UNARY-/ y))
						  `((x . ,x) (y . ,y))
						  mfc state)))
	   (equal (floor x y)
		  (if (real/rationalp (/ x y))
		      (floor x y)
		    0))))

(defthm default-floor-1
  (implies (syntaxp (not (proveably-acl2-numberp 'x `((x . ,x)) mfc state)))
	   (equal (floor x y)
		  (if (acl2-numberp x)
		      (floor x y)
		    0))))

(defthm default-floor-2
  (implies (syntaxp (not (proveably-acl2-numberp 'y `((y . ,y)) mfc state)))
	   (equal (floor x y)
		  (if (acl2-numberp y)
		      (floor x y)
		    0))))

(defthm default-mod-ratio
  (implies (syntaxp (not (proveably-real/rational '(BINARY-* x (UNARY-/ y))
					     `((x . ,x) (y . ,y))
					     mfc state)))
	   (equal (mod x y)
		  (if (real/rationalp (/ x y))
		      (mod x y)
		    (if (acl2-numberp x)
			x
		      0)))))

(defthm default-mod-1
  (implies (syntaxp (not (proveably-acl2-numberp 'x `((x . ,x)) mfc state)))
	   (equal (mod x y)
		  (if (acl2-numberp x)
		      (mod x y)
		    0))))

(defthm default-mod-2
  (implies (syntaxp (not (proveably-acl2-numberp 'y `((y . ,y)) mfc state)))
	   (equal (mod x y)
		  (if (acl2-numberp y)
		      (mod x y)
		    (if (acl2-numberp x)
			x
		      0)))))

(defthm default-logand-1
  (implies (syntaxp (not (proveably-integer 'x `((x . ,x)) mfc state)))
	   (equal (logand x y)
		  (if (integerp x)
		      (logand x y)
		    0))))

(defthm default-logand-2
  (implies (syntaxp (not (proveably-integer 'y `((y . ,y)) mfc state)))
	   (equal (logand x y)
		  (if (integerp y)
		      (logand x y)
		    0))))

(defthm default-logior-1
  (implies (syntaxp (not (proveably-integer 'x `((x . ,x)) mfc state)))
	   (equal (logior x y)
		  (if (integerp x)
		      (logior x y)
		    (logior 0 y)))))

(defthm default-logior-2
  (implies (syntaxp (not (proveably-integer 'y `((y . ,y)) mfc state)))
	   (equal (logior x y)
		  (if (integerp y)
		      (logior x y)
		    (logior x 0)))))

(defthm default-logxor-1
  (implies (syntaxp (not (proveably-integer 'x `((x . ,x)) mfc state)))
	   (equal (logxor x y)
		  (if (integerp x)
		      (logxor x y)
		    (logxor 0 y)))))

(defthm default-logxor-2
  (implies (syntaxp (not (proveably-integer 'y `((y . ,y)) mfc state)))
	   (equal (logxor x y)
		  (if (integerp y)
		      (logxor x y)
		    (logxor x 0)))))

(defthm default-lognot
  (implies (syntaxp (not (proveably-integer 'x `((x . ,x)) mfc state)))
	   (equal (lognot x)
		  (if (integerp x)
		      (lognot x)
		    -1))))
