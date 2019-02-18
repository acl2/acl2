; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; top.lisp
;;;
;;;
;;; This book collects all the other books together in one place,
;;; establishes a couple of useful theory collections, and sets up
;;; a default starting point.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "build/ground-zero-theory.certdep" :dir :system)

(deftheory-static arithmetic-5-current-base
  ;; Presumably the same as 'ground-zero
  (current-theory :here))

(deftheory-static arithmetic-5-universal-base
  (universal-theory :here))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This book defines some theories we will use below.
(include-book "lib/basic-ops/top")

(include-book "lib/floor-mod/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftheory-static arithmetic-5-current-full
  (current-theory :here))

(deftheory-static arithmetic-5-universal-full
  (universal-theory :here))

;;; Now, let us build our theories piece by piece.  This could be done
;;; more efficiently, but slow and simple wins the race.

(deftheory minimal-arithmetic-5-base
  ;; We want ACL2's base here.
  (theory 'arithmetic-5-current-base))

(deftheory default-arithmetic-5-base
  ;; Rules from the base (whether or not enabled at that time) that are enabled
  ;; in the full
  (intersection-theories (theory 'arithmetic-5-universal-base)
			 (theory 'arithmetic-5-current-full)))

(deftheory-static minimal-arithmetic-5
  ;; Using theories defined in lib/basic-ops/top.lisp
  (union-theories
   (set-difference-theories (theory 'arithmetic-5-minimal-end-a)
			    (theory 'arithmetic-5-minimal-start-a))
   (set-difference-theories (theory 'arithmetic-5-minimal-end-b)
			    (theory 'arithmetic-5-minimal-start-b))))

(deftheory default-arithmetic-5
  (set-difference-theories (theory 'arithmetic-5-current-full)
			   (theory 'arithmetic-5-current-base)))

(defmacro intersection-theories-3 (x y z)
  `(intersection-theories ,x
			  (intersection-theories ,y ,z)))

(defmacro union-theories-3 (x y z)
  `(union-theories ,x
		   (union-theories ,y ,z)))

(defmacro set-minimal-arithmetic-5-theory ()
  ;; 1. ground-zero less anything disabled by either arithmetic-5 or the user,
  ;;    i.e., those rules enabled in ground-zero that are enabled both by
  ;;    arithmetic-5 and by the user
  ;; 2. the minimal arithmetic theory
  ;; 3. whatever enabled rules the user has added (i.e. not in arithmetic-5 or
  ;;    ground-zero)
  `(in-theory (union-theories-3
               (intersection-theories-3 (theory 'minimal-arithmetic-5-base)
                                        (theory 'arithmetic-5-current-full)
                                        (current-theory :here))
	       (theory 'minimal-arithmetic-5)
	       (set-difference-theories (current-theory :here)
					(theory 'arithmetic-5-universal-full)))))

(defmacro set-default-arithmetic-5-theory ()
  `(in-theory (union-theories-3
	       (intersection-theories-3 (theory 'default-arithmetic-5-base)
                                        (theory 'arithmetic-5-current-full)
                                        (current-theory :here))
	       (theory 'default-arithmetic-5)
	       (set-difference-theories (current-theory :here)
					(theory 'arithmetic-5-universal-full)))))
