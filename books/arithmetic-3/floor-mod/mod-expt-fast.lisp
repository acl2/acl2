; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; This book is a modification, primarily by Robert Krug, of one submitted by
;;; Warren Hunt.  It contains an optimized version of mod-expt ---
;;; mod-expt-fast.  NOTE: Users of GCL Versions 2.7.0 and beyond can probably
;;; get optimal performance by using the built-in function mod-expt rather than
;;; using mod-expt-fast.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (include-book "../bind-free/top"))

(local
 (include-book "floor-mod"))

(local
 (SET-DEFAULT-HINTS '((NONLINEARP-DEFAULT-HINT STABLE-UNDER-SIMPLIFICATIONP
					       HIST PSPV))))

(local (in-theory (e/d (ash-to-floor) (ash))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The following theorems really should have been included in
;;; floor-mod.lisp.

(local
 (defthm mod-theorem-one
   (implies (and (rationalp a)
		 (integerp b)
		 (rationalp n)
		 (not (equal n 0)))
	    (equal (mod (* b (mod a n)) n)
		   (mod (* a b) n)))))

(local
 (encapsulate ()

  (local
   (defun ind-fn (i)
     (if (zp i)
	 t
       (ind-fn (+ -1 i)))))

  (local
   (scatter-exponents))

  (local
   (defthm mod-theorem-two-helper-helper
     (IMPLIES (AND (NOT (ZP I))
		   (EQUAL (MOD (EXPT A I) N)
			  (MOD (EXPT (MOD A N) I) N))
		   (INTEGERP A)
		   (integerp b)
		   (INTEGERP N)
		   (NOT (EQUAL N 0)))
	      (EQUAL (MOD (* b (EXPT (MOD A N) I)) N)
		     (MOD (* b (EXPT A I)) N)))
     :hints (("Goal" :induct (ind-fn b)))))

  ;; This helper, and ones like it, irritate me.  ACL2 failed to prove
  ;; theorem two, with the subgoal:

  ;; (IMPLIES (AND (NOT (ZP I))
  ;;               (EQUAL (MOD (EXPT A (+ -1 I)) N)
  ;;                      (MOD (EXPT (MOD A N) (+ -1 I)) N))
  ;;               (INTEGERP A)
  ;;               (INTEGERP N)
  ;;               (NOT (EQUAL N 0)))
  ;;          (EQUAL (MOD (EXPT (MOD A N) I) N)
  ;;                 (MOD (EXPT A I) N)))

  ;; but (EXPT A (+ -1 I)) expand to (* (/ A) (EXPT A I)) and thus
  ;; introduces division which is always harder to reason about than
  ;; multiplication.  It would be nice if ACL2 could induct with a base
  ;; case of I and an inductive case of (+ 1 I), rather than using a
  ;; base case of (+ -1 I) and an inductive case of I.  But this is not
  ;; going to happen.

  (local
   (defthm mod-theorem-two-helper
     (IMPLIES (AND (NOT (ZP I))
		   (EQUAL (MOD (EXPT A I) N)
			  (MOD (EXPT (MOD A N) I) N))
		   (INTEGERP A)
		   (INTEGERP N)
		   (NOT (EQUAL N 0)))
	      (EQUAL (MOD (EXPT (MOD A N) (+ 1 I)) N)
		     (MOD (EXPT A (+ 1 I)) N)))))

  (local
   (gather-exponents))

  (defthm mod-theorem-two
    (implies (and (integerp a)
		  (integerp i)
		  (<= 0 i)
		  (integerp n)
		  (not (equal n 0)))
	     (equal (mod (expt (mod a n) i) n)
		    (mod (expt a i) n)))
    :hints (("Goal" :induct (ind-fn i)
	     :do-not '(generalize))
	    ("Subgoal *1/2''" :cases ((equal i 1)))
	    ("Subgoal *1/2.2" :use (:instance mod-theorem-two-helper
					      (i (+ -1 i)))
	     :in-theory (disable mod-theorem-two-helper))))

  ))

(local
 (defthm mod-theorem-three
   (implies (and (integerp a)
		 (integerp i)
		 (<= 0 i)
		 (integerp n)
		 (not (equal n 0))
		 (integerp x))
	    (equal (mod (* x (expt (mod a n) i)) n)
		   (mod (* x (expt a i)) n)))
   :hints (("Goal" :use ((:instance mod-theorem-one
				    (a (expt (mod a n) i))
				    (b x))
			 (:instance mod-theorem-one
				    (a (expt a i))
				    (b x)))
	    :in-theory (disable mod-theorem-one)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Here is a recursive definition (* acc (mod (expt a i) n)):

(defun mod-expt-fast-1 (a i n acc)
  (declare (xargs :guard (and (integerp a)
                              (natp i)
                              (integerp n)
                              (< 0 n)
                              (integerp acc))))
  (if (zp i)
      acc
    ;; Divide by 2 using right shift
    (let ((floor-i-by-2 (ash i -1)))
      (if (oddp i)
	  (mod-expt-fast-1 (mod (* a a) n)
                           floor-i-by-2
                           n
                           (mod (* a acc) n))
	(mod-expt-fast-1 (mod (* a a) n)
                         floor-i-by-2
                         n
                         acc)))))

(local
 (defthm mod-expt-fast-1-as-mod-and-expt
   (implies (and (integerp a)
		 (natp i)
		 (integerp n)
		 (< 0 n)
		 (natp acc)
		 (< acc n))
	    (equal (mod-expt-fast-1 a i n acc)
		   (mod (* acc (expt a i)) n)))))

(defthm mod-expt-fast-is-mod-expt
  (implies (and (integerp a)
                (natp i)
                (integerp n)
                (< 1 n))
           (equal (mod-expt-fast-1 a i n 1)
                  (mod-expt a i n))))

; WARNING: If you are using GCL Version 2.7.0 or beyond, consider using
; mod-expt instead of mod-expt-fast for better performance.
; Note: (mod-expt-fast-1 3 0 1 7) = 7, so the test (< 1 n) below is at least
; somewhat necessary.
(defun mod-expt-fast (a i n)
  (declare (xargs :guard (and (rationalp a)
                              (integerp i)
                              (not (and (eql a 0) (< i 0)))
                              (<= 0 i)
                              (rationalp n)
                              (not (eql n 0)))))
  (mbe :exec
       (cond ((not (integerp a))
              (mod (expt a i) n))
             ((and (integerp n) (< 1 n))
              (mod-expt-fast-1 a i n 1))
             ((eql n 1)
              0)
             (t
              (mod (expt a i) n)))
       :logic
       (mod (expt a i) n)))

