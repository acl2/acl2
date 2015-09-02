; See the top-level arithmetic-2 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; expt-helper.lisp
;;
;;
;; This book contains some messy proofs which I want to hide.
;; There is probably nothing to be gained by looking at it.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local
 (include-book "../pass1/top"))

(local
 (in-theory (disable FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT
		     FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun ind (x)
   (if (integerp x)
       (cond ((equal x 0) t)
	     ((equal x -1) t)
	     ((equal x 1) t)
	     ((< 0 x) (ind (- x 2)))
	     ((< x 0) (ind (+ x 2))))
       t)))

(local
 (encapsulate
  ()

  (local
   (defthm hack1a
     (implies (integerp x)
	      (integerp (+ -1 x)))))

  (local
   (defthm hack1b
     (implies (integerp x)
	      (integerp (+ x 1)))))

  (defthm odd-and-even
    (implies (and (integerp x)
		  (not (integerp (* 1/2 x))))
	     (integerp (+ -1/2 (* 1/2 x))))  ; (* 1/2 (- x 1))))
    :hints (("Goal" :induct (ind x))
	    ("Subgoal *1/5'''" :use ((:instance hack1a
						(x (+ 1/2 R)))))
	    ("Subgoal *1/4'''":use ((:instance hack1b
					       (x (+ -3/2 R))))))
    :rule-classes :type-prescription)

  ))


(encapsulate
 ()

 (local
  (defthm expt-x-2
    (implies (and (real/rationalp x)
		  (not (equal x 0)))
	     (< 0 (expt x 2)))))

 (local
  (defthm <-0-expt-x-2
    (implies (and (< r 0)
		  (real/rationalp r)
		  (integerp i))
	     (< 0 (expt (expt r i) 2)))
    :hints (("Goal" :use ((:instance expt-x-2
				     (x (expt r i))))))))

 (defthm expt-type-prescription-negative-base-even-exponent
   (implies (and (< r 0)
		 (real/rationalp r)
		 (integerp i)
		 (integerp (* 1/2 i)))
	    (< 0 (expt r i)))
   :rule-classes (:type-prescription :generalize)
   :hints (("Goal" :use ((:instance <-0-expt-x-2
				    (i (* 1/2 i)))))))

 (local
  (defthm reduce
    (implies (and (integerp i)
		  (real/rationalp r)
		  (not (equal r 0)))
	     (equal (expt r i)
		    (* r (expt r (- i 1)))))))

 (defthm expt-type-prescription-negative-base-odd-exponent
   (implies (and (< r 0)
		 (real/rationalp r)
		 (integerp i)
		 (not (integerp (* 1/2 i))))
	    (< (expt r i) 0))
   :rule-classes (:type-prescription :generalize)
   :hints (("Goal" :use ((:instance
			  expt-type-prescription-negative-base-even-exponent
				    (r r)
				    (i (- i 1)))
			 (:instance reduce))
	    :in-theory (disable reduce))))

 )



(defthm expt-negative-base-even-exponent
  (implies (and (real/rationalp r)
		(integerp i)
		(integerp (* 1/2 i)))
	   (equal (expt (* -1 r) i)
		  (expt r i)))
  :hints (("Goal" :induct (ind i))))

(defthm expt-negative-base-odd-exponent
  (implies (and (real/rationalp r)
		(integerp i)
		(not (integerp (* 1/2 i))))
	   (equal (expt (* -1 r) i)
		  (* -1 (expt  r i))))
  :hints (("Goal" :induct (ind i))))
