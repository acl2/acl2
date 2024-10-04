;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; MAETT-lemmas1.lisp
; Author  Jun Sawada, University of Texas at Austin
;
;  This book contains various lemmas about the FM9801 and its MAETT
;  abstraction.  This book continues to another book MAETT-lemmas2.lisp. 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "MA2-lemmas")
(include-book "invariants-def")

(deflabel begin-MAETT-lemmas1)

; Index
;   INST-in subtrace-p INST-in-order and related lemmas
;   Def and lemmas about ISA-before specultv-before?, modified-inst-before?
;   and ISA-before.
;   Redefining MA-stepn
;   Misc Lemmas
;   Lemmas about stages
;     Basic Lemmas
;     Theory  about  dispatched and committed instructions
;   Lemmas about init-MT
;   Lemmas about micro-architecture
;   Lemmas about stages after step-INST
;   Lemmas about INST-functions and step-INST
;   Lemmas about relations between instructions
;   Lemmas to open INST-inv
;     Lemmas after this are in MAETT-lemmas2.lisp
;   Lemmas about relations between MT and MA
;     relations between exception events
;     (this part occupies 60% of the whole file)
;   Lemmas about micro-architecture satisfying invariants.
;   Lemmas about stages after step-INST, again.
;   Lemmas about commit again.
;   Lemmas about no-commit-inst-p and no-dispatched-inst-p
;   Lemmas about MT-no-jmp-exintr-before

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;   INST-in subtrace-p INST-in-order and related lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun head-p (x y)
  (if (endp x)
      t
      (if (endp y)
	  nil
	  (and (equal (car x) (car y))
	       (head-p (cdr x) (cdr y))))))

(defun tail-p (sublist list)
  (declare (xargs :guard (and (true-listp sublist) (true-listp list))))
  (if (equal sublist list)
      T
      (if (endp list)
	  nil
	  (tail-p sublist (cdr list)))))

(defun tail-after-p (elm sub lst)
  (declare (xargs :guard (and (true-listp sub) (true-listp lst))))
  (tail-p sub (cdr (member-equal elm lst))))

(defun member-in-order (elm1 elm2 lst)
  (declare (xargs :guard (true-listp lst)))
  (member-equal elm2 (cdr (member-equal elm1 lst))))

(defthm member-equal-car-of-tail-p
    (implies (and (consp sub) (tail-p sub lst))
	     (member-equal (car sub) lst)))

(defthm tail-p-cdr-1
    (implies (and (consp sub) (tail-p sub lst))
	     (tail-p (cdr sub) lst)))

(defthm tail-p-nil
    (implies (true-listp list)
	     (tail-p nil list))) 

(defthm tail-p-transitivity
    (implies (and (tail-p lst1 lst2) (tail-p lst2 lst3))
	     (tail-p lst1 lst3)))

(defthm tail-p-member-equal
    (implies (and (tail-p lst1 lst2) (member-equal elm lst1))
	     (member-equal elm lst2)))

(in-theory (disable tail-p-transitivity tail-p-member-equal))

(defthm tail-p-cdr-2
    (implies (consp lst) (not (tail-p lst (cdr lst))))
  :hints (("Goal" :induct (len lst))))

(defthm tail-antisymmetry
    (implies (and (not (equal x y)) (tail-p x y))
	     (not (tail-p y x)))
  :rule-classes nil)

(defthm tail-p-antisymmetry
    (implies (and (tail-p sub lst) (not (equal sub lst)))
	     (not (tail-p lst sub))))

(defthm tail-p-cddr
    (implies (consp (cdr lst))
	     (not (tail-p lst (cddr lst)))))

(defthm tail-after-p*
    (equal (tail-after-p elm sub lst)
	   (if (endp lst)
	       (null sub)
	       (if (equal elm (car lst))
		   (tail-p sub (cdr lst))
		   (tail-after-p elm sub (cdr lst)))))
  :rule-classes :definition)
(in-theory (disable tail-after-p*))

(defthm tail-after-p-nil
    (implies (true-listp lst)
	     (tail-after-p elm nil lst)))

(defthm tail-after-p-cdr
    (implies (and (consp sub) (tail-after-p elm sub lst))
	     (tail-after-p elm (cdr sub) lst)))

(defthm tail-after-p-car-cdr
    (implies (and (consp sub) (tail-p sub lst))
	     (tail-after-p (car sub) (cdr sub) lst))
  :hints (("goal" :in-theory (enable tail-after-p*))))

(in-theory (disable tail-after-p member-in-order))

(defun INST-in (i MT)
  (declare (xargs :guard (and (INST-p i) (MAETT-p MT))))
  (member-equal i (MT-trace MT)))

(defun subtrace-p (trace MT)
  (declare (xargs :guard (and (INST-listp trace) (MAETT-p MT))))
  (tail-p trace (MT-trace MT)))

(defun subtrace-after-p (elm sub MT)
  (declare (xargs :guard (and (INST-p elm) (INST-listp sub) (MAETT-p MT))))
  (tail-after-p elm sub (MT-trace MT)))

(defun INST-in-order-p (i1 i2 MT)
  (declare (xargs :guard (and (INST-p i1) (INST-p i2)
			      (MAETT-p MT))))
  (member-in-order i1 i2 (MT-trace MT)))

(defthm INST-in-car-of-subtrace
    (implies (and (consp trace) (subtrace-p trace MT))
	     (INST-in (car trace) MT)))

(defthm member-of-subtrace
    (implies (and (member-equal i trace)
		  (subtrace-p trace MT))
	     (INST-in i MT)))

(defthm member-in-order*
    (equal (member-in-order elm1 elm2 lst)
	   (if (endp lst)
	       nil
	       (if (equal (car lst) elm1)
		   (member-equal elm2 (cdr lst))
		   (member-in-order elm1 elm2 (cdr lst)))))
  :hints (("Goal" :in-theory (enable member-in-order)))
  :rule-classes :definition)

(in-theory (disable member-in-order*))

(defthm not-member-in-order-if-member-equal-1
    (implies (not (member-equal elm1 trace))
	     (not (member-in-order elm1 elm2 trace)))
  :hints (("Goal" :in-theory (enable member-in-order*))))

(defthm not-member-in-order-if-member-equal-2
    (implies (not (member-equal elm2 trace))
	     (not (member-in-order elm1 elm2 trace)))
  :hints (("Goal" :in-theory (enable member-in-order*))))

(defthm subtrace-p-MT-trace
    (subtrace-p (MT-trace MT) MT))

(defthm subtrace-p-nil
    (implies (MAETT-p MT) (subtrace-p nil MT)))

(defthm subtrace-p-cdr
    (implies (and (consp trace) (subtrace-p trace MT))
	     (subtrace-p (cdr trace) MT)))

(defthm subtrace-tail-p
    (implies (and (tail-p sub trace) (subtrace-p trace MT))
	     (subtrace-p sub MT))
  :hints (("goal" :in-theory (enable subtrace-p))))

(defthm subtrace-after-p-nil
    (implies (MAETT-p MT)
	     (subtrace-after-p i nil MT)))

(defthm subtrace-after-p-cdr
    (implies (and (consp trace) (subtrace-after-p i trace MT))
	     (subtrace-after-p i (cdr trace) MT)))

(defthm subtrace-after-p-car-cdr
    (implies (and (consp trace) (subtrace-p trace MT))
	     (subtrace-after-p (car trace) (cdr trace) MT)))

(encapsulate nil
(local
(defthm subtrace-p-subtrace-after-p-help
    (implies (and (INST-listp trace) (tail-after-p i sub trace))
	     (tail-p sub trace))
  :hints (("goal" :in-theory (enable tail-after-p*)))))

(defthm subtrace-p-subtrace-after-p
    (implies (and (MAETT-p MT) (subtrace-after-p i trace MT))
	     (subtrace-p trace MT))
  :hints (("goal" :in-theory (enable subtrace-after-p subtrace-p))))
)

(encapsulate nil
(local
(defthm INST-in-order-car-if-subtrace-after-p-help
    (implies (and (consp sub) (tail-after-p i sub trace))
	     (member-in-order i (car sub) trace))
  :hints (("goal" :in-theory (enable tail-after-p* member-in-order*)
		  :induct (member-equal i trace)))))

(defthm INST-in-order-car-if-subtrace-after-p
    (implies (and (consp sub) (subtrace-after-p i sub MT))
	     (INST-in-order-p i (car sub) MT))
  :hints (("goal" :in-theory (enable subtrace-after-p INST-in-order-p))))
)

(encapsulate nil
(local
(defthm not-member-equal-car-help
    (implies (and (distinct-member-p trace)
 		  (tail-p sub trace))
	     (not (member-equal (car sub) (cdr sub))))))

(defthm not-member-equal-car
    (implies (and (inv MT MA)
		  (subtrace-p trace MT))
	     (not (member-equal (car trace) (cdr trace))))
  :hints (("goal" :in-theory (enable inv weak-inv
				     MT-distinct-inst-p subtrace-p)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (subtrace-p trace MT)
			   (member-equal i (cdr trace)))
		      (not (equal (car trace) i))))
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (subtrace-p trace MT)
			   (member-equal i (cdr trace)))
		      (not (equal i (car trace))))))
)
)

(encapsulate nil
(local
(defthm INST-in-order-p-car-trace-help
    (implies (and (consp trace)
		  (tail-p trace trace2) (member-equal i trace)
		  (not (equal i (car trace))))
	     (member-in-order (car trace) i trace2))
  :hints (("goal" :in-theory (enable member-in-order*)))))

(defthm INST-in-order-p-car-trace
    (implies (and (consp trace)
		  (subtrace-p trace MT) (member-equal i trace)
		  (not (equal i (car trace))))
	     (INST-in-order-p (car trace) i MT))
  :hints (("Goal" :in-theory (enable INST-in-order-p subtrace-p)
		  :do-not-induct t)))
)

(encapsulate nil
(local
(defthm member-in-order-antisymmetry
    (implies (and (distinct-member-p trace)
		  (member-in-order i j trace))
	     (not (member-in-order j i trace)))
  :hints (("goal" :in-theory (enable member-in-order*)))))

(defthm INST-in-order-antisymmetry
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in-order-p i j MT))
	     (not (INST-in-order-p j i MT)))
  :Hints (("Goal" :in-theory (enable INST-in-order-p inv
				     weak-inv
				     MT-distinct-inst-p))))
)

(encapsulate nil
(local
(defthm INST-in-order-p-total-help
    (implies (and (not (member-in-order j i trace))
		  (not (equal i j))
		  (member-equal i trace) (member-equal j trace))
	     (member-in-order i j trace))
  :hints (("goal" :in-theory (enable member-in-order*)))))

(defthm INST-in-order-p-total
    (implies (and (not (INST-in-order-p j i MT))
		  (not (equal i j))
		  (INST-in i MT) (INST-in j MT))
	     (INST-in-order-p i j MT))
  :hints (("goal" :in-theory (enable INST-in INST-in-order-p))))
)

(encapsulate nil
(local
 (defthm member-in-order-transitivity
     (implies (and (distinct-member-p trace)
		   (member-in-order i j trace)
		   (member-in-order j k trace))
	      (member-in-order i k trace))
   :hints (("Goal" :in-theory (enable member-in-order*)
		   :induct (len trace)))))

(defthm INST-in-order-transitivity
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in-order-p i j MT)
		  (INST-in-order-p j k MT))
	     (INST-in-order-p i k MT))
  :hints (("goal" :in-theory (enable inv weak-inv
				     MT-distinct-inst-p
				     INST-in-order-p)))
  :rule-classes
  ((:rewrite :corollary
	     (implies (and (INST-in-order-p j k MT)
			   (inv MT MA)
			   (MAETT-p MT) (MA-state-p MA)
			   (INST-in-order-p i j MT))
		      (INST-in-order-p i k MT)))
   (:rewrite :corollary
	     (implies (and (INST-in-order-p i j MT)
			   (inv MT MA)
			   (MAETT-p MT) (MA-state-p MA)
			   (INST-in-order-p j k MT))
		      (INST-in-order-p i k MT)))))
)

(in-theory (disable INST-in subtrace-p subtrace-after-p INST-in-order-p))

(defthm member-in-order-car-member-cdr
    (implies (and (tail-p sub trace)
		  (member-equal i (cdr sub)))
	     (member-in-order (car sub) i trace))
  :hints (("goal" :in-theory (enable member-in-order*))))

; If instruction i is a member or (cdr trace), i follows instruction
; (car trace).
(defthm INST-in-order-car-member-cdr
    (implies (and (subtrace-p trace MT)
		  (member-equal i (cdr trace)))
	     (INST-in-order-p (car trace) i MT))
  :hints (("goal" :in-theory (enable subtrace-p INST-in-order-p))))

(encapsulate nil
(local
(defthm INST-in-order-p-cars-if-tailp-help
    (implies (and (tail-p lst2 trace)
		  (tail-p lst1 lst2)
		  (consp lst1)
		  (not (equal lst1 lst2)))
	     (member-in-order (car lst2) (car lst1) trace))
  :hints (("Goal" :in-theory (enable member-in-order*)))))

(defthm INST-in-order-p-cars-if-tailp
    (implies (and (subtrace-p trace MT)
		  (tail-p sub trace)
		  (consp sub)
		  (not (equal sub trace)))
	     (INST-in-order-p (car trace) (car sub) MT)))
)

(encapsulate nil
(local
(defthm INST-in-order-p-identity-help
    (implies (and (DISTINCT-MEMBER-P trace)
		  (member-equal i trace))
	     (not (member-in-order i i trace)))
  :hints (("Goal" :in-theory (enable member-in-order*)))))
  
(defthm INST-in-order-p-identity
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA))
	     (not (INST-in-order-p i i MT)))
  :hints (("Goal" :in-theory (enable INST-in INST-in-order-p
				     inv weak-inv
				     MT-distinct-inst-p))))
)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Speculative, modified-inst, pre-ISA before a terminal subtrace.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun specultv-at-tail (sub trace spc)
  (declare (xargs :guard (and (INST-listp sub) (INST-listp trace)
			      (bitp spc))))
  (if (equal sub trace)
      spc
      (if (endp trace) spc
	  (specultv-at-tail sub (cdr trace)
			    (b-ior (inst-specultv? (car trace))
				   (INST-start-specultv? (car trace)))))))

(defthm bitp-specultv-at-tail
    (implies (bitp spc)
	     (bitp (specultv-at-tail sub trace spc))))

(defun specultv-before? (sub MT)
  (declare (xargs :guard (and (INST-listp sub) (MAETT-p MT))))
  (specultv-at-tail sub (MT-trace MT) 0))

(defthm bitp-specultv-before?
    (bitp (specultv-before? sub MT)))

(defun modified-inst-before-tail (sub trace smc)
  (declare (xargs :guard (and (INST-listp sub) (INST-listp trace)
			      (bitp smc))))
  (if (equal sub trace)
      smc
      (if (endp trace) smc
	  (modified-inst-before-tail sub (cdr trace)
				     (INST-modified? (car trace))))))

(defthm bitp-modified-inst-before-tail
    (implies (and (INST-listp trace) (bitp smc))
	     (bitp (modified-inst-before-tail sub trace smc))))

(defun modified-inst-before? (sub MT)
  (declare (xargs :guard (and (INST-listp sub) (MAETT-p MT))))
  (modified-inst-before-tail sub (MT-trace MT) 0))

(defthm bitp-modified-inst-before?
    (implies (MAETT-p MT) (bitp (modified-inst-before? sub MT))))

(defun ISA-at-tail (sub trace pre)
  (declare (xargs :guard (and (INST-listp sub) (INST-listp trace)
			      (ISA-state-p pre))))
  (if (equal sub trace)
      pre
      (if (endp trace) pre
	  (ISA-at-tail sub (cdr trace) (INST-post-ISA (car trace))))))

(defthm ISA-state-p-ISA-at-tail
    (implies (and (ISA-state-p pre)
		  (INST-listp trace))
	     (ISA-state-p (ISA-at-tail sub trace pre))))

(defun ISA-before (sub MT)
  (declare (xargs :guard (and (INST-listp sub) (MAETT-p MT))))  
  (ISA-at-tail sub (MT-trace MT) (MT-init-ISA MT)))

(defthm ISA-state-p-ISA-before
    (implies (MAETT-p MT)
	     (ISA-state-p (ISA-before sub MT))))
		       
(in-theory (disable ISA-before specultv-before? modified-inst-before?))

(encapsulate nil
(local
(defthm specultv-before-cdr-help
    (implies (and (tail-p sub trace)
		  (consp sub))
	     (equal (specultv-at-tail (cdr sub) trace spc)
		    (b-ior (inst-specultv? (car sub))
			   (INST-start-specultv? (car sub)))))))

(defthm specultv-before-cdr
    (implies (and (subtrace-p sub MT)
		  (consp sub))
	     (equal (specultv-before? (cdr sub) MT)
		    (b-ior (inst-specultv? (car sub))
			   (INST-start-specultv? (car sub)))))
  :hints (("Goal" :in-theory (enable specultv-before? 
				     subtrace-p
				     ISA-STEP-CHAIN-P))))
)

(encapsulate nil
(local 
(defthm specultv-at-tail-nil-if-trace-all-specultv
    (implies (and (trace-all-specultv-p trace)
		  (b1p spc))
	     (b1p (specultv-at-tail sub trace spc)))
  :hints (("Goal" :in-theory (enable lift-b-ops)))))

(local 
(defthm specultv-at-tail-nil
    (implies (and (trace-correct-speculation-p trace)
		  (bitp spc) (not (b1p spc)))
	     (equal (specultv-at-tail nil trace spc)
		    (trace-specultv? trace)))
  :hints (("Goal" :in-theory (enable lift-b-ops equal-b1p-converter)))))

(defthm specultv-before-nil
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA))
	     (equal (specultv-before? nil MT)
		    (MT-specultv? MT)))
  :hints (("Goal" :in-theory (enable specultv-before? MT-specultv?
				     inv
				     weak-inv correct-speculation-p))))
)

(defthm specultv-before-MT-trace
    (equal (specultv-before? (MT-trace MT) MT) 0)
  :hints (("Goal" :in-theory (enable specultv-before?))))

(encapsulate nil
(local
(defthm modified-inst-before-cdr-help
    (implies (and (tail-p sub trace)
		  (consp sub))
	     (equal (modified-inst-before-tail (cdr sub) trace spc)
		    (INST-modified? (car sub))))))

(defthm modified-inst-before-cdr
    (implies (and (subtrace-p sub MT)
		  (consp sub))
	     (equal (modified-inst-before? (cdr sub) MT)
		    (INST-modified? (car sub))))
  :hints (("Goal" :in-theory (enable modified-inst-before? weak-inv
				     inv subtrace-p
				     ISA-STEP-CHAIN-P))))
)

(encapsulate nil
(local 
(defthm modified-inst-before-tail-nil-if-trace-is-all-modified-flgs-on
    (implies (and (trace-correct-modified-flgs-p trace MT 1)
		  (b1p spc))
	     (b1p (modified-inst-before-tail sub trace spc)))
  :hints (("Goal" :in-theory (enable lift-b-ops)))))

(local 
(defthm modified-inst-before-nil-help
    (implies (and (trace-correct-modified-flgs-p trace MT 0)
		  (INST-listp trace)
		  (bitp smc)
		  (not (b1p smc)))
	     (equal (modified-inst-before-tail nil trace smc)
		    (trace-self-modify? trace)))
  :hints (("Goal" :in-theory (enable lift-b-ops equal-b1p-converter)))))

(defthm modified-inst-before-nil
    (implies (and (weak-inv MT)
		  (MAETT-p MT))
	     (equal (modified-inst-before? nil MT)
		    (MT-self-modify? MT)))
  :hints (("Goal" :in-theory (enable modified-inst-before? MT-self-modify?
				     weak-inv correct-modified-flgs-p)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (MAETT-p MT)
			   (MA-state-p MA))
		      (equal (modified-inst-before? nil MT)
			     (MT-self-modify? MT))))))

)

(defthm modified-inst-before-MT-trace
    (equal (modified-inst-before? (MT-trace MT) MT) 0)
  :hints (("Goal" :in-theory (enable modified-inst-before?))))

(encapsulate nil
(local
(defthm ISA-before-cdr-help
    (implies (and (ISA-chained-trace-p trace pre)
		  (tail-p sub trace)
		  (consp sub))
	     (equal (ISA-at-tail (cdr sub) trace pre)
		    (INST-post-ISA (car sub))))))

(defthm ISA-before-cdr
    (implies (and (weak-inv MT)
		  (subtrace-p sub MT)
		  (consp sub))
	     (equal (ISA-before (cdr sub) MT)
		    (INST-post-ISA (car sub))))
  :hints (("Goal" :in-theory (enable ISA-before weak-inv inv
				     subtrace-p
				     ISA-STEP-CHAIN-P)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (subtrace-p sub MT)
			   (consp sub))
		      (equal (ISA-before (cdr sub) MT)
			     (INST-post-ISA (car sub)))))))
)

(defthm ISA-at-tail-nil
    (equal (ISA-at-tail nil trace pre)
	   (trace-final-ISA trace pre)))

(defthm ISA-before-nil
    (equal (ISA-before nil MT)
	   (MT-final-ISA MT))
  :hints (("Goal" :in-theory (enable ISA-before MT-final-ISA))))

(defthm ISA-before-MT-trace
    (equal (ISA-before (MT-trace MT) MT)
	   (MT-init-ISA MT))
  :hints (("Goal" :in-theory (enable ISA-before))))

(encapsulate nil
(local
(defthm ISA-before-MT-non-nil-trace-help
    (implies (and (consp sub)
		  (tail-p sub trace)
		  (ISA-chained-trace-p trace pre))
	     (equal (ISA-at-tail sub trace pre)
		    (INST-pre-ISA (car sub))))))

(defthm ISA-before-MT-non-nil-trace
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (consp trace)
		  (subtrace-p trace MT))
	     (equal (ISA-before trace MT)
		    (INST-pre-ISA (car trace))))
  :hints (("Goal" :in-theory (enable weak-inv inv
				     ISA-step-chain-p
				     subtrace-p ISA-before))))
)
(in-theory (disable ISA-before-MT-non-nil-trace))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Redefining MA-stepn
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm MA-step0
    (equal (MA-stepn MA sig-lst 0) MA)
  :hints (("goal" :in-theory (enable MA-stepn))))

(defthm MA-stepn*
    (implies (<= n (len sig-lst))
	     (equal (MA-stepn MA sig-lst n)
		    (if (zp n)
			MA
			(MA-step (MA-stepn MA sig-lst (1- n))
				 (nth (1- n) sig-lst)))))
  :hints (("Goal" :in-theory (enable MA-stepn)))
  :rule-classes :definition)

(in-theory (disable MA-stepn*))

(defthm MT-stepn*
    (equal (MT-stepn MT MA sig-lst n)
	   (if (zp n)
	       MT
	       (if (< (len sig-lst) n)
		   (MT-stepn MT MA sig-lst (1- n))
		   (MT-step (MT-stepn MT MA sig-lst (1- n))
			    (MA-stepn MA sig-lst (1- n))
			    (nth (1- n) sig-lst)))))
  :hints (("Goal" :in-theory (enable MA-stepn)))
  :rule-classes :definition)
			 
(in-theory (disable MT-stepn*))

(defthm MT-trace-MT-step
    (equal (MT-trace (MT-step MT MA sigs))
	   (step-trace (MT-trace MT) MT MA sigs (MT-init-ISA MT) 0 0))
  :hints (("goal" :in-theory (enable MT-step))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Miscellaneous Lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm rob-index-p-plus
    (implies (and (<= x 0) (<= 0 (+ x y))
		  (rob-index-p y)
		  (integerp x))
	     (rob-index-p (+ x y)))
  :hints (("goal" :in-theory (enable rob-index-p unsigned-byte-p))))

(defthm ISA-extensionality
    (implies (and (ISA-state-p s1)
		  (ISA-state-p s2)
		  (equal (ISA-pc s1) (ISA-pc s2))
		  (equal (ISA-RF s1) (ISA-RF s2))
		  (equal (ISA-SRF s1) (ISA-SRF s2))
		  (equal (ISA-mem s1) (ISA-mem s2)))
	     (equal s1 s2))
  :rule-classes
  ((:rewrite :corollary
	     (implies (and (ISA-state-p s1)
			   (ISA-state-p s2)
			   (equal (ISA-pc s1) (ISA-pc s2))
			   (equal (ISA-RF s1) (ISA-RF s2))
			   (equal (ISA-SRF s1) (ISA-SRF s2))
			   (equal (ISA-mem s1) (ISA-mem s2)))
		      (equal (equal s1 s2) t)))))

(in-theory (disable ISA-extensionality))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Theories about stages
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm INST-is-at-one-of-the-stages
    (implies (INST-p i)
	     (or (IFU-stg-p (INST-stg i))
		 (DQ-stg-p (INST-stg i))
		 (EXECUTE-stg-p (INST-stg i))
		 (COMPLETE-stg-p (INST-stg i))
		 (COMMIT-stg-p (INST-stg i))
		 (RETIRE-stg-p (INST-stg i))))
  :hints (("goal" :in-theory (enable MA-stg-def)))
  :rule-classes
  ((:rewrite :corollary
	    (implies (and (INST-p i)
		  (not (IFU-stg-p (INST-stg i)))
		  (not (DQ-stg-p (INST-stg i)))
		  (not (EXECUTE-stg-p (INST-stg i)))
		  (not (COMPLETE-stg-p (INST-stg i)))
		  (not (COMMIT-stg-p (INST-stg i))))
	     (RETIRE-stg-p (INST-stg i))))))

(defthm IFU-stg-not-DQ-stg
    (implies (IFU-stg-p stg) (not (DQ-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm IFU-stg-not-execute-stg
    (implies (IFU-stg-p stg) (not (execute-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm IFU-stg-not-complete-stg
    (implies (IFU-stg-p stg) (not (complete-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm IFU-stg-not-commit-stg
    (implies (IFU-stg-p stg) (not (commit-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm IFU-stg-not-retire-stg
    (implies (IFU-stg-p stg) (not (retire-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm DQ-stg-not-IFU-stg
    (implies (DQ-stg-p stg) (not (IFU-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm DQ-stg-not-execute-stg
    (implies (DQ-stg-p stg) (not (execute-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm DQ-stg-not-complete-stg
    (implies (DQ-stg-p stg) (not (complete-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm DQ-stg-not-commit-stg
    (implies (DQ-stg-p stg) (not (commit-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm DQ-stg-not-retire-stg
    (implies (DQ-stg-p stg) (not (retire-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm execute-stg-not-IFU-stg
    (implies (execute-stg-p stg) (not (IFU-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm execute-stg-not-DQ-stg
    (implies (execute-stg-p stg) (not (DQ-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm execute-stg-not-complete-stg
    (implies (execute-stg-p stg) (not (complete-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm execute-stg-not-commit-stg
    (implies (execute-stg-p stg) (not (commit-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm execute-stg-not-retire-stg
    (implies (execute-stg-p stg) (not (retire-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm complete-stg-not-IFU-stg
    (implies (complete-stg-p stg) (not (IFU-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm complete-stg-not-DQ-stg
    (implies (complete-stg-p stg) (not (DQ-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm complete-stg-not-execute-stg
    (implies (complete-stg-p stg) (not (execute-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm complete-stg-not-commit-stg
    (implies (complete-stg-p stg) (not (commit-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm complete-stg-not-retire-stg
    (implies (complete-stg-p stg) (not (retire-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm commit-stg-not-IFU-stg
    (implies (commit-stg-p stg) (not (IFU-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm commit-stg-not-DQ-stg
    (implies (commit-stg-p stg) (not (DQ-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm commit-stg-not-execute-stg
    (implies (commit-stg-p stg) (not (execute-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm commit-stg-not-complete-stg
    (implies (commit-stg-p stg) (not (complete-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm commit-stg-not-retire-stg
    (implies (commit-stg-p stg) (not (retire-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm retire-stg-not-IFU-stg
    (implies (retire-stg-p stg) (not (IFU-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm retire-stg-not-DQ-stg
    (implies (retire-stg-p stg) (not (DQ-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm retire-stg-not-execute-stg
    (implies (retire-stg-p stg) (not (execute-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm retire-stg-not-complete-stg
    (implies (retire-stg-p stg) (not (complete-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm retire-stg-not-commit-stg
    (implies (retire-stg-p stg) (not (commit-stg-p stg)))
  :hints (("Goal" :in-theory (enable MA-stg-def))))

(defthm execute-stage-exclusive
    (and (implies (LSU-stg-p stg) (not (IU-stg-p stg)))
	 (implies (LSU-stg-p stg) (not (MU-stg-p stg)))
	 (implies (LSU-stg-p stg) (not (BU-stg-p stg)))
	 (implies (IU-stg-p stg) (not (LSU-stg-p stg)))
	 (implies (IU-stg-p stg) (not (MU-stg-p stg)))
	 (implies (IU-stg-p stg) (not (BU-stg-p stg)))	  
	 (implies (BU-stg-p stg) (not (LSU-stg-p stg)))
	 (implies (BU-stg-p stg) (not (MU-stg-p stg)))
	 (implies (BU-stg-p stg) (not (IU-stg-p stg)))	  
	 (implies (MU-stg-p stg) (not (LSU-stg-p stg)))
	 (implies (MU-stg-p stg) (not (BU-stg-p stg)))
	 (implies (MU-stg-p stg) (not (IU-stg-p stg))))
  :hints (("goal" :in-theory (enable BU-stg-p IU-stg-p MU-stg-p LSU-stg-p))))

; Wbuf-stg-p and other stages are exclusive.
(defthm wbuf-stg-not-IFU-stg
    (implies (wbuf-stg-p stg)
	     (not (IFU-stg-p stg)))
  :hints (("goal" :in-theory (enable wbuf-stg-p IFU-stg-p))))

(defthm wbuf-stg-not-dq-stg
    (implies (wbuf-stg-p stg)
	     (not (dq-stg-p stg)))
  :hints (("goal" :in-theory (enable wbuf-stg-p dq-stg-p))))

(defthm wbuf-stg-not-retire-stg
    (implies (wbuf-stg-p stg)
	     (not (retire-stg-p stg)))
  :hints (("goal" :in-theory (enable wbuf-stg-p retire-stg-p))))

(defthm wbuf0-stg-p-wbuf1-stg-p-exclusive
    (and (implies (wbuf0-stg-p i) (not (wbuf1-stg-p i)))
	 (implies (wbuf1-stg-p i) (not (wbuf0-stg-p i))))
  :hints (("goal" :in-theory (enable wbuf0-stg-p wbuf1-stg-p))))

(defthm wbuf-stg-if-wbuf0-stg
    (implies (wbuf0-stg-p stg) (wbuf-stg-p stg))
  :hints (("goal" :in-theory (enable wbuf0-stg-p wbuf-stg-p))))

(defthm wbuf-stg-if-wbuf1-stg
    (implies (wbuf1-stg-p stg) (wbuf-stg-p stg))
  :hints (("goal" :in-theory (enable wbuf1-stg-p wbuf-stg-p))))

(defthm IFU-stg-p-cons
    (implies (not (equal tag 'IFU))
	     (not (IFU-stg-p (cons tag x))))
  :hints (("goal" :in-theory (enable MA-stg-def))))

(defthm DQ-stg-p-cons
    (implies (not (equal tag 'DQ))
	     (not (DQ-stg-p (cons tag x))))
  :hints (("goal" :in-theory (enable MA-stg-def))))

(defthm execute-stg-p-cons
    (implies (and (not (equal tag 'IU))
		  (not (equal tag 'BU))
		  (not (equal tag 'LSU))
		  (not (equal tag 'MU)))
	     (not (execute-stg-p (cons tag x))))
  :hints (("goal" :in-theory (enable MA-stg-def))))

(defthm complete-stg-p-cons
    (implies (not (equal tag 'complete))
	     (not (complete-stg-p (cons tag x))))
  :hints (("goal" :in-theory (enable MA-stg-def))))

(defthm commit-stg-p-cons
    (implies (not (equal tag 'commit))
	     (not (commit-stg-p (cons tag x))))
  :hints (("goal" :in-theory (enable MA-stg-def))))

(defthm retire-stg-p-cons
    (implies (not (equal tag 'retire))
	     (not (retire-stg-p (cons tag x))))
  :hints (("goal" :in-theory (enable MA-stg-def))))

(encapsulate nil
(local
(defthm not-IFU-stg-p-if-not-last-INST-help
    (implies (and (in-order-trace-p trace)
		  (tail-p sub trace)
		  (consp sub)
		  (consp (cdr sub)))
	     (not (IFU-stg-p (INST-stg (car sub)))))))

;; The instruction at IFU stage is always at the end of a MAETT.
(defthm not-IFU-stg-p-if-not-last-INST
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT)
		  (subtrace-p trace MT)
		  (consp trace)
		  (consp (cdr trace)))
	     (not (IFU-stg-p (INST-stg (car trace)))))
  :hints (("goal" :in-theory (enable inv in-order-dispatch-commit-p
				     subtrace-p))))
)

; An instruction at IFU stage is always at the end of MAETT.  So any
; instruction j cannot be a member of (cdr trace) if (car trace) is
; IFU-stg-p.  Note: This rule is found to be useful several proofs,
; where a manual hint is required to split the case depending on
; (consp (cdr trace)) or not.
(defthm not-member-of-cdr-if-car-is-IFU-stg
    (implies (and (inv MT MA)
		  (IFU-stg-p (INST-stg (car trace)))
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (consp trace))
	     (not (member-equal j (cdr trace))))
  :hints (("goal" :cases ((consp (cdr trace))))))

(encapsulate nil
(local
(defthm IFU-is-last-inst-help
    (implies (and (in-order-trace-p trace)
		  (IFU-stg-p (INST-stg j))
		  (not (equal i j))
		  (member-equal i trace) 
		  (member-equal j trace))
	     (member-in-order i j trace))
  :hints (("goal" :in-theory (enable member-in-order*)))))
 
(defthm IFU-is-last-inst
    (implies (and (inv MT MA)
		  (IFU-stg-p (INST-stg j))
		  (not (equal i j))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) 
		  (INST-in j MT)) 
	     (INST-in-order-p i j MT))
  :hints (("goal" :in-theory (enable INST-in-order-p INST-in
				     inv in-order-dispatch-commit-p))))
)

(in-theory (disable IFU-is-last-inst )) 

(encapsulate nil
(local
(defthm lower-bound-of-DQ-stg-idx-of-member
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (member-equal j trace)
		  (DQ-stg-p (INST-stg j))
		  (in-order-DQ-trace-p trace idx))
	     (<= idx (DQ-stg-idx (INST-stg J))))
  :rule-classes nil))

(local
(defthm DQ-stg-index-monotonic-induct
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (in-order-DQ-trace-p trace idx)
		  (subtrace-p trace MT)
		  (member-in-order i j trace)
		  (DQ-stg-p (INST-stg i))
		  (DQ-stg-p (INST-stg j)))
	     (< (DQ-stg-idx (INST-stg i)) (DQ-stg-idx (INST-stg j))))
  :hints (("goal" :in-theory (enable member-in-order*))
	  (when-found (binary-+ '1 (DQ-STG-IDX (INST-STG (CAR TRACE))))
	      (:use (:instance lower-bound-of-DQ-stg-idx-of-member
			       (idx (+ 1 (DQ-STG-IDX (INST-STG (CAR TRACE)))))
			       (trace (cdr trace))))))
  :rule-classes nil))

; Dispatch queue works as a FIFO queue.  If instruction i precedes
; instruction j, and they are both in DQ-stg, DQ-stg-idx of i is smaller
; than that of j.
(defthm DQ-stg-index-monotonic
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in-order-p i j MT)
		  (DQ-stg-p (INST-stg i))
		  (DQ-stg-p (INST-stg j)))
	     (< (DQ-stg-idx (INST-stg i)) (DQ-stg-idx (INST-stg j))))
  :hints (("goal" :use (:instance DQ-stg-index-monotonic-induct
				  (trace (MT-trace MT))
				  (idx 0))
		  :in-theory (enable inv in-order-DQ-p
				     INST-in-order-p)))
  :rule-classes nil)
)

(defthm DQ0-is-earlier-than-other-DQ
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(DQ 0))
		  (not (equal i j))
		  (DQ-stg-p (INST-stg j))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-p j)
		  (INST-in i MT)
		  (INST-in j MT))
	     (INST-in-order-p i j MT))
  :hints (("goal" :use (:instance DQ-stg-index-monotonic
				  (i j) (j i)))))

(in-theory (disable DQ0-is-earlier-than-other-DQ))

(encapsulate nil
(local
(defthm non-commit-stg-p-cadr-if-not-committed-p-car-help
    (implies (and (tail-p sub trace)
		  (INST-listp sub) 
		  (in-order-trace-p trace)
		  (not (committed-p (car sub))))
	     (not (commit-stg-p (INST-stg (cadr sub)))))
  :hints (("goal" :in-theory (enable committed-p)))))

(local
(defthm non-retire-stg-p-cadr-if-not-committed-p-car-help
    (implies (and (tail-p sub trace)
		  (INST-listp sub) 
		  (in-order-trace-p trace)
		  (not (committed-p (car sub))))
	     (not (retire-stg-p (INST-stg (cadr sub)))))
  :hints (("goal" :in-theory (enable committed-p)))))

; Instructions commit in order.  If car of trace is not committed,
; cadr of trace is not committed either.  A similar lemma follows.
(defthm non-commit-stg-p-cadr-if-not-committed-p-car
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (not (committed-p (car trace))))
	     (not (commit-stg-p (INST-stg (cadr trace)))))
  :hints (("goal" :in-theory (enable inv subtrace-p
				     in-order-dispatch-commit-p))))

(defthm non-retire-stg-p-cadr-if-not-committed-p-car
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (not (committed-p (car trace))))
	     (not (retire-stg-p (INST-stg (cadr trace)))))
  :hints (("goal" :in-theory (enable inv subtrace-p
				     in-order-dispatch-commit-p))))
)

; This lemma shows that the instruction at stage (DQ 0), if it exists,
; is the first non-dispatched instruction in program order.
; Presentation of this lemma is more technical. If instruction i is at
; (DQ 0), and car of trace is a non-dispatched instruction, then i
; cannot be a member of cdr of trace.
(defthm INST-at-DQ-0-is-first-non-dispatched-inst
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(DQ 0))
		  (not (dispatched-p (car trace)))
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace))
	     (not (member-equal i (cdr trace))))
  :hints (("goal" :in-theory (enable dispatched-p)
		  :use ((:instance DQ-stg-index-monotonic
				   (i (car trace))
				   (j i))
			(:instance INST-is-at-one-of-the-stages
				   (i (car trace)))))
	  (when-found (IFU-STG-P (INST-STG (CAR TRACE)))
		      (:cases ((consp (cdr trace))))))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (equal (INST-stg i) '(DQ 0))
			   (member-equal i (cdr trace))
			   (MAETT-p MT) (MA-state-p MA)
			   (subtrace-p trace MT)
			   (INST-listp trace))
		      (dispatched-p (car trace))))))
(in-theory
 (disable (:rewrite INST-at-DQ-0-is-first-non-dispatched-inst . 2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Theory  about  dispatched and committed instructions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deflabel begin-dispatch-commit-inst-stages)

(defthm IFU-not-dispatched-inst
    (implies (IFU-stg-p (INST-stg i)) (not (dispatched-p i))))

(defthm dq-not-dispatched-inst
    (implies (DQ-stg-p (INST-stg i)) (not (dispatched-p i))))

(defthm executed-dispatched-inst
    (implies (execute-stg-p (INST-stg i)) (dispatched-p i)))

(defthm completed-dispatched-inst
    (implies (complete-stg-p (INST-stg i)) (dispatched-p i)))

(defthm commit-dispatched-inst
    (implies (commit-stg-p (INST-stg i)) (dispatched-p i)))

(defthm retired-dispatched-inst
    (implies (retire-stg-p (INST-stg i)) (dispatched-p i)))

(defthm IFU-not-committed-inst
    (implies (IFU-stg-p (INST-stg i)) (not (committed-p i))))

(defthm dq-not-committed-inst
    (implies (DQ-stg-p (INST-stg i)) (not (committed-p i))))

(defthm executed-committed-inst
    (implies (execute-stg-p (INST-stg i)) (not (committed-p i))))

(defthm completed-committed-inst
    (implies (complete-stg-p (INST-stg i)) (not (committed-p i))))

(defthm commit-committed-inst
    (implies (commit-stg-p (INST-stg i)) (committed-p i)))

(defthm retired-committed-inst
    (implies (retire-stg-p (INST-stg i)) (committed-p i)))

(defthm not-committed-p-if-not-commit-retire
    (implies (and (not (commit-stg-p (INST-stg i)))
		  (not (retire-stg-p (INST-stg i))))
	     (not (committed-p i)))
  :hints (("goal" :in-theory (enable committed-p))))

(deflabel end-dispatch-commit-inst-stages)

(deftheory dispatch-commit-inst-stages
    (set-difference-theories
     (universal-theory 'end-dispatch-commit-inst-stages)
     (universal-theory 'begin-dispatch-commit-inst-stages)))

(defthm dispatched-p*
    (implies (INST-p i)
	     (equal (dispatched-p i)
		    (not (or (IFU-stg-p (INST-stg i))
			     (DQ-stg-p (INST-stg i))))))
  :hints (("goal" :in-theory (enable dispatched-p)
		  :use (:instance INST-is-at-one-of-the-stages))))

(defthm committed-p*
    (implies (INST-p i)
	     (equal (committed-p i)
		    (not (or (IFU-stg-p (INST-stg i))
			     (DQ-stg-p (INST-stg i))
			     (execute-stg-p (INST-stg i))
			     (complete-stg-p (INST-stg i))))))
  :hints (("goal" :in-theory (enable committed-p)
		  :use (:instance INST-is-at-one-of-the-stages))))

(in-theory (disable committed-p* dispatched-p*))

(encapsulate nil
;; These lemmas are locally defined because the derived rules are
;; fired too frequently and slows down the proof process.
(local
(defthm not-member-equal-if-no-dispatched-inst
    (implies (and (dispatched-p i)
		  (no-dispatched-inst-p trace))
	     (not (member-equal i trace)))))

(local
(defthm not-member-equal-if-no-commit-inst
    (implies (and (committed-p i)
		  (no-commit-inst-p trace))
	     (not (member-equal i trace)))))

(local
(defthm INST-in-order-commit-uncommit-help
    (implies (and (in-order-trace-p trace)
		  (INST-listp trace)
		  (INST-p i) (INST-p j)
		  (member-equal i trace)
 		  (member-equal j trace)
		  (committed-p i)
		  (not (committed-p j)))
	     (member-in-order i j trace))
  :hints (("goal" :in-theory (enable member-in-order*)
		  :induct t))))

(defthm INST-in-order-commit-uncommit
    (implies (and (inv MT MA)
 		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
 		  (INST-in j MT)
		  (committed-p i)
		  (not (committed-p j)))
	     (INST-in-order-p i j MT))
  :hints (("goal" :in-theory (enable INST-in-order-p INST-in
				     inv
				     IN-ORDER-DISPATCH-COMMIT-P))))

(local
(defthm INST-in-order-dispatched-undispatched-help
    (implies (and (in-order-trace-p trace)
		  (INST-listp trace)
		  (member-equal i trace)
 		  (member-equal j trace)
		  (dispatched-p i)
		  (not (dispatched-p j)))
	     (member-in-order i j trace))
  :hints (("goal" :in-theory (enable member-in-order*)
		  :induct t))))

(defthm INST-in-order-dispatched-undispatched
    (implies (and (inv MT MA)
 		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
 		  (INST-in j MT)
		  (dispatched-p i)
		  (not (dispatched-p j)))
	     (INST-in-order-p i j MT))
  :hints (("goal" :in-theory (enable INST-in-order-p INST-in
				     inv in-order-dispatch-commit-p))))
) ;encapsulate

(in-theory (disable dispatched-p committed-p))

(defthm not-member-equal-cdr-if-car-is-not-commit
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (consp trace)
		  (not (committed-p (car trace)))
		  (committed-p i)
		  (MAETT-p MT) (MA-state-p MA))
	     (not (member-equal i (cdr trace))))
  :hints (("goal" :use (:instance INST-IN-ORDER-COMMIT-UNCOMMIT
				  (i i) (j (car trace)))
		  :in-theory (disable INST-IN-ORDER-COMMIT-UNCOMMIT)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary 
	     (implies (and (inv MT MA)
			   (subtrace-p trace MT)
			   (consp trace)
			   (member-equal i (cdr trace))
			   (committed-p i)
			   (MAETT-p MT) (MA-state-p MA))
		      (committed-p (car trace))))))

(in-theory
 (disable (:rewrite not-member-equal-cdr-if-car-is-not-commit . 2)))

(defthm not-member-equal-cdr-if-car-is-not-dispatched
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (consp trace)
		  (not (dispatched-p (car trace)))
		  (dispatched-p i)
		  (MAETT-p MT) (MA-state-p MA))
	     (not (member-equal i (cdr trace))))
  :hints (("goal" :use (:instance inst-in-order-dispatched-undispatched
				  (i i) (j (car trace)))
		  :in-theory (disable inst-in-order-dispatched-undispatched)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (subtrace-p trace MT) (INST-listp trace)
			   (consp trace)
			   (member-equal i (cdr trace))
			   (dispatched-p i)
			   (MAETT-p MT) (MA-state-p MA))
		      (dispatched-p (car trace))))))

(in-theory
 (disable (:rewrite not-member-equal-cdr-if-car-is-not-dispatched . 2)))

(encapsulate nil
(local
 (defthm inst-of-tag-is-dispatched-help
     (implies (uniq-inst-of-tag-in-trace rix trace)
	      (dispatched-p (inst-of-tag-in-trace rix trace)))
   :hints (("goal" :in-theory (enable dispatched-p )))))

(defthm inst-of-tag-is-dispatched
    (implies (uniq-inst-of-tag rix MT)
	     (dispatched-p (inst-of-tag rix MT)))
  :hints (("goal" :in-theory (enable inst-of-tag uniq-inst-of-tag)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (uniq-inst-of-tag rix MT)
		      (not (IFU-stg-p (INST-stg (inst-of-tag rix MT))))))
   (:rewrite :corollary
	     (implies (uniq-inst-of-tag rix MT)
		      (not (DQ-stg-p (INST-stg (inst-of-tag rix MT))))))))
)

(encapsulate nil
(local
 (defthm inst-of-tag-is-not-committed-help
     (implies (uniq-inst-of-tag-in-trace rix trace)
	      (not (committed-p (inst-of-tag-in-trace rix trace))))
   :hints (("goal" :in-theory (enable committed-p )))))

(defthm inst-of-tag-is-not-committed
    (implies (uniq-inst-of-tag rix MT)
	     (not (committed-p (inst-of-tag rix MT))))
  :hints (("goal" :in-theory (enable inst-of-tag uniq-inst-of-tag)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (uniq-inst-of-tag rix MT)
		      (not (retire-stg-p (INST-stg (inst-of-tag rix MT))))))
   (:rewrite :corollary
	     (implies (uniq-inst-of-tag rix MT)
		      (not (commit-stg-p (INST-stg (inst-of-tag rix MT))))))))

)

;; End of the theory  about  dispatched and committed instructions

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Theories about init-MT
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(encapsulate nil
 (local (in-theory (enable init-MT)))

(defthm MT-init-ISA-init-MT
    (equal (MT-init-ISA (init-MT MA))
	   (proj MA)))

(defthm MT-new-ID-init-MT
    (equal (MT-new-ID (init-MT MA)) 0))

(defthm MT-dq-len-init-MT
    (equal (MT-dq-len (init-MT MA)) 0))

(defthm MT-rob-head-init-MT
    (equal (MT-rob-head (init-MT MA)) (ROB-head (MA-rob MA))))

(defthm MT-rob-tail-init-MT
    (equal (MT-rob-tail (init-MT MA)) (ROB-tail (MA-rob MA))))

(defthm MT-trace-init-MT
    (equal (MT-trace (init-MT MA)) nil))
)

(defthm MT-init-ISA-MT-step
    (equal (MT-init-ISA (MT-step MT MA sigs))
	   (MT-init-ISA MT))
  :hints (("Goal" :in-theory (enable MT-step))))

(defthm MT-init-ISA-MT-stepn
    (equal (MT-init-ISA (MT-stepn MT MA sigs-lst n))
	   (MT-init-ISA MT)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Lemmas about microarchitecture
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm not-fetch-inst-if-ex-intr
    (implies (b1p (ex-intr? MA sigs))
	     (equal (fetch-inst? MA sigs) 0))
  :hints (("Goal" :in-theory (enable fetch-inst? lift-b-ops flush-all?
				     b1p-bit-rewriter))))

(defthm flush-all-fetch-inst-exclusive
    (implies (b1p (fetch-inst? MA sigs))
	     (equal (flush-all? MA sigs) 0))
  :Hints (("goal" :in-theory (enable fetch-inst? lift-b-ops
				     equal-b1p-converter))))

(defthm not-fetch-inst-if-dq-full
    (implies (and (b1p (IFU-valid? (MA-IFU MA)))
		  (b1p (DQ-full? (MA-dq MA))))
	     (equal (fetch-inst? MA sigs) 0))
  :hints (("Goal" :in-theory (enable fetch-inst? lift-b-ops
				     equal-b1p-converter))))

; The proof of dispatch-to-IU-no-unit-exclusive If dispatch-to-IU is
; true, there should be an instruction at DE0.  This instruction
; should satisfy INST-inv.  We can prove that dispatch-to-IU? and
; dispatch-no-unit? are not 1 simultaneously in a reachable state.
(encapsulate nil
(local
(defthm dispatch-to-IU-no-unit-exclusive-help
    (implies (and (inv MT MA)
		  (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))
		  (b1p (logbit 0 (cntlv-exunit
				  (DE-cntlv (DQ-DE0 (MA-DQ MA)))))))
	     (not (b1p (logbit 4 (cntlv-exunit
				  (DE-cntlv (DQ-DE0 (MA-DQ MA))))))))
    :hints (("goal" :in-theory (enable consistent-cntlv-p
				       inv CONSISTENT-MA-P
				       CONSISTENT-DQ-CNTLV-P
				       lift-b-ops)))))

  
(defthm dispatch-to-IU-no-unit-exclusive
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-IU? MA)))
	     (not (b1p (dispatch-no-unit? MA))))
  :hints (("goal" :in-theory (e/d (dispatch-to-IU? dispatch-no-unit?
				     DQ-ready-to-IU? DQ-ready-no-unit?
				     dispatch-inst?
				     lift-b-ops) ))))
)

(encapsulate nil
(local
(defthm dispatch-to-MU-no-unit-exclusive-help
    (implies (and (inv MT MA)
		  (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))
		  (b1p (logbit 1 (cntlv-exunit (DE-cntlv
						(DQ-DE0 (MA-DQ MA)))))))
	     (not (b1p (logbit 4 (cntlv-exunit (DE-cntlv
						(DQ-DE0 (MA-DQ MA))))))))
    :hints (("goal" :in-theory (enable consistent-cntlv-p
				       inv CONSISTENT-MA-P
				       CONSISTENT-DQ-CNTLV-P
				       lift-b-ops)))))

  
(defthm dispatch-to-MU-no-unit-exclusive
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-MU? MA)))
	     (not (b1p (dispatch-no-unit? MA))))
  :hints (("goal" :in-theory (e/d (dispatch-to-MU? dispatch-no-unit?
				     DQ-ready-to-MU? DQ-ready-no-unit?
				     dispatch-inst?
				     lift-b-ops) ))))
)

(encapsulate nil
(local
  (defthm dispatch-to-LSU-no-unit-exclusive-help
      (implies (and (inv MT MA)
		    (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))
		    (b1p (logbit 2 (cntlv-exunit (DE-cntlv (DQ-DE0 (MA-DQ MA)))))))
	       (not (b1p (logbit 4 (cntlv-exunit (DE-cntlv (DQ-DE0 (MA-DQ MA))))))))

    :hints (("goal" :in-theory (enable consistent-cntlv-p
				       inv CONSISTENT-MA-P
				       CONSISTENT-DQ-CNTLV-P
				       lift-b-ops)))))

  
(defthm dispatch-to-LSU-no-unit-exclusive
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-LSU? MA)))
	     (not (b1p (dispatch-no-unit? MA))))
  :hints (("goal" :in-theory (e/d (dispatch-to-LSU? dispatch-no-unit?
				     DQ-ready-to-LSU? DQ-ready-no-unit?
				     dispatch-inst?
				     lift-b-ops) ))))
)

(encapsulate nil
(local
(defthm dispatch-to-BU-no-unit-exclusive-help
    (implies (and (inv MT MA)
		  (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))
		  (b1p (logbit 3 (cntlv-exunit (DE-cntlv
						(DQ-DE0 (MA-DQ MA)))))))
	     (not (b1p (logbit 4 (cntlv-exunit (DE-cntlv
						(DQ-DE0 (MA-DQ MA))))))))
    :hints (("goal" :in-theory (enable consistent-cntlv-p
				       inv CONSISTENT-MA-P
				       CONSISTENT-DQ-CNTLV-P
				       lift-b-ops)))))

  
(defthm dispatch-to-BU-no-unit-exclusive
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-BU? MA)))
	     (not (b1p (dispatch-no-unit? MA))))
  :hints (("goal" :in-theory (e/d (dispatch-to-BU? dispatch-no-unit?
				     DQ-ready-to-BU? DQ-ready-no-unit?
				     dispatch-inst?
				     lift-b-ops) ))))
)

(encapsulate nil
(local
(defthm dispatch-to-MU-IU-exclusive-help
    (implies (and (inv MT MA)
		  (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))
		  (b1p (logbit 1 (cntlv-exunit (DE-cntlv
						(DQ-DE0 (MA-DQ MA)))))))
	     (not (b1p (logbit 0 (cntlv-exunit (DE-cntlv
						(DQ-DE0 (MA-DQ MA))))))))
  
    :hints (("goal" :in-theory (enable consistent-cntlv-p
				       inv CONSISTENT-MA-P
				       CONSISTENT-DQ-CNTLV-P
				       lift-b-ops)))))

  
(defthm dispatch-to-MU-IU-exclusive
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-MU? MA)))
	     (not (b1p (dispatch-to-IU? MA))))
  :hints (("goal" :in-theory (e/d (dispatch-to-MU? dispatch-to-IU?
				     DQ-ready-to-MU? DQ-ready-to-IU?
				     dispatch-inst?
				     lift-b-ops) ))))
)

(encapsulate nil
(local
(defthm dispatch-to-LSU-IU-exclusive-help
    (implies (and (inv MT MA)
		  (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))
		  (b1p (logbit 2 (cntlv-exunit (DE-cntlv
						(DQ-DE0 (MA-DQ MA)))))))
	     (not (b1p (logbit 0 (cntlv-exunit (DE-cntlv
						(DQ-DE0 (MA-DQ MA))))))))
      :hints (("goal" :in-theory (enable consistent-cntlv-p
				       inv CONSISTENT-MA-P
				       CONSISTENT-DQ-CNTLV-P
				       lift-b-ops)))))

  
(defthm dispatch-to-LSU-IU-exclusive
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-LSU? MA)))
	     (not (b1p (dispatch-to-IU? MA))))
  :hints (("goal" :in-theory (e/d (dispatch-to-LSU? dispatch-to-IU?
				     DQ-ready-to-LSU? DQ-ready-to-IU?
				     dispatch-inst?
				     lift-b-ops) ))))
)

(encapsulate nil
(local
(defthm dispatch-to-BU-IU-exclusive-help
    (implies (and (inv MT MA)
		  (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))
		  (b1p (logbit 3 (cntlv-exunit (DE-cntlv
						(DQ-DE0 (MA-DQ MA)))))))
	     (not (b1p (logbit 0 (cntlv-exunit (DE-cntlv
						(DQ-DE0 (MA-DQ MA))))))))
    :hints (("goal" :in-theory (enable consistent-cntlv-p
				       inv CONSISTENT-MA-P
				       CONSISTENT-DQ-CNTLV-P
				       lift-b-ops)))))

  
(defthm dispatch-to-BU-IU-exclusive
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-BU? MA)))
	     (not (b1p (dispatch-to-IU? MA))))
  :hints (("goal" :in-theory (e/d (dispatch-to-BU? dispatch-to-IU?
				     DQ-ready-to-BU? DQ-ready-to-IU?
				     dispatch-inst?
				     lift-b-ops) ))))
)

(encapsulate nil
(local
(defthm dispatch-to-LSU-MU-exclusive-help
    (implies (and (inv MT MA)
		  (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))
		  (b1p (logbit 2 (cntlv-exunit (DE-cntlv
						(DQ-DE0 (MA-DQ MA)))))))
	     (not (b1p (logbit 1 (cntlv-exunit (DE-cntlv
						(DQ-DE0 (MA-DQ MA))))))))
    :hints (("goal" :in-theory (enable consistent-cntlv-p
				       inv CONSISTENT-MA-P
				       CONSISTENT-DQ-CNTLV-P
				       lift-b-ops)))))

  
(defthm dispatch-to-LSU-MU-exclusive
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-LSU? MA)))
	     (not (b1p (dispatch-to-MU? MA))))
  :hints (("goal" :in-theory (e/d (dispatch-to-LSU? dispatch-to-MU?
				     DQ-ready-to-LSU? DQ-ready-to-MU?
				     dispatch-inst?
				     lift-b-ops) ))))
)

(encapsulate nil
(local
(defthm dispatch-to-BU-MU-exclusive-help
    (implies (and (inv MT MA)
		  (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))
		  (b1p (logbit 3 (cntlv-exunit (DE-cntlv
						(DQ-DE0 (MA-DQ MA)))))))
	     (not (b1p (logbit 1 (cntlv-exunit (DE-cntlv
						(DQ-DE0 (MA-DQ MA))))))))
    :hints (("goal" :in-theory (enable consistent-cntlv-p
				       inv CONSISTENT-MA-P
				       CONSISTENT-DQ-CNTLV-P
				       lift-b-ops)))))

  
(defthm dispatch-to-BU-MU-exclusive
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-BU? MA)))
	     (not (b1p (dispatch-to-MU? MA))))
  :hints (("goal" :in-theory (e/d (dispatch-to-BU? dispatch-to-MU?
				     DQ-ready-to-BU? DQ-ready-to-MU?
				     dispatch-inst?
				     lift-b-ops) ))))
)

(encapsulate nil
(local
  (defthm dispatch-to-BU-LSU-exclusive-help
      (implies (and (inv MT MA)
		    (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))
		    (b1p (logbit 3 (cntlv-exunit (DE-cntlv (DQ-DE0 (MA-DQ MA)))))))
	       (not (b1p (logbit 2 (cntlv-exunit (DE-cntlv (DQ-DE0 (MA-DQ MA))))))))

    :hints (("goal" :in-theory (enable consistent-cntlv-p
				       inv CONSISTENT-MA-P
				       CONSISTENT-DQ-CNTLV-P
				       lift-b-ops)))))

  
(defthm dispatch-to-BU-LSU-exclusive
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-to-BU? MA)))
	     (not (b1p (dispatch-to-LSU? MA))))
  :hints (("goal" :in-theory (e/d (dispatch-to-BU? dispatch-to-LSU?
				     DQ-ready-to-BU? DQ-ready-to-LSU?
				     dispatch-inst?
				     lift-b-ops) ))))
)

(defthm DE-valid-consistent
    (and (implies (and (inv MT MA)
		       (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))))
		  (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))))
	 (implies (and (inv MT MA)
		       (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))))
		  (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))))
	 (implies (and (inv MT MA)
		       (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))))
		  (not (b1p (DE-valid? (DQ-DE3 (MA-DQ MA))))))
	 (implies (and (inv MT MA)
		       (b1p (DE-valid? (DQ-DE1 (MA-DQ MA)))))
		  (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
	 (implies (and (inv MT MA)
		       (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))))
		  (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))))
	 (implies (and (inv MT MA)
		       (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))))
		  (not (b1p (DE-valid? (DQ-DE3 (MA-DQ MA))))))
	 (implies (and (inv MT MA)
		       (b1p (DE-valid? (DQ-DE2 (MA-DQ MA)))))
		  (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
	 (implies (and (inv MT MA)
		       (b1p (DE-valid? (DQ-DE2 (MA-DQ MA)))))
		  (b1p (DE-valid? (DQ-DE1 (MA-DQ MA)))))
	 (implies (and (inv MT MA)
		       (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))))
		  (not (b1p (DE-valid? (DQ-DE3 (MA-DQ MA))))))
	 (implies (and (inv MT MA)
		       (b1p (DE-valid? (DQ-DE3 (MA-DQ MA)))))
		  (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
	 (implies (and (inv MT MA)
		       (b1p (DE-valid? (DQ-DE3 (MA-DQ MA)))))
		  (b1p (DE-valid? (DQ-DE1 (MA-DQ MA)))))
	 (implies (and (inv MT MA)
		       (b1p (DE-valid? (DQ-DE3 (MA-DQ MA)))))
		  (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))))
  :hints (("goal" :in-theory (enable inv misc-inv
				     correct-entries-in-DQ-p))))

(defthm LSU-wbuf0-valid-if-LSU-wbuf1-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
	     (equal (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))) 1))
  :hints (("goal" :in-theory (enable inv consistent-MA-p
				     consistent-LSU-p
				     equal-b1p-converter))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Lemmas about stages after step-INST
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deflabel begin-step-INST-opener)
(in-theory (enable step-INST))
(defthm step-INST-IFU-INST
    (implies (IFU-stg-p (INST-stg i))
	     (equal (step-INST i MT MA sigs)
		    (step-INST-IFU I MT MA sigs))))

(defthm step-INST-DQ-INST
    (implies (DQ-stg-p (INST-stg i))
	     (equal (step-INST i MT MA sigs)
		    (step-INST-DQ I MT MA sigs))))

(defthm step-INST-execute-INST
    (implies (execute-stg-p (INST-stg i))
	     (equal (step-INST i MT MA sigs)
		    (step-INST-execute I MA sigs))))

(defthm step-INST-complete-INST
    (implies (complete-stg-p (INST-stg i))
	     (equal (step-INST i MT MA sigs)
		    (step-INST-complete I MA sigs))))

(defthm step-INST-commit-INST
    (implies (commit-stg-p (INST-stg i))
	     (equal (step-INST i MT MA sigs)
		    (step-INST-commit I MA sigs))))

(in-theory (disable step-INST))
(deflabel end-step-INST-opener)
(deftheory step-INST-opener
    (set-difference-theories (universal-theory 'end-step-INST-opener)
			     (universal-theory 'begin-step-INST-opener)))
(in-theory (disable step-INST-opener))

(defthm INST-stg-exintr-INST
    (equal (INST-stg (exintr-INST MT ISA smc)) '(retire))
  :hints (("goal" :in-theory (enable exintr-INST))))

(defthm INST-stg-fetched-inst
    (equal (INST-stg (fetched-inst MT ISA spc smc)) '(IFU))
  :hints (("goal" :in-theory (enable fetched-inst))))

(defthm not-IFU-stg-step-INST-if-not-IFU
    (implies (not (IFU-stg-p (INST-stg i)))
	     (not (IFU-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :in-theory (enable MT-def))))

(defthm not-IFU-stg-step-INST-if-not-IFU-2
    (implies (not (IFU-stg-p (INST-stg i)))
	     (not (equal (INST-stg (step-INST i MT MA sigs)) '(IFU))))
  :hints (("goal" :in-theory (enable IFU-stg-p)
		  :use (:instance not-IFU-stg-step-INST-if-not-IFU))))

(defthm not-DQ-stg-step-INST-if-not-IFU
    (implies (and (not (IFU-stg-p (INST-stg i)))
		  (not (DQ-stg-p (INST-stg i))))
	     (not (DQ-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :in-theory (enable MT-def))))

(defthm not-DQ-stg-step-INST-if-not-IFU-2
    (implies (and (INST-p i)
		  (not (IFU-stg-p (INST-stg i)))
		  (not (DQ-stg-p (INST-stg i))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 (list 'DQ idx))))
  :hints (("goal" :in-theory (enable MT-def MA-stg-def)
		  :use (inst-is-at-one-of-the-stages))))

(defthm not-execute-stg-step-INST-if-not-DQ
    (implies (and (not (DQ-stg-p (INST-stg i)))
		  (not (execute-stg-p (INST-stg i))))
	     (not (execute-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :in-theory (enable MT-def))))

(defthm not-IU-stg-step-INST-if-not-DQ-2
    (implies (and (INST-p i)
		  (not (DQ-stg-p (INST-stg i)))
		  (not (execute-stg-p (INST-stg i))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 (cons 'IU trailer))))
  :hints (("goal" :in-theory (enable MT-def MA-stg-def)
		  :use (inst-is-at-one-of-the-stages))))

(defthm not-BU-stg-step-INST-if-not-DQ-2
    (implies (and (INST-p i)
		  (not (DQ-stg-p (INST-stg i)))
		  (not (execute-stg-p (INST-stg i))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 (cons 'BU trailer))))
  :hints (("goal" :in-theory (enable MT-def MA-stg-def)
		  :use (inst-is-at-one-of-the-stages))))

(defthm not-MU-stg-step-INST-if-not-DQ-2
    (implies (and (INST-p i)
		  (not (DQ-stg-p (INST-stg i)))
		  (not (execute-stg-p (INST-stg i))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 (cons 'MU trailer))))
  :hints (("goal" :in-theory (enable MT-def MA-stg-def)
		  :use (inst-is-at-one-of-the-stages))))

(defthm not-LSU-stg-step-INST-if-not-DQ-2
    (implies (and (INST-p i)
		  (not (DQ-stg-p (INST-stg i)))
		  (not (execute-stg-p (INST-stg i))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 (cons 'LSU trailer))))
  :hints (("goal" :in-theory (enable MT-def MA-stg-def)
		  :use (inst-is-at-one-of-the-stages))))

(defthm not-complete-stg-step-INST-if-not-execute-or-DQ
    (implies (and (not (DQ-stg-p (INST-stg i)))
		  (not (execute-stg-p (INST-stg i)))
		  (not (complete-stg-p (INST-stg i))))
	     (not (complete-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :in-theory (enable MT-def))))

(defthm not-complete-stg-step-INST-if-not-execute-or-DQ-2
    (implies (and (INST-p i)
		  (not (DQ-stg-p (INST-stg i)))
		  (not (execute-stg-p (INST-stg i)))
		  (not (complete-stg-p (INST-stg i))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 (cons 'complete trailer))))
  :hints (("goal" :in-theory (enable MT-def MA-stg-def)
		  :use (inst-is-at-one-of-the-stages))))

(defthm not-commit-stg-step-INST-if-not-commit-or-complete
    (implies (and (not (complete-stg-p (INST-stg i)))
		  (not (commit-stg-p (INST-stg i))))
	     (not (commit-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :in-theory (enable MT-def))))

(defthm not-commit-stg-step-INST-if-not-commit-or-complete-2
    (implies (and (INST-p i)
		  (not (complete-stg-p (INST-stg i)))
		  (not (commit-stg-p (INST-stg i))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 (cons 'commit trailer))))
  :hints (("goal" :in-theory (enable MT-def MA-stg-def)
		  :use (inst-is-at-one-of-the-stages))))

(defthm not-retire-stg-step-INST-if-not-commit-or-complete
    (implies (and (not (complete-stg-p (INST-stg i)))
		  (not (commit-stg-p (INST-stg i)))
		  (not (retire-stg-p (INST-stg i))))
	     (not (retire-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :in-theory (enable MT-def))))

(defthm not-retire-stg-step-INST-if-not-commit-or-complete-2
    (implies (and (INST-p i)
		  (not (complete-stg-p (INST-stg i)))
		  (not (commit-stg-p (INST-stg i)))
		  (not (retire-stg-p (INST-stg i))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 '(retire))))
  :hints (("goal" :in-theory (enable MT-def MA-stg-def)
		  :use (inst-is-at-one-of-the-stages))))

(defthm IFU-or-DQ-stg-step-INST-if-IFU
    (implies (IFU-stg-p (INST-stg i))
	     (or (IFU-stg-p (INST-stg (step-INST i MT MA sigs)))
		 (DQ-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :in-theory (enable MT-def DQ-stg-p)))
  :rule-classes
  ((:rewrite :corollary
     (implies (and (IFU-stg-p (INST-stg i))
		   (not (IFU-stg-p (INST-stg (step-INST i MT MA sigs)))))
	      (DQ-stg-p (INST-stg (step-INST i MT MA sigs)))))))

(defthm execute-or-complete-stg-step-INST-if-DQ
    (implies (DQ-stg-p (INST-stg i))
	     (or (DQ-stg-p (INST-stg (step-INST i MT MA sigs)))
		 (execute-stg-p (INST-stg (step-INST i MT MA sigs)))
		 (complete-stg-p (INST-stg (step-INST i MT MA sigs)))))
    :hints (("goal" :in-theory (enable MT-def DQ-stg-p)))
    :rule-classes
    ((:rewrite :corollary
       (implies (and (DQ-stg-p (INST-stg i))
		     (not (DQ-stg-p (INST-stg (step-INST i MT MA sigs))))
		     (not (execute-stg-p (INST-stg (step-INST i MT MA sigs)))))
		(complete-stg-p (INST-stg (step-INST i MT MA sigs)))))))

(defthm execute-or-complete-stg-step-INST-if-execute
    (implies (execute-stg-p (INST-stg i))
	     (or (execute-stg-p (INST-stg (step-INST i MT MA sigs)))
		 (complete-stg-p (INST-stg (step-INST i MT MA sigs)))))
    :hints (("goal" :in-theory (enable MT-def)))
    :rule-classes
    ((:rewrite :corollary
       (implies (and (execute-stg-p (INST-stg i))
		     (not (execute-stg-p (INST-stg (step-INST i MT MA sigs)))))
		(complete-stg-p (INST-stg (step-INST i MT MA sigs)))))))

(defthm commit-or-retire-stg-step-INST-if-complete
    (implies (complete-stg-p (INST-stg i))
	     (or (complete-stg-p (INST-stg (step-INST i MT MA sigs)))
		 (commit-stg-p (INST-stg (step-INST i MT MA sigs)))
		 (retire-stg-p (INST-stg (step-INST i MT MA sigs)))))
    :hints (("goal" :in-theory (enable MT-def)))
    :rule-classes
    ((:rewrite :corollary
       (implies (and (complete-stg-p (INST-stg i))
		     (not (complete-stg-p (INST-stg (step-INST i MT MA sigs))))
		     (not (commit-stg-p (INST-stg (step-INST i MT MA sigs)))))
		(retire-stg-p (INST-stg (step-INST i MT MA sigs)))))))

(defthm retire-or-commit-stg-step-INST-if-commit
    (implies (commit-stg-p (INST-stg i))
	     (or (commit-stg-p (INST-stg (step-INST i MT MA sigs)))
		 (retire-stg-p (INST-stg (step-INST i MT MA sigs)))))
    :hints (("goal" :in-theory (enable MT-def)))
    :rule-classes
    ((:rewrite :corollary
       (implies (and (commit-stg-p (INST-stg i))
		     (not (commit-stg-p (INST-stg (step-INST i MT MA sigs)))))
		(retire-stg-p (INST-stg (step-INST i MT MA sigs)))))))

(defthm retire-stg-step-INST-if-retire
    (implies (retire-stg-p (INST-stg i))
	     (retire-stg-p (INST-stg (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (enable MT-def))))

(defthm RS-stg-p-step-INST-if-DQ-stg-p
    (implies (and (DQ-stg-p (INST-stg i))
		  (execute-stg-p (INST-stg (step-INST i MT MA sigs))))
	     (RS-stg-p (INST-stg (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (enable lift-b-ops STEP-INST-DQ
				     step-INST-dq-inst
				     dispatch-inst))))

(defthm RS-stg-p-step-INST-if-DQ-stg-p-col1
    (implies (and (DQ-stg-p (INST-stg i))
		  (not (RS-stg-p (cons 'MU trailer))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 (cons 'MU trailer))))
  :hints (("goal" :in-theory (enable lift-b-ops STEP-INST-DQ
				     step-INST-dq-inst
				     dq-stg-p
				     dispatch-inst))))

(defthm RS-stg-p-step-INST-if-DQ-stg-p-col2
    (implies (and (DQ-stg-p (INST-stg i))
		  (not (RS-stg-p (cons 'LSU trailer))))
	     (not (equal (INST-stg (step-INST i MT MA sigs))
			 (cons 'LSU trailer))))
  :hints (("goal" :in-theory (enable lift-b-ops STEP-INST-DQ
				     step-INST-dq-inst
				     dq-stg-p
				     dispatch-inst))))

(defthm WBUF-stg-p-step-DQ-INST
    (implies (DQ-stg-p (INST-stg i))
	     (not (wbuf-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :in-theory (enable step-inst-dq-inst
				     dq-stg-p wbuf-stg-p
				     step-inst-low-level-functions)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (and (wbuf-stg-p stg)
			   (DQ-stg-p (INST-stg i)))
		      (not (equal (INST-stg (step-INST i MT MA sigs)) stg)))
	     :hints (("goal" :in-theory (enable wbuf-stg-p))))))

;; More specific lemmas about stages and step-INST
(defthm INST-stg-step-IFU-inst-if-DQ-full
    (implies (IFU-stg-p (INST-stg i))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (b-if (DQ-full? (MA-DQ MA))
			  '(IFU)
			  (NEW-dq-stage MT MA))))
  :hints (("goal" :in-theory (enable MT-def IFU-stg-p))))

(defthm INST-stg-step-DQ-inst-if-not-dispatch
    (implies (and (not (b1p (dispatch-inst? MA)))
		  (DQ-stg-p (inst-stg i)))
	     (equal (inst-stg (step-INST i MT MA sigs))
		    (inst-stg i)))
  :hints (("Goal" :in-theory (enable MT-def))))

(defthm INST-stg-step-DQ-inst-if-dispatch-1
    (implies (and (b1p (dispatch-inst? MA))
		  (dq-stg-p (inst-stg i))
		  (not (zp (DQ-stg-idx (INST-stg i)))))
	     (equal (inst-stg (step-INST i MT MA sigs))
		    (list 'dq (nfix (1- (DQ-stg-idx (inst-stg i)))))))
  :hints (("goal" :in-theory (enable MT-def))))

(defthm INST-stg-step-DQ-inst-if-dispatch-2
    (implies (and (b1p (dispatch-inst? MA))
		  (equal (inst-stg i) '(DQ 0)))
	     (not (equal (inst-stg (step-INST i MT MA sigs)) (list 'DQ idx))))
  :hints (("Goal" :in-theory (enable MT-def))))

(defthm complete-stg-p-step-inst-if-LSU-lch
    (implies (and (equal (INST-stg i) '(LSU lch))
		  (not (equal (INST-stg (step-INST i MT MA sigs))
			      '(LSU lch))))
	     (complete-stg-p (INST-stg (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (enable MT-def))))

(defthm complete-stg-p-step-inst-if-LSU-wbuf0-lch
    (implies (and (equal (INST-stg i) '(LSU wbuf0 lch))
		  (not (equal (INST-stg (step-INST i MT MA sigs))
			      '(LSU wbuf0 lch))))
	     (complete-stg-p (INST-stg (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (enable MT-def))))

(defthm complete-stg-p-step-inst-if-LSU-wbuf1-lch
    (implies (and (equal (INST-stg i) '(LSU wbuf1 lch))
		  (not (equal (INST-stg (step-INST i MT MA sigs))
			      '(LSU wbuf0 lch)))
		  (not (equal (INST-stg (step-INST i MT MA sigs))
			      '(LSU wbuf1 lch))))
	     (complete-stg-p (INST-stg (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (enable MT-def))))

(defthm LSU-stages-direct-reachable-to-complete
    (implies (and (LSU-stg-p (INST-stg i))
		  (not (or (equal (INST-stg i) '(LSU lch))
			   (equal (INST-stg i) '(LSU wbuf0 lch))
			   (equal (INST-stg i) '(LSU wbuf1 lch)))))
	     (not (complete-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :in-theory (enable LSU-stg-p step-INST
				     step-INST-execute
				     step-INST-low-level-functions))))

; An instruction dispatch is never undone.
(defthm dispatch-inst-p-step-inst-if-dispatch
    (implies (dispatched-p i)
	     (dispatched-p (step-INST i MT MA sigs)))
  :hints (("goal" :in-theory (enable step-inst
				     step-INST-low-level-functions))))

(defthm dispatched-inst-step-inst-if-not-dispatch-inst
    (implies (and (INST-p i) (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (not (b1p (dispatch-inst? MA)))
		  (not (dispatched-p i)))
	     (not (dispatched-p (step-INST i MT MA sigs))))
  :hints (("Goal" :in-theory (enable dispatched-p*))))

(defthm dispatched-p-step-INST-if-dispatch-inst
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (b1p (dispatch-inst? MA))
		  (equal (INST-stg i) '(DQ 0))
		  (MAETT-p MT) (MA-state-p MA)) 
	     (dispatched-p (step-INST i MT MA sigs)))
  :hints (("Goal" :in-theory (enable dispatched-p
				     step-inst-dq-inst
				     step-inst-low-level-functions ))))

; An instruction is once committed, it will be in the future forever.
(defthm committed-p-step-inst-if-commit
    (implies (committed-p i)
	     (committed-p (step-INST i MT MA sigs)))
  :hints (("goal" :in-theory (enable step-inst
				     step-INST-low-level-functions))))

(deflabel begin-inst-stg-step-inst)

; Stage inference rules for instructions at (DQ 0)
; Following Lemmas show to which stage an instruction is dispatched.
(defthm INST-stg-step-INST-if-dispatch-no-unit
    (implies (and (equal (INST-stg i) '(DQ 0))
		  (b1p (dispatch-no-unit? MA)))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    '(complete)))
  :hints (("goal" :in-theory (enable step-INST step-INST-dq
				     dispatch-inst? lift-b-ops
				     dispatch-inst))))

(defthm INST-stg-step-INST-if-dispatch-IU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(DQ 0))
		  (b1p (dispatch-to-IU? MA)))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (b-if (select-IU-RS0? (MA-IU MA))
			  '(IU RS0)
			  '(IU RS1))))
  :hints (("goal" :in-theory (enable step-INST step-INST-dq
				     dispatch-inst? lift-b-ops
				     dispatch-inst))))

(defthm INST-stg-step-INST-if-dispatch-MU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(DQ 0))
		  (b1p (dispatch-to-MU? MA)))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (b-if (select-MU-RS0? (MA-MU MA))
			  '(MU RS0)
			  '(MU RS1))))
  :hints (("goal" :in-theory (enable step-INST step-INST-dq
				     dispatch-inst? lift-b-ops
				     dispatch-inst))))

(defthm INST-stg-step-INST-if-dispatch-BU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(DQ 0))
		  (b1p (dispatch-to-BU? MA)))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (b-if (select-BU-RS0? (MA-BU MA))
			  '(BU RS0)
			  '(BU RS1))))
  :hints (("goal" :in-theory (enable step-INST step-INST-dq
				     dispatch-inst? lift-b-ops
				     dispatch-inst))))

(defthm INST-stg-step-INST-if-dispatch-LSU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(DQ 0))
		  (b1p (dispatch-to-LSU? MA)))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (b-if (select-LSU-RS0? (MA-LSU MA))
			  '(LSU RS0)
			  '(LSU RS1))))
  :hints (("goal" :in-theory (enable step-INST step-INST-dq
				     dispatch-inst? lift-b-ops
				     dispatch-inst))))

(defthm INST-stg-step-INST-IU-RS0
    (implies (equal (INST-stg i) '(IU RS0))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (if (b1p (issue-IU-RS0? (MA-IU MA) MA))
			'(complete) '(IU RS0))))
  :hints (("goal" :in-theory (enable step-INST-opener  step-INST-execute
				     step-INST-IU))))

(defthm INST-stg-step-INST-IU-RS1
    (implies (equal (INST-stg i) '(IU RS1))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (if (b1p (issue-IU-RS1? (MA-IU MA) MA))
			'(complete) '(IU RS1))))
  :hints (("goal" :in-theory (enable step-INST-opener  step-INST-execute
				     step-INST-IU))))

(defthm INST-stg-step-INST-MU-RS0
    (implies (equal (INST-stg i) '(MU RS0))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (if (b1p (issue-MU-RS0? (MA-MU MA) MA))
			'(MU lch1) '(MU RS0))))
  :hints (("goal" :in-theory (enable step-INST-opener  step-INST-execute
				     step-INST-MU))))

(defthm INST-stg-step-INST-MU-RS1
    (implies (equal (INST-stg i) '(MU RS1))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (if (b1p (issue-MU-RS1? (MA-MU MA) MA))
			'(MU lch1) '(MU RS1))))
  :hints (("goal" :in-theory (enable step-INST-opener  step-INST-execute
				     step-INST-MU))))

(defthm INST-stg-step-INST-MU-lch1
    (implies (equal (INST-stg i) '(MU lch1))
     (equal (INST-stg (step-INST i MT MA sigs))
	    (if (or (b1p (CDB-FOR-MU? MA))
		    (b1p (B-NOT (MU-LATCH2-VALID? (MU-LCH2 (MA-MU MA))))))
		'(MU lch2) '(MU lch1))))
  :hints (("goal" :in-theory (enable step-INST-opener  step-INST-execute
				     lift-b-ops step-INST-MU))))

(defthm INST-stg-step-INST-MU-lch2
   (implies (equal (INST-stg i) '(MU lch2))
     (equal (INST-stg (step-INST i MT MA sigs))
	    (if (b1p (CDB-FOR-MU? MA))
		'(complete) '(MU lch2))))
  :hints (("goal" :in-theory (enable step-INST-opener  step-INST-execute
				     lift-b-ops step-INST-MU))))

(defthm INST-stg-step-INST-BU-RS0
    (implies (equal (INST-stg i) '(BU RS0))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (if (b1p (issue-BU-RS0? (MA-BU MA) MA))
			'(complete) '(BU RS0))))
  :hints (("goal" :in-theory (enable step-INST-opener  step-INST-execute
				     step-INST-BU))))

(defthm INST-stg-step-INST-BU-RS1
    (implies (equal (INST-stg i) '(BU RS1))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (if (b1p (issue-BU-RS1? (MA-BU MA) MA))
			'(complete) '(BU RS1))))
  :hints (("goal" :in-theory (enable step-INST-opener  step-INST-execute
				     step-INST-BU))))

(defthm INST-stg-step-INST-LSU-RS0
    (implies (equal (INST-stg i) '(LSU RS0))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (if (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs))
			(if (b1p (LSU-RS-ld-st? (LSU-RS0 (MA-LSU MA))))
			    (if (b1p (INST-select-wbuf0? MA sigs))
				'(LSU wbuf0)
				'(LSU wbuf1))
			    '(LSU rbuf))
			'(LSU RS0))))
  :hints (("goal" :in-theory (enable step-INST-opener  step-INST-execute
				     step-INST-LSU
				     step-INST-LSU-RS0))))

(defthm INST-stg-step-INST-LSU-RS1
    (implies (equal (INST-stg i) '(LSU RS1))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (if (b1p (issue-LSU-RS1? (MA-LSU MA) MA sigs))
			(if (b1p (LSU-RS-ld-st? (LSU-RS1 (MA-LSU MA))))
			    (if (b1p (INST-select-wbuf0? MA sigs))
				'(LSU wbuf0)
				'(LSU wbuf1))
			    '(LSU rbuf))
			'(LSU RS1))))
  :hints (("goal" :in-theory (enable step-INST-opener  step-INST-execute
				     step-INST-LSU step-INST-LSU-RS1))))

(defthm INST-stg-step-INST-LSU-wbuf1
    (implies (equal (INST-stg i) '(LSU wbuf1))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (if (b1p (check-wbuf1? (MA-LSU MA)))
			'(LSU wbuf1 lch)
			(if (b1p (release-wbuf0? (MA-LSU MA) sigs))
			    '(LSU wbuf0)
			    '(LSU wbuf1)))))
  :hints (("goal" :in-theory (enable step-INST-opener  step-INST-execute
				     step-INST-LSU step-INST-LSU-wbuf1))))

(defthm INST-stg-step-INST-LSU-wbuf0
    (implies (equal (INST-stg i) '(LSU wbuf0))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (if (b1p (check-wbuf0? (MA-LSU MA)))
			'(LSU wbuf0 lch)
			'(LSU wbuf0))))
  :hints (("goal" :in-theory (enable step-INST-opener  step-INST-execute
				     step-INST-LSU step-INST-LSU-wbuf0))))

(defthm INST-stg-step-INST-LSU-rbuf
    (implies (equal (INST-stg i) '(LSU rbuf))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (if (b1p (release-rbuf? (MA-LSU MA) MA sigs))
			'(LSU  lch)
			'(LSU rbuf))))
  :hints (("goal" :in-theory (enable step-INST-opener  step-INST-execute
				     lift-b-ops
				     step-INST-LSU step-INST-LSU-rbuf))))

(defthm INST-stg-step-INST-LSU-wbuf0-lch
    (implies (equal (INST-stg i) '(LSU wbuf0 lch))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    '(complete wbuf0)))
  :hints (("goal" :in-theory (enable step-INST-opener  step-INST-execute
				     step-INST-LSU step-INST-LSU-wbuf0-lch
				     lift-b-ops))))

(defthm INST-stg-step-INST-LSU-wbuf1-lch
    (implies (equal (INST-stg i) '(LSU wbuf1 lch))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (if (b1p (release-wbuf0? (MA-LSU MA) sigs))
			'(complete wbuf0)
			'(complete wbuf1))))
  :hints (("goal" :in-theory (enable step-INST-opener  step-INST-execute
				     step-INST-LSU step-INST-LSU-wbuf1-lch
				     lift-b-ops))))

(defthm INST-stg-step-INST-complete-normal
    (implies (equal (INST-stg i) '(complete))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (if (b1p (INST-commit? i MA)) '(retire) '(complete))))
  :hints (("goal" :in-theory (enable step-INST-opener  step-INST-complete
				     lift-b-ops))))

(defthm INST-stg-step-INST-complete-wbuf0
    (implies (equal (INST-stg i) '(complete wbuf0))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (if (b1p (b-and (INST-commit? i MA) (enter-excpt? MA)))
			'(retire)
			(if (b1p (INST-commit? i MA))
			    '(commit wbuf0)
			    '(complete wbuf0)))))
  :hints (("goal" :in-theory (enable step-INST-opener  step-INST-complete
				     lift-b-ops))))

(defthm INST-stg-step-INST-complete-wbuf1
    (implies (equal (INST-stg i) '(complete wbuf1))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (if (b1p (b-and (INST-commit? i MA) (enter-excpt? MA)))
			'(retire)
			(if (b1p (b-and (INST-commit? i MA)
					(release-wbuf0? (MA-LSU MA) sigs)))
			    '(commit wbuf0)
			    (if (b1p (INST-commit? i MA))
				'(commit wbuf1)
				(if (b1p (release-wbuf0? (MA-LSU MA) sigs))
				    '(complete wbuf0)
				    '(complete wbuf1)))))))
  :hints (("goal" :in-theory (enable step-INST-opener  step-INST-complete
				     lift-b-ops))))

(defthm INST-stg-step-INST-commit-wbuf0
    (implies (equal (INST-stg i) '(commit wbuf0))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (if (b1p (release-wbuf0? (MA-LSU MA) sigs))
			'(retire)
			'(commit wbuf0))))
  :hints (("goal" :in-theory (enable step-INST-opener  step-INST-commit
				     step-INST-LSU
				     lift-b-ops))))

(defthm INST-stg-step-INST-commit-wbuf1
    (implies (equal (INST-stg i) '(commit wbuf1))
	     (equal (INST-stg (step-INST i MT MA sigs))
		    (if (b1p (release-wbuf0? (MA-LSU MA) sigs))
			'(commit wbuf0)
			'(commit wbuf1))))
  :hints (("goal" :in-theory (enable step-INST-opener  step-INST-commit
				     step-INST-LSU
				     lift-b-ops))))

(deflabel end-inst-stg-step-inst)
(deftheory inst-stg-step-inst
    (set-difference-theories (universal-theory 'end-inst-stg-step-inst)
			     (universal-theory 'begin-inst-stg-step-inst)))
			     
(in-theory (disable inst-stg-step-inst))

;;;;; Lemmas about Reachable Stages
; instruction can i is in stage (IU RS0) only if its previous stage is
; (DQ 0) or (IU RS0) itself.
;
; Similar lemmas follow.
(defthm stages-reachable-to-IU-RS0
    (implies (equal (INST-stg (step-INST i MT MA sigs)) '(IU RS0))
	     (or (equal (INST-stg i) '(DQ 0))
		 (equal (INST-stg i) '(IU RS0))))
  :hints (("goal" :in-theory (enable step-INST MT-def-non-rec-functions
				     DQ-stg-p)))
  :rule-classes nil)

(defthm stages-reachable-to-IU-RS1
    (implies (equal (INST-stg (step-INST i MT MA sigs)) '(IU RS1))
	     (or (equal (INST-stg i) '(DQ 0))
		 (equal (INST-stg i) '(IU RS1))))
  :hints (("goal" :in-theory (enable step-INST MT-def-non-rec-functions
				     DQ-stg-p)))
  :rule-classes nil)

(defthm stages-reachable-to-MU-RS0
    (implies (equal (INST-stg (step-INST i MT MA sigs)) '(MU RS0))
	     (or (equal (INST-stg i) '(DQ 0))
		 (equal (INST-stg i) '(MU RS0))))
  :hints (("goal" :in-theory (enable step-INST MT-def-non-rec-functions
				     DQ-stg-p)))
  :rule-classes nil)

(defthm stages-reachable-to-MU-RS1
    (implies (equal (INST-stg (step-INST i MT MA sigs)) '(MU RS1))
	     (or (equal (INST-stg i) '(DQ 0))
		 (equal (INST-stg i) '(MU RS1))))
  :hints (("goal" :in-theory (enable step-INST MT-def-non-rec-functions
				     DQ-stg-p)))
  :rule-classes nil)

(defthm stages-reachable-to-MU-lch1
    (implies (equal (INST-stg (step-INST i MT MA sigs)) '(MU lch1))
	     (or (equal (INST-stg i) '(MU RS0))
		 (equal (INST-stg i) '(MU RS1))
		 (equal (INST-stg i) '(MU lch1))))
  :hints (("goal" :in-theory (enable step-INST MT-def-non-rec-functions
				     MU-stg-p)))
  :rule-classes nil)

(defthm stages-reachable-to-MU-lch2
    (implies (equal (INST-stg (step-INST i MT MA sigs)) '(MU lch2))
	     (or (equal (INST-stg i) '(MU lch1))
		 (equal (INST-stg i) '(MU lch2))))
  :hints (("goal" :in-theory (enable step-INST MT-def-non-rec-functions
				     MU-stg-p)))
  :rule-classes nil)

(defthm stages-reachable-to-BU-RS0
    (implies (equal (INST-stg (step-INST i MT MA sigs)) '(BU RS0))
	     (or (equal (INST-stg i) '(DQ 0))
		 (equal (INST-stg i) '(BU RS0))))
  :hints (("goal" :in-theory (enable step-INST MT-def-non-rec-functions
				     DQ-stg-p BU-stg-p)))
  :rule-classes nil)

(defthm stages-reachable-to-BU-RS1
    (implies (equal (INST-stg (step-INST i MT MA sigs)) '(BU RS1))
	     (or (equal (INST-stg i) '(DQ 0))
		 (equal (INST-stg i) '(BU RS1))))
  :hints (("goal" :in-theory (enable step-INST MT-def-non-rec-functions
				     DQ-stg-p BU-stg-p)))
  :rule-classes nil)

(defthm stages-reachable-to-lsu-RS0
    (implies (equal (INST-stg (step-INST i MT MA sigs)) '(LSU RS0))
	     (or (equal (INST-stg i) '(DQ 0))
		 (equal (INST-stg i) '(LSU RS0))))
  :hints (("goal" :in-theory (enable step-INST MT-def-non-rec-functions
				     DQ-stg-p LSU-stg-p)))
  :rule-classes nil)

(defthm stages-reachable-to-lsu-RS1
    (implies (equal (INST-stg (step-INST i MT MA sigs)) '(LSU RS1))
	     (or (equal (INST-stg i) '(DQ 0))
		 (equal (INST-stg i) '(LSU RS1))))
  :hints (("goal" :in-theory (enable step-INST MT-def-non-rec-functions
				     DQ-stg-p LSU-stg-p)))
  :rule-classes nil)

(defthm stages-reachable-to-lsu-wbuf1
    (implies (equal (INST-stg (step-INST i MT MA sigs)) '(LSU wbuf1))
	     (or (equal (INST-stg i) '(LSU RS0))
		 (equal (INST-stg i) '(LSU RS1))
		 (equal (INST-stg i) '(LSU wbuf1))))
  :hints (("goal" :in-theory (enable step-INST MT-def-non-rec-functions
				     LSU-stg-p)))
  :rule-classes nil)

(defthm stages-reachable-to-lsu-wbuf0
    (implies (equal (INST-stg (step-INST i MT MA sigs)) '(LSU wbuf0))
	     (or (equal (INST-stg i) '(LSU RS0))
		 (equal (INST-stg i) '(LSU RS1))
		 (equal (INST-stg i) '(LSU wbuf0))
		 (equal (INST-stg i) '(LSU wbuf1))))
  :hints (("goal" :in-theory (enable step-INST MT-def-non-rec-functions
				     LSU-stg-p)))
  :rule-classes nil)

(defthm stages-reachable-to-lsu-rbuf
    (implies (equal (INST-stg (step-INST i MT MA sigs)) '(LSU rbuf))
	     (or (equal (INST-stg i) '(LSU RS0))
		 (equal (INST-stg i) '(LSU RS1))
		 (equal (INST-stg i) '(LSU rbuf))))
  :hints (("goal" :in-theory (enable step-INST MT-def-non-rec-functions
				     LSU-stg-p)))
  :rule-classes nil)

(defthm stages-reachable-to-lsu-wbuf0-lch
    (implies (equal (INST-stg (step-INST i MT MA sigs))
		    '(LSU wbuf0 lch))
	     (equal (INST-stg i) '(LSU wbuf0)))
  :hints (("goal" :in-theory (enable step-INST MT-def-non-rec-functions
				     LSU-stg-p)))
  :rule-classes nil)

(defthm stages-reachable-to-lsu-wbuf1-lch
    (implies (equal (INST-stg (step-INST i MT MA sigs))
		    '(LSU wbuf1 lch))
	     (equal (INST-stg i) '(LSU wbuf1)))
  :hints (("goal" :in-theory (enable step-INST MT-def-non-rec-functions
				     LSU-stg-p)))
  :rule-classes nil)

(defthm stages-reachable-to-lsu-lch
    (implies (equal (INST-stg (step-INST i MT MA sigs))
		    '(LSU lch))
	     (equal (INST-stg i) '(LSU rbuf)))
  :hints (("goal" :in-theory (enable step-INST MT-def-non-rec-functions
				     LSU-stg-p)))
  :rule-classes nil)

(defthm reachable-stages-to-LSU-issued-stg-p
    (implies (LSU-issued-stg-p (INST-stg (step-INST i MT MA sigs)))
	     (or (LSU-stg-p (INST-stg i))
		 (LSU-issued-stg-p (INST-stg i))))
  :hints (("Goal" :in-theory (enable LSU-stg-p LSU-issued-stg-p
				     COMMIT-STG-P lift-b-ops
				     COMPLETE-STG-P
				     execute-stg-p
				     step-INST MT-def-non-rec-functions)))
  :rule-classes nil)

; An instruction can be in an execute stage if its previous stage is
; (DQ 0) or one of the execute stages. 
(defthm stages-reachable-to-execute
    (implies (and (INST-p i)
		  (execute-stg-p (INST-stg (step-INST i MT MA sigs))))
	     (or (equal (INST-stg i) '(DQ 0))
		 (execute-stg-p (INST-stg i))))
  :hints (("goal" :in-theory (enable step-INST MT-def-non-rec-functions
				     DQ-stg-p)))
  :rule-classes nil)

; An instruction can be in a complete stage if its previous stage is 
; (DQ 0) or one of the execute stages. 
(defthm stages-reachable-to-complete
    (implies (and (INST-p i)
		  (complete-stg-p (INST-stg (step-INST i MT MA sigs))))
	     (or (equal (INST-stg i) '(DQ 0))
		 (execute-stg-p (INST-stg i))
		 (complete-stg-p (INST-stg i))))
  :hints (("goal" :in-theory (enable step-INST MT-def-non-rec-functions
				     DQ-stg-p)))
  :rule-classes nil)

(defthm stages-reachable-to-complete-normal
    (implies (and (INST-p i)
		  (equal (INST-stg (step-INST i MT MA sigs)) '(complete)))
	     (or (equal (INST-stg i) '(DQ 0))
		 (equal (INST-stg i) '(IU RS0))
		 (equal (INST-stg i) '(IU RS1))
		 (equal (INST-stg i) '(MU lch2))
		 (equal (INST-stg i) '(BU RS0))
		 (equal (INST-stg i) '(BU RS1))
		 (equal (INST-stg i) '(LSU lch))
		 (equal (INST-stg i) '(complete))))
  :hints (("goal" :in-theory (enable step-INST DQ-stg-p
				     execute-stg-p IU-stg-p MU-stg-p
				     BU-stg-p
				     MT-def-non-rec-functions)))
  :rule-classes nil)

(defthm stages-reachable-to-complete-wbuf0
    (implies (and (INST-p i)
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(complete wbuf0)))
	     (or (equal (INST-stg i) '(LSU wbuf0 lch))
		 (equal (INST-stg i) '(LSU wbuf1 lch))
		 (equal (INST-stg i) '(complete wbuf0))
		 (equal (INST-stg i) '(complete wbuf1))))
  :hints (("goal" :in-theory (enable step-INST
				     EXECUTE-STG-P LSU-stg-p
				     complete-stg-p
				     MT-def-non-rec-functions)))
  :rule-classes nil)

(defthm stages-reachable-to-complete-wbuf1
    (implies (and (INST-p i)
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(complete wbuf1)))
	     (or (equal (INST-stg i) '(LSU wbuf1 lch))
		 (equal (INST-stg i) '(complete wbuf1))))
  :hints (("goal" :in-theory (enable step-INST
				     execute-stg-p LSU-stg-p
				     complete-stg-p
				     MT-def-non-rec-functions)))
  :rule-classes nil)

(defthm stages-reachable-to-commit-wbuf0
    (implies (and (INST-p i)
		  (equal (INST-stg (step-INST i MT MA sigs)) '(commit wbuf0)))
	     (or (equal (INST-stg i) '(complete wbuf0))
		 (equal (INST-stg i) '(complete wbuf1))
		 (equal (INST-stg i) '(commit wbuf0))
		 (equal (INST-stg i) '(commit wbuf1))))
  :hints (("goal" :in-theory (enable step-INST
				     complete-stg-p
				     commit-stg-p
				     MT-def-non-rec-functions)))
  :rule-classes nil)

(defthm stages-reachable-to-commit-wbuf1
    (implies (and (INST-p i)
		  (equal (INST-stg (step-INST i MT MA sigs)) '(commit wbuf1)))
	     (or (equal (INST-stg i) '(complete wbuf1))
		 (equal (INST-stg i) '(commit wbuf1))))
  :hints (("goal" :in-theory (enable step-INST
				     complete-stg-p
				     MT-def-non-rec-functions)))
  :rule-classes nil)

(defthm stages-reachable-to-retire-stg
    (implies (retire-stg-p (INST-stg (step-INST i MT MA sigs)))
	     (or (equal (INST-stg i) '(retire))
		 (equal (INST-stg i) '(complete))
		 (equal (INST-stg i) '(complete wbuf0))
		 (equal (INST-stg i) '(complete wbuf1))
		 (equal (INST-stg i) '(commit wbuf0))
		 (equal (INST-stg i) '(commit wbuf1))))
  :hints (("Goal" :in-theory (enable step-INST MT-def-non-rec-functions
				     complete-stg-p
				     RETIRE-STG-P)))
  :rule-classes nil)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; INST-functions and step-INST
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm INST-ID-fetched-inst
    (equal (INST-ID (fetched-inst MT ISA spc smc)) (MT-new-ID MT))
  :hints (("Goal" :in-theory (enable MT-def))))

(defthm INST-ID-exintr-INST
    (equal (INST-ID (exintr-INST MT ISA spc)) (MT-new-ID MT))
  :hints (("Goal" :in-theory (enable MT-def))))

(defthm INST-ID-step-INST
    (equal (INST-ID (step-INST i MT MA sigs)) (INST-ID i))
  :hints (("Goal" :in-theory (enable MT-def))))

     

(defthm INST-modified-exintr-INST
    (equal (INST-modified? (exintr-INST MT pre smc)) smc)
  :hints (("Goal" :in-theory (enable exintr-INST))))

(defthm INST-modified-fetched-inst
    (equal (INST-modified? (fetched-inst MT ISA spc smc))
	   (if (MT-no-write-at (ISA-pc ISA) MT)
	       (bfix smc) 1))
  :hints (("Goal" :in-theory (enable fetched-inst lift-b-ops))))

(defthm INST-modified-step-INST
    (implies (INST-p i)
	     (equal (INST-modified? (step-INST i MT MA sigs))
		    (INST-modified? i)))
  :hints (("Goal" :in-theory (enable MT-def))))

(defthm INST-first-modified-step-INST
    (implies (INST-p i)
	     (equal (INST-first-modified? (step-INST i MT MA sigs))
		    (INST-first-modified? i)))
  :hints (("Goal" :in-theory (enable MT-def))))

(defthm inst-first-modified-fetched-inst
    (equal (INST-first-modified? (fetched-inst MT ISA spc smc))
	   (b-nor smc (if (MT-no-write-at (ISA-pc ISA) MT) 1 0)))
  :hints (("Goal" :in-theory (enable fetched-inst equal-b1p-converter
				     lift-b-ops))))

(defthm inst-specultv-fetched-inst
    (equal (inst-specultv? (fetched-inst MT ISA spc smc))
	   spc)
  :hints (("Goal" :in-theory (enable MT-def))))

(defthm inst-specultv-exintr-INST
    (equal (inst-specultv? (exintr-INST MT ISA smc)) 0)
  :hints (("Goal" :in-theory (enable MT-def))))

(defthm inst-specultv-step-INST
    (equal (inst-specultv? (step-INST i MT MA sigs))
	   (inst-specultv? i))
  :hints (("Goal" :in-theory (enable MT-def))))

(defthm INST-br-predict-fetched-inst
    (equal (INST-br-predict? (fetched-inst MT ISA flg flg2)) 0)
  :hints (("Goal" :in-theory (enable fetched-inst))))

(defthm INST-br-predict-exintr-INST
    (equal (INST-br-predict? (exintr-INST MT ISA flg)) 0)
  :hints (("Goal" :in-theory (enable exintr-INST))))

; Field br-predict? of a control vector stores the branch prediction outcome.
(defthm cntlv-br-predict-INST-cntlv
    (implies (INST-p i)
	     (equal (cntlv-br-predict? (INST-cntlv i))
		    (INST-br-predict? i)))
  :hints (("goal" :in-theory (enable INST-cntlv))))

(defthm cntlv-sync-and-branch-of-INST-cntlv-exclusive
    (implies (and (INST-p i)
		  (b1p (cntlv-sync? (INST-cntlv i))))
	     (equal (logbit 3 (cntlv-exunit (INST-cntlv i))) 0))
  :hints (("goal" :in-theory (enable INST-cntlv))))

; INST-exintr
(defthm INST-exintr-fetched-inst
    (equal (INST-exintr? (fetched-inst MT ISA flg flg2)) 0)
  :hints (("Goal" :in-theory (enable fetched-inst))))

(defthm INST-exintr-step-INST
    (equal (INST-exintr? (step-INST i MT MA sigs)) (INST-exintr? i))
  :hints (("Goal" :in-theory (enable step-INST MT-def))))

(defthm INST-exintr-exintr-INST
    (equal (INST-exintr? (exintr-INST MT ISA smc)) 1)
  :hints (("Goal" :in-theory (enable exintr-INST))))

(defthm INST-word-fetched-inst
    (equal (INST-word (fetched-inst MT ISA spc smc))
	   (read-mem (ISA-pc ISA) (ISA-mem ISA)))
  :Hints (("goal" :in-theory (enable fetched-inst INST-word
				     INST-pc INST-mem))))

(defthm Inst-word-step-INST
    (equal (Inst-word (step-INST i MT MA sigs)) (Inst-word i))
  :hints (("Goal" :in-theory (enable MT-def ))))

(defthm Inst-opcode-step-INST
    (equal (Inst-opcode (step-INST i MT MA sigs)) (Inst-opcode i))
  :hints (("Goal" :in-theory (enable MT-def ))))

(defthm Inst-ra-step-INST
    (equal (Inst-ra (step-INST i MT MA sigs)) (Inst-ra i))
  :hints (("Goal" :in-theory (enable MT-def ))))

(defthm Inst-rb-step-INST
    (equal (Inst-rb (step-INST i MT MA sigs)) (Inst-rb i))
  :hints (("Goal" :in-theory (enable MT-def ))))

(defthm Inst-rc-step-INST
    (equal (Inst-rc (step-INST i MT MA sigs)) (Inst-rc i))
  :hints (("Goal" :in-theory (enable MT-def ))))

(defthm Inst-im-step-INST
    (equal (Inst-im (step-INST i MT MA sigs)) (Inst-im i))
  :hints (("Goal" :in-theory (enable MT-def ))))

(defthm INST-br-predict-step-non-IFU-INST
    (implies (not (IFU-stg-p (INST-stg i)))
	     (equal (INST-br-predict? (step-INST i MT MA sigs))
		    (INST-br-predict? i)))
  :hints (("goal" :in-theory (enable MT-def))))

(defthm INST-br-predict-step-INST
    (implies (and (not (b1p (DQ-full? (MA-DQ MA))))
		  (IFU-stg-p (INST-stg i)))
	     (equal (INST-br-predict? (step-INST i MT MA sigs))
		    (IFU-branch-predict? (MA-IFU MA) MA sigs)))
  :hints (("goal" :in-theory (enable step-INST step-INST-IFU
				     equal-b1p-converter))))


(defthm INST-writeback-p-iff-INST-wb
    (iff (INST-writeback-p i) (b1p (INST-wb? i)))
  :rule-classes
  ((:rewrite :corollary
	     (implies (b1p (INST-wb? i)) (INST-writeback-p i)))
   (:rewrite :corollary
	     (implies (not (b1p (INST-wb? i))) (not (INST-writeback-p i)))))
  :hints (("goal" :in-theory (enable INST-writeback-p INST-wb? lift-b-ops
				     INST-opcode INST-cntlv
				     decode rdb logbit*))))

; Following lemmas show that return values of INST functions don't change
; after step-INST. 
; 
; For example, (INST-writeback-p i') = (INST-writeback i) if i'
; is INST i updated by step-INST. 
(defthm INST-writeback-p-step-INST
    (implies (INST-p i)
	     (equal (INST-writeback-p (step-INST i MT MA sigs))
		    (INST-writeback-p i)))
  :hints (("goal" :in-theory (enable INST-writeback-p))))

(defthm INST-cntlv-step-inst-if-IFU-stg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (INST-p i)
		  (IFU-stg-p (INST-stg i))
		  (not (b1p (DQ-full? (MA-DQ MA)))))
	     (equal (INST-cntlv (step-INST i MT MA sigs))
		    (decode (INST-opcode i)
			    (IFU-branch-predict? (MA-IFU MA) MA sigs))))
  :hints (("goal" :in-theory (enable  inst-cntlv))))

(defthm INST-cntlv-step-non-IFU-INST
    (implies (not (IFU-stg-p (INST-stg i)))
	     (equal (INST-cntlv (step-INST i MT MA sigs))
		    (INST-cntlv i)))
  :hints (("goal" :in-theory (enable INST-cntlv))))

(defthm INST-IU-step-inst
    (implies (and (INST-p i) (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (INST-IU? (step-INST i MT MA sigs))
		    (INST-IU? i)))
  :hints (("goal" :in-theory (enable INST-function-def
				     INST-cntlv decode lift-b-ops
				     rdb logbit*))))

(defthm INST-no-unit-step-inst
    (implies (and (INST-p i) (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (INST-no-unit? (step-INST i MT MA sigs))
		    (INST-no-unit? i)))
  :hints (("goal" :in-theory (enable INST-function-def
				     INST-cntlv decode lift-b-ops
				     rdb logbit*))))

(defthm INST-BU-step-inst
    (implies (and (INST-p i) (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (INST-BU? (step-INST i MT MA sigs))
		    (INST-BU? i)))
  :hints (("goal" :in-theory (enable INST-function-def
				     INST-cntlv decode lift-b-ops
				     rdb logbit*))))

(defthm INST-LSU-step-inst
    (implies (and (INST-p i) (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (INST-LSU? (step-INST i MT MA sigs))
		    (INST-LSU? i)))
  :hints (("goal" :in-theory (enable INST-function-def
				     INST-cntlv decode lift-b-ops
				     rdb logbit*))))

(defthm INST-MU-step-inst
    (implies (and (INST-p i) (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (INST-MU? (step-INST i MT MA sigs))
		    (INST-MU? i)))
  :hints (("goal" :in-theory (enable INST-function-def
				     INST-cntlv decode lift-b-ops
				     rdb logbit*))))

(defthm INST-ld-st-step-inst
    (equal (INST-ld-st? (step-INST i MT MA sigs))
	   (INST-ld-st? i))
  :hints (("goal" :in-theory (enable INST-function-def
				     INST-cntlv decode lift-b-ops
				     rdb logbit*))))

(defthm INST-sync-step-inst
    (equal (INST-sync? (step-INST i MT MA sigs))
	   (INST-sync? i))
  :hints (("goal" :in-theory (enable INST-sync? INST-cntlv decode lift-b-ops
				     rdb logbit*))))

(defthm INST-wb-step-inst
    (equal (INST-wb? (step-INST i MT MA sigs))
	   (INST-wb? i))
  :hints (("goal" :in-theory (enable INST-function-def
				     INST-cntlv decode lift-b-ops
				     rdb logbit*))))

(defthm INST-wb-sreg-step-inst
    (equal (INST-wb-sreg? (step-INST i MT MA sigs))
	   (INST-wb-sreg? i))
  :hints (("goal" :in-theory (enable INST-function-def
				     INST-cntlv decode lift-b-ops
				     rdb logbit*))))

(defthm INST-rfeh-step-inst
    (equal (INST-rfeh? (step-INST i MT MA sigs))
	   (INST-rfeh? i))
  :hints (("goal" :in-theory (enable INST-function-def
				     INST-cntlv decode lift-b-ops
				     rdb logbit*))))

(defthm INST-dest-reg-step-INST
    (equal (Inst-dest-reg (step-INST i MT MA sigs)) (Inst-dest-reg i))
  :hints (("Goal" :in-theory (enable MT-def ))))

(defthm INST-tag-step-INST
    (implies (and (INST-p i) (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (not (DQ-stg-p (INST-stg i))))
	     (equal (INST-tag (step-INST i MT MA sigs)) (INST-tag i)))
  :hints (("goal" :in-theory (enable step-INST
				     step-INST-low-level-functions))))

(defthm INST-pre-ISA-step-INST
    (equal (INST-pre-ISA (step-INST i MT MA sigs))
	   (INST-pre-ISA i))
  :hints (("goal" :in-theory (enable MT-def))))

(defthm INST-post-ISA-step-INST
    (equal (INST-post-ISA (step-INST i MT MA sigs))
	   (INST-post-ISA i))
  :hints (("goal" :in-theory (enable MT-def))))
  
(defthm INST-pre-ISA-fetched-inst
    (equal (INST-pre-ISA (fetched-inst MT ISA spc smc)) ISA)
  :hints (("goal" :in-theory (enable MT-def))))

(defthm INST-post-ISA-fetched-inst
    (equal (INST-post-ISA (fetched-inst MT ISA spc smc))
	   (ISA-step ISA (ISA-input 0)))
  :hints (("goal" :in-theory (enable MT-def))))

(defthm INST-pre-ISA-exintr-INST
    (equal (INST-pre-ISA (exintr-INST MT ISA smc)) ISA)
  :hints (("goal" :in-theory (enable MT-def))))

(defthm INST-post-ISA-exintr-INST
    (equal (INST-post-ISA (exintr-INST MT ISA smc))
	   (ISA-step ISA (ISA-input 1)))
  :hints (("goal" :in-theory (enable MT-def))))

(defthm INST-pc-step-INST
    (equal (INST-pc (step-INST i MT MA sigs)) (INST-pc i))
  :hints (("Goal" :in-theory (enable MT-def))))

(defthm INST-su-step-INST
    (equal (INST-su (step-INST i MT MA sigs)) (INST-su i))
  :hints (("Goal" :in-theory (enable MT-def))))

(defthm INST-br-target-step
    (equal (INST-br-target (step-INST i MT MA sigs)) (INST-br-target i))
  :hints (("goal" :in-theory (enable INST-br-target))))

(defthm INST-branch-taken-step-inst
    (equal (INST-branch-taken? (step-INST i MT MA sigs))
	   (INST-branch-taken? i))
  :hints (("goal" :in-theory (enable INST-branch-taken?))))

(defthm INST-src-val1-step-INST
    (equal (INST-src-val1 (step-INST i MT MA sigs)) (INST-src-val1 i))
  :hints (("Goal" :in-theory (enable MT-def))))

(defthm INST-src-val2-step-INST
    (equal (INST-src-val2 (step-INST i MT MA sigs)) (INST-src-val2 i))
  :hints (("Goal" :in-theory (enable MT-def))))

(defthm INST-src-val3-step-INST
    (equal (INST-src-val3 (step-INST i MT MA sigs)) (INST-src-val3 i))
  :hints (("Goal" :in-theory (enable MT-def))))

(defthm INST-dest-val-step-INST
    (equal (INST-dest-val (step-INST i MT MA sigs))
	   (INST-dest-val i))
  :hints (("goal" :in-theory (enable INST-function-def))))

(defthm INST-IU-op-step-INST
    (implies (and (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs))
	     (equal (INST-IU-op? (step-INST i MT MA sigs)) (INST-IU-op? i)))
  :hints (("goal" :in-theory (enable  inst-function-def inst-cntlv
				      decode lift-b-ops rdb logbit*))))
	   
(defthm INST-LSU-op-step-INST
    (implies (and (INST-p i) (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (INST-LSU-op? (step-INST i MT MA sigs)) (INST-LSU-op? i)))
  :hints (("goal" :in-theory (enable  inst-function-def inst-cntlv
				      decode lift-b-ops rdb logbit*))))

(defthm INST-load-addr-step-inst
    (equal (INST-load-addr (step-INST i MT MA sigs))
	   (INST-load-addr i))
  :hints (("Goal" :in-theory (enable MT-def))))

(defthm INST-load-step-INST
    (implies (and (INST-p i) (MAETT-p MT)
		  (MA-state-p MA) (MA-input-p sigs))
	     (equal (INST-load? (step-INST i MT MA sigs))
		    (INST-load? i)))
  :hints (("goal" :in-theory (enable INST-function-def lift-b-ops
				     ISA-functions decode
				     rdb logbit*))))

(defthm INST-store-step-INST
    (implies (and (INST-p i) (MAETT-p MT)
		  (MA-state-p MA) (MA-input-p sigs))
	     (equal (INST-store? (step-INST i MT MA sigs))
		    (INST-store? i)))
  :hints (("goal" :in-theory (enable INST-function-def lift-b-ops
				     ISA-functions decode
				     rdb logbit*))))

(defthm INST-LSU-if-INST-store
    (implies (b1p (INST-store? i))
	     (equal (INST-LSU? i) 1))
  :hints (("Goal" :in-theory (enable INST-LSU? lift-b-ops
				     equal-b1p-converter
				     b1p-bit-rewriter
				     INST-store?))))

(defthm INST-LSU-if-INST-load
    (implies (b1p (INST-load? i))
	     (equal (INST-LSU? i) 1))
  :hints (("Goal" :in-theory (enable INST-LSU? lift-b-ops
				     equal-b1p-converter
				     b1p-bit-rewriter
				     INST-load?))))

(defthm INST-LSU-IF-INST-store-2
    (implies (not (b1p (INST-LSU? i))) (not (b1p (INST-store? i))))
  :hints (("goal" :In-theory (enable INST-LSU? lift-b-ops b1p-bit-rewriter
				     INST-store?))))

(defthm INST-LSU-IF-INST-load-2
    (implies (not (b1p (INST-LSU? i)))
	     (not (b1p (INST-load? i))))
  :hints (("goal" :In-theory (enable INST-LSU? lift-b-ops b1p-bit-rewriter
				     INST-load?))))

(defthm INST-store-addr-step-INST
    (equal (INST-store-addr (step-INST i MT MA sigs))
	   (INST-store-addr i))
  :hints (("goal" :in-theory (enable INST-function-def lift-b-ops))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;   Lemmas about relations between instructions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Following lemmas show that distinct instructions are not equal to each
; other after step-INST.
(encapsulate nil
(local
(defthm INST-new-ID-distinct-if-INST-in-help
    (implies (and (ID-LT-ALL-P trace new-ID)
		  (member-equal i trace))
	     (< (INST-ID i) new-ID))))

(defthm INST-new-ID-distinct-if-INST-in
    (implies (and (weak-inv MT)
		  (INST-in i MT))
	     (< (INST-ID i) (MT-new-ID MT)))
  :hints (("goal" :in-theory (enable weak-inv INST-in
				     MT-new-ID-distinct-p)
		  :restrict ((INST-new-ID-distinct-if-INST-in-help
			      ((trace (MT-trace MT)))))))
  :rule-classes :linear)
)

(encapsulate nil
(local
 (defthm INST-ID-distinct-help
     (implies (and (member-equal i2 trace)
		   (equal (INST-ID i1) (INST-ID i2)))
	      (member-eq-ID i1 trace))))

(local
(defthm INST-ID-distinct-local
    (implies (and (distinct-IDs-p trace)
		  (INST-listp trace)
		  (member-equal I1 trace)
		  (member-equal I2 trace)
		  (not (equal I1 I2)))
	     (not (equal (INST-ID I1) (INST-ID I2))))))

(defthm INST-ID-distinct
    (implies (and (weak-inv MT)
		  (MAETT-p MT)
		  (INST-in I1 MT) (INST-in I2 MT)
		  (not (equal I1 I2)))
	     (not (equal (INST-ID I1) (INST-ID I2))))
  :hints (("goal" :in-theory (enable weak-inv MT-distinct-IDs-p
				     MAETT-p INST-in))))
)

(defthm equal-step-INSTs
    (implies (and (weak-inv MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in I1 MT)
		  (INST-in I2 MT))
	     (equal (equal (step-INST I1 MT MA sigs)
			   (step-INST I2 MT MA sigs))
		    (equal I1 I2)))
  :hints (("goal" :cases ((equal (INST-ID (step-INST I1 MT MA sigs))
				 (INST-ID (step-INST I2 MT MA sigs)))))
	  ("subgoal 2" :in-theory (disable INST-ID-step-INST))))

(defthm equal-step-INST-fetched-inst
    (implies (and (weak-inv MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT))
	     (not (equal (step-INST i MT MA sigs)
			 (fetched-inst MT ISA spc smc))))
  :hints (("goal" :cases ((equal (INST-ID (step-INST i MT MA sigs))
				 (INST-ID (fetched-inst MT ISA spc smc)))))
	  ("Subgoal 2" :in-theory (disable INST-ID-step-INST))))

(defthm equal-step-Inst-word-for-exintr
    (implies (and (weak-inv MT)
		  (MAETT-p MT)
		  (INST-in i MT))
	     (not (equal (step-INST i MT MA sigs)
			 (exintr-INST MT ISA spc))))
  :hints (("goal" :cases ((equal (INST-ID (step-INST i MT MA sigs))
				 (INST-ID (exintr-INST MT ISA spc)))))
	  ("Subgoal 2" :in-theory (disable INST-ID-step-INST))))

(encapsulate nil
(local
 (defthm MT-modify-exintr-INST-help
     (not (trace-modify-p (exintr-INST MT ISA smc) trace))
   :hints (("goal" :in-theory (enable INST-MODIFY-P)))))

(defthm MT-modify-exintr-INST
    (not (MT-modify-p (exintr-INST MT ISA smc) MT2))
  :hints (("goal" :in-theory (enable MT-modify-p))))
)

(defthm MT-modified-p-car-MT-trace
    (implies (and (MAETT-p MT) 
		  (consp (MT-trace MT)))
	     (not (MT-modify-p (car (MT-trace MT)) MT)))
  :hints (("goal" :in-theory (enable MT-modify-p))))

; A non-speculative instruction is not a member of trace-all-specultv-p.
(defthm inst-specultv-is-not-member-equal-to-trace-all-specultv
    (implies (and (trace-all-specultv-p trace)
		  (not (b1p (inst-specultv? i))))
	     (not (member-equal i trace))))

(encapsulate nil
(local
(defthm INST-in-order-p-inst-specultv-help-help
    (implies (and (member-equal i trace)
		  (trace-all-specultv-p trace)
		  (INST-listp trace))
	     (equal (inst-specultv? i) 1))
  :hints (("goal" :in-theory (enable equal-b1p-converter)))))

(local
(defthm INST-in-order-p-inst-specultv-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (trace-correct-speculation-p trace)
		  (b1p (inst-specultv? i))
		  (not (b1p (inst-specultv? j)))
		  (INST-listp trace))
	     (not (member-in-order i j trace)))
  :hints (("goal" :in-theory (enable member-in-order*
           inst-specultv-is-not-member-equal-to-trace-all-specultv)))))

; If instruction i precedes instruction j in program order, and
; if i is a speculatively executed instruction, so is j.
(defthm INST-in-order-p-inst-specultv
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA)
		  (b1p (inst-specultv? i))
		  (INST-in-order-p i j MT))
	     (b1p (inst-specultv? j)))
  :hints (("goal" :use (:instance INST-in-order-p-inst-specultv-help
				  (trace (MT-trace MT)))
		  :in-theory (enable inv correct-speculation-p
				     INST-in INST-in-order-p)))
  :rule-classes
  ((:rewrite :corollary
	     (implies (and (inv MT MA)
			   (b1p (inst-specultv? i))
			   (not (b1p (inst-specultv? j)))
			   (MAETT-p MT) (MA-state-p MA))
		      (not (INST-in-order-p i j MT))))))
)

(encapsulate nil
(local
(defthm INST-in-order-p-INST-modified-help-help
    (implies (and (member-equal i trace)
		  (trace-correct-modified-flgs-p trace MT flg)
		  (b1p flg)
		  (INST-listp trace))
	     (equal (INST-modified? i) 1))
  :hints (("goal" :in-theory (enable equal-b1p-converter)))))

(local
(defthm INST-in-order-p-INST-modified-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (trace-correct-modified-flgs-p trace MT flg)
		  (b1p (INST-modified? i))
		  (not (b1p (INST-modified? j)))
		  (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA))
	     (not (member-in-order i j trace)))
  :hints (("goal" :in-theory (enable member-in-order*)))))

; If instruction i precedes instruction j, and (INST-modified? i) is
; true, then so is (INST-modified? j).  INST-modified? is defined in
; the same way as inst-specultv?, and (INST-modifier? i) is false only
; if no instruction before i is modified by self-modifying code.
(defthm INST-in-order-p-INST-modified
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA)
		  (b1p (INST-modified? i))
		  (INST-in-order-p i j MT))
	     (b1p (INST-modified? j)))
  :hints (("goal" :use (:instance INST-in-order-p-INST-modified-help
				  (trace (MT-trace MT))
				  (flg 0))
		  :in-theory (enable inv weak-inv
				     correct-modified-flgs-p
				     INST-in INST-in-order-p)))
  :rule-classes
  ((:rewrite :corollary
	     (implies (and (inv MT MA)
			   (b1p (INST-modified? i))
			   (not (b1p (INST-modified? j)))
			   (MAETT-p MT) (MA-state-p MA))
		      (not (INST-in-order-p i j MT))))))
)

(encapsulate nil
(local
(encapsulate nil
(local
(defthm trace-modify-p-if-INST-modify-p
    (implies (and (inv MT MA)
		  (member-equal i trace)
		  (member-equal j trace)
		  (member-in-order i j trace)
		  (subtrace-p trace MT)
		  (not (trace-modify-p j trace)))
	     (not (INST-modify-p i j)))
  :hints (("goal" :in-theory (enable member-in-order*)))))

(defthm MT-modify-p-if-INST-modify-p
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-p j)
		  (INST-in i MT) (INST-in j MT)
		  (INST-in-order-p i j MT)
		  (not (MT-modify-p j MT)))
	     (not (INST-modify-p i j)))
  :hints (("goal" :in-theory (enable INST-in INST-in-order-p
				     MT-modify-p))))
))

(local
(encapsulate nil 
(local
(defthm trace-INST-modified-if-MT-modify-p
    (implies (and (TRACE-CORRECT-MODIFIED-FLGS-P trace MT sticky)
		  (member-equal j trace)
		  (not (b1p (INST-modified? j))))
	     (not (MT-modify-p j MT)))))

(defthm INST-modified-if-MT-modify-p
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p j)
		  (INST-in j MT)
		  (not (b1p (INST-modified? j))))
	     (not (MT-modify-p j MT)))
  :hints (("goal" :in-theory (enable inv weak-inv INST-in
				     correct-modified-flgs-p))))
))

(defthm INST-modified-if-INST-modify-p
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-p j)
		  (INST-in i MT) (INST-in j MT)
		  (INST-in-order-p i j MT)
		  (INST-modify-p i j))
	     (b1p (INST-modified? j)))
  :rule-classes
  ((:rewrite :corollary
	     (implies (and (inv MT MA)
			   (MAETT-p MT) (MA-state-p MA)
			   (INST-p i) (INST-p j)
			   (INST-in i MT) (INST-in j MT)
			   (INST-modify-p i j)
			   (not (b1p (INST-modified? j))))
		      (not (INST-in-order-p i j MT))))))

)
(in-theory (disable INST-modified-if-INST-modify-p))

(encapsulate nil
(local
(defthm inst-in-order-p-INST-start-specultv-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (trace-correct-speculation-p trace)
		  (b1p (INST-start-specultv? i))
		  (not (b1p (inst-specultv? j)))
		  (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA))
	     (not (member-in-order i j trace)))
  :hints (("goal" :in-theory (enable member-in-order*)))
  :rule-classes nil))

; Suppose instruction i precedes instruction j.  If i is not committed, 
; and if i starts a speculative execution, j is speculatively executed
; instruction.
(defthm inst-in-order-p-INST-start-specultv
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA)
		  (b1p (INST-start-specultv? i))
		  (INST-in-order-p i j MT))
	     (b1p (inst-specultv? j)))
  :hints (("goal" :in-theory (enable inv correct-speculation-p
				     INST-in-order-p)
		  :use (:instance inst-in-order-p-INST-start-specultv-help
				  (trace (MT-trace MT))
				  (MT MT) (MA MA))))
  :rule-classes
  ((:rewrite :corollary
	     (implies (and (inv MT MA)
			   (b1p (INST-start-specultv? i))
			   (not (b1p (inst-specultv? j)))
			   (MAETT-p MT) (MA-state-p MA))
		      (not (INST-in-order-p i j MT)))))
  )
)

; Suppose trace is a subtrace of MT.  If (car trace) is a
; speculatively executed instruction, any instruction in (cdr trace)
; is also speculatively executed.
(defthm inst-specultv-car
    (implies (and (inv MT MA)
		  (member-equal i (cdr trace))
		  (consp trace)
		  (not (b1p (inst-specultv? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace))
	     (equal (inst-specultv? (car trace)) 0))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter)
				  (INST-in-order-p-inst-specultv))
		  :use (:instance INST-in-order-p-inst-specultv
				  (i (car trace)) (j i)))))

; Suppose instruction i follows instruction j=(car trace).  If j is an
; exception-raising instruction, then i is speculatively executed
; instruction.  
(defthm INST-excpt-car
    (implies (and (inv MT MA)
		  (consp trace)
		  (member-equal i (cdr trace))
		  (not (b1p (inst-specultv? i)))
		  (not (committed-p (car trace)))
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace))
	     (equal (INST-excpt? (car trace)) 0))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter
				   INST-start-specultv? lift-b-ops)
				  (inst-in-order-p-INST-start-specultv))
		  :use (:instance inst-in-order-p-INST-start-specultv
				  (i (car trace)) (j i)))))

(defthm INST-start-specultv-car
    (implies (and (inv MT MA)
		  (member-equal i (cdr trace))
		  (consp trace)
		  (not (b1p (inst-specultv? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace))
	     (equal (INST-start-specultv? (car trace)) 0))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter)
				  (INST-IN-ORDER-P-INST-START-SPECULTV))
		  :use (:instance INST-IN-ORDER-P-INST-START-SPECULTV
				  (i (car trace)) (j i)))))
(in-theory (disable INST-start-specultv-car))

; If INST-modified? is true for (car trace), INST-modified? is also true for
; any instruction in (cdr trace).
(defthm INST-modified-car
    (implies (and (inv MT MA)
		  (member-equal i (cdr trace))
		  (consp trace)
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace))
	     (equal (INST-modified? (car trace)) 0))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter)
				  (INST-in-order-p-INST-modified))
		  :use (:instance INST-in-order-p-INST-modified
				  (i (car trace))
				  (j i)))))

; If an instruction i follows instruction j=(car trace).  If j is an
; context synchronization instruction, then i is a speculatively executed
; instruction.
(defthm INST-context-sync-car
    (implies (and (inv MT MA)
		  (consp trace)
		  (member-equal i (cdr trace))
		  (not (b1p (inst-specultv? i)))
		  (not (committed-p (car trace)))
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace))
	     (equal (INST-context-sync? (car trace)) 0))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter
				   INST-start-specultv? lift-b-ops)
				  (inst-in-order-p-INST-start-specultv))
		  :use (:instance inst-in-order-p-INST-start-specultv
				  (i (car trace)) (j i)))))
;(in-theory (disable inst-specultv-is-not-member-equal-to-trace-all-specultv))

(defthm not-inst-modified-car-MT-trace
    (implies (and (inv MT MA)
		  (consp (MT-trace MT))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-modified? (car (MT-trace MT))) 0))
  :hints (("goal" :in-theory (enable inv weak-inv
				     correct-modified-flgs-p)
		  :expand (TRACE-CORRECT-MODIFIED-FLGS-P (MT-TRACE MT)
							 MT 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Opening INST-inv 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deflabel begin-INST-inv-opener)		     
(defthm INST-inv-for-IFU
    (implies (IFU-stg-p (INST-stg i))
	     (equal (INST-inv i MA)
		    (IFU-inst-inv i MA)))
  :hints (("Goal" :in-theory (enable INST-inv))))

(defthm DQ-inv-for-execute
    (implies (DQ-stg-p (INST-stg i))
	     (equal (INST-inv i MA)
		    (DQ-inst-inv i MA)))
  :hints (("Goal" :in-theory (enable INST-inv))))

(defthm INST-inv-for-execute
    (implies (execute-stg-p (INST-stg i))
	     (equal (INST-inv i MA)
		    (execute-inst-inv i MA)))
  :hints (("Goal" :in-theory (enable INST-inv))))

(defthm INST-inv-for-complete
    (implies (complete-stg-p (INST-stg i))
	     (equal (INST-inv i MA)
		    (complete-inst-inv i MA)))
  :hints (("Goal" :in-theory (enable INST-inv))))

(defthm INST-inv-for-commit
    (implies (commit-stg-p (INST-stg i))
	     (equal (INST-inv i MA)
		    (commit-inst-inv i MA)))
  :hints (("Goal" :in-theory (enable INST-inv))))
(deflabel end-INST-inv-opener)		     

(deftheory INST-inv-open-lemmas
    (set-difference-theories (universal-theory 'end-INST-inv-opener)
			     (universal-theory 'begin-INST-inv-opener)))

(deftheory INST-inv-opener
    (set-difference-theories 
     (union-theories (theory 'inst-inv-def)
		     (theory 'INST-inv-open-lemmas))
     '(INST-inv)))

(in-theory (disable INST-inv-opener))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  MT and MA relations
;    Invariants that every instructions should satisfy
;    Relations between Exceptions
;    Exceptions and stages
;    MT-init-ISA
;    MT-DQ-len 
;    Lemmas about inst-specultv?
;    Lemmas about INST-exintr?
;    Lemmas about INST-word
;    Miscellaneous lemmas about INST-pre-ISA and INST-post-ISA.
;    Relations between ISA predicate and INST predicates   
;    Lemmas about subtraces and trace predicates.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate nil
(local
(defthm INST-inv-if-member
    (implies (and (trace-INST-inv trc MA)
		  (member-equal i trc))
	     (INST-inv i MA))))

(local
(defthm INST-inv-if-MT-INST-inv
    (implies (and (MT-INST-inv MT MA)
		  (INST-in i MT))
	     (INST-inv i MA))
  :hints (("Goal" :in-theory (enable MT-INST-inv INST-in)))))

;; Every instruction in a MAETT should satisfy INST-inv.
(defthm INST-inv-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT))
	     (INST-inv i MA))
  :hints (("Goal" :in-theory (enable inv))))
)

(encapsulate nil
(local
(defthm consistent-RS-entry-p-if-INST-in-help
    (implies (and (trace-consistent-RS-p trace MT MA)
		  (member-equal i trace))
	     (consistent-RS-entry-p i MT MA))
  :rule-classes nil))

; consistent-RS-entry-p is true for any instruction i in MT.
(defthm consistent-RS-entry-p-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT))
	     (consistent-RS-entry-p i MT MA))
  :hints (("goal" :use (:instance consistent-RS-entry-p-if-INST-in-help
				  (trace (MT-trace MT)))
		  :in-theory (enable inv consistent-RS-p
				     INST-in)))
  :rule-classes nil)
)

;;;;;; Relations between Exceptions
(deflabel begin-exception-relations)
(defthm INST-excpt-detected-p-if-INST-fetch-error-detected-p
    (implies (INST-fetch-error-detected-p i)
	     (INST-excpt-detected-p i))
  :hints (("Goal" :in-theory (enable INST-excpt-detected-p)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (not (INST-excpt-detected-p i))
		      (not (INST-fetch-error-detected-p i))))))

(defthm INST-excpt-detected-p-if-INST-decode-error-detected-p
    (implies (INST-decode-error-detected-p i)
	     (INST-excpt-detected-p i))
  :hints (("Goal" :in-theory (enable INST-excpt-detected-p)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (not (INST-excpt-detected-p i))
		      (not (INST-decode-error-detected-p i))))))

(defthm INST-excpt-detected-p-if-INST-data-accs-error-detected-p
    (implies (INST-data-accs-error-detected-p i)
	     (INST-excpt-detected-p i))
  :hints (("Goal" :in-theory (enable INST-excpt-detected-p)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (not (INST-excpt-detected-p i))
		      (not (INST-data-accs-error-detected-p i))))))

(defthm INST-data-accs-error-detected-p-if-INST-store-accs-error-detected-p
    (implies (INST-store-accs-error-detected-p i)
	     (INST-data-accs-error-detected-p i))
  :hints (("Goal" :in-theory (enable INST-data-accs-error-detected-p)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (not (INST-data-accs-error-detected-p i))
		      (not (INST-store-accs-error-detected-p i))))))

(defthm INST-data-accs-error-detected-p-if-INST-load-accs-error-detected-p
    (implies (INST-load-accs-error-detected-p i)
	     (INST-data-accs-error-detected-p i))
  :hints (("Goal" :in-theory (enable INST-data-accs-error-detected-p)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (not (INST-data-accs-error-detected-p i))
		      (not (INST-load-accs-error-detected-p i))))))

(defthm INST-data-accs-error-fetch-error-exclusive
    (implies (INST-data-accs-error-detected-p i)
	     (not (INST-fetch-error-detected-p i)))
  :hints (("Goal" :in-theory (enable INST-function-def))))

(defthm INST-decode-error-fetch-error-exclusive
    (implies (INST-decode-error-detected-p i)
	     (not (INST-fetch-error-detected-p i)))
  :hints (("Goal" :in-theory (enable INST-function-def))))

(defthm INST-data-accs-error-decode-error-exclusive
    (implies (INST-data-accs-error-detected-p i)
	     (not (INST-decode-error-detected-p i)))
  :hints (("Goal" :in-theory (enable INST-function-def))))

(defthm INST-fetch-error-decode-error-exclusive
    (implies (INST-fetch-error-detected-p i)
	     (not (INST-decode-error-detected-p i)))
  :hints (("Goal" :in-theory (enable INST-function-def))))

(defthm INST-decode-error-data-accs-error-exclusive
    (implies (INST-decode-error-detected-p i)
	     (not (INST-data-accs-error-detected-p i)))
  :hints (("Goal" :in-theory (enable INST-function-def))))

(defthm INST-fetch-error-data-accs-error-exclusive
    (implies (INST-fetch-error-detected-p i)
	     (not (INST-data-accs-error-detected-p i)))
  :hints (("Goal" :in-theory (enable INST-function-def))))

(deflabel end-exception-relations)
(deftheory exception-relations
    (set-difference-theories (universal-theory 'end-exception-relations)
			     (universal-theory 'begin-exception-relations)))
(in-theory (disable exception-relations))

;;;;; Exceptions and stages
;; Instructions with a fetch error or a decode error cannot be in the
;; execution stage.
(encapsulate nil
(local
(defthm not-fetch-error-detected-if-execute-stg-help
    (implies (and (MA-state-p MA)
		  (INST-inv i MA)
		  (INST-p i) 
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (execute-stg-p (INST-stg i)))
	     (not (INST-fetch-error-detected-p i)))
  :hints (("Goal" :in-theory (enable inst-inv-def exception-relations)))))

(defthm not-fetch-error-detected-if-execute-stg
    (implies (and (inv MT MA)
		  (execute-stg-p (INST-stg i))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (INST-p i))
	     (not (INST-fetch-error-detected-p i))))
)

(encapsulate nil
(local
(defthm not-decode-error-detected-if-execute-stg-help
    (implies (and (MA-state-p MA)
		  (INST-inv i MA)
		  (INST-p i)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (execute-stg-p (INST-stg i)))
	     (not (INST-decode-error-detected-p i)))
  :hints (("Goal" :in-theory (enable inst-inv-def exception-relations)))))

(defthm not-decode-error-detected-if-execute-stg
    (implies (and (inv MT MA)
		  (execute-stg-p (INST-stg i))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (not (INST-decode-error-detected-p i))))
)

;;;;; Other exception related lemmas
(defthm INST-fetch-error-step-INST
    (equal (INST-fetch-error? (step-INST i MT MA sigs))
	   (INST-fetch-error? i))
  :hints (("Goal" :in-theory (enable INST-fetch-error?))))

(defthm INST-decode-error-step-INST
    (equal (INST-decode-error? (step-INST i MT MA sigs))
	   (INST-decode-error? i))
  :hints (("Goal" :in-theory (enable INST-decode-error?))))

(defthm INST-load-error-step-INST
    (equal (INST-load-error? (step-INST i MT MA sigs))
	   (INST-load-error? i))
  :hints (("Goal" :in-theory (enable INST-load-error?))))

(defthm INST-store-error-step-INST
    (equal (INST-store-error? (step-INST i MT MA sigs))
	   (INST-store-error? i))
  :hints (("Goal" :in-theory (enable INST-store-error?))))

(defthm INST-data-access-error-step-INST
    (equal (INST-data-access-error? (step-INST i MT MA sigs))
	   (INST-data-access-error? i))
  :hints (("Goal" :in-theory (enable INST-data-access-error?))))

(defthm INST-fetch-error-detected-p-iff-INST-fetch-error?
    (iff (INST-fetch-error-detected-p i)
	 (b1p (INST-fetch-error? i)))
  :hints (("Goal" :in-theory (enable INST-fetch-error-detected-p
				     INST-fetch-error?)))
  :rule-classes
  ((:rewrite :corollary
	     (implies (b1p (INST-fetch-error? i))
		      (INST-fetch-error-detected-p i)))
   (:rewrite :corollary
	     (implies (not (b1p (INST-fetch-error? i)))
		      (not (INST-fetch-error-detected-p i))))))

(defthm INST-decode-error-detected-p-iff-INST-decode-error?
    (implies (and (b1p (INST-decode-error? i))
		  (not (b1p (INST-fetch-error? i)))
		  (not (IFU-stg-p (INST-stg i))))
	     (INST-decode-error-detected-p i))
  :hints (("goal" :in-theory (enable INST-decode-error-detected-p
				     INST-decode-error? lift-b-ops
				     INST-opcode
				     decode-illegal-inst? INST-su))))

(defthm not-INST-decode-error-detected-p-iff-not-INST-decode-error?
    (implies (not (b1p (INST-decode-error? i)))
	     (not (INST-decode-error-detected-p i)))
  :hints (("goal" :in-theory (enable INST-decode-error-detected-p
				     INST-decode-error? lift-b-ops
				     INST-opcode
				     decode-illegal-inst? INST-su))))

(defthm not-INST-decode-error-detected-p-if-IFU-stg
    (implies (IFU-stg-p (INST-stg i))
	     (not (INST-decode-error-detected-p i)))
  :hints (("goal" :in-theory (enable INST-decode-error-detected-p))))

(defthm not-INST-fetch-error-if-execute-stg
    (implies (and (inv MT MA)
		  (execute-stg-p (INST-stg i))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (INST-p i))
	     (equal (INST-fetch-error? i) 0))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter
				   exception-relations)
				  (not-fetch-error-detected-if-execute-stg))
		  :use (:instance not-fetch-error-detected-if-execute-stg))))

(defthm not-INST-decode-error-if-execute-stg
    (implies (and (inv MT MA)
		  (execute-stg-p (INST-stg i))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (INST-p i))
	     (equal (INST-decode-error? i) 0))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter
				   exception-relations)
				  (not-decode-error-detected-if-execute-stg))
		  :use (:instance not-decode-error-detected-if-execute-stg))))

(encapsulate nil
(local
(defthm not-fetch-error-detected-if-wbuf-stg-help
    (implies (and (INST-p i) (MA-state-p MA)
		  (MAETT-p MT)
		  (INST-inv i MA)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (wbuf-stg-p (INST-stg i)))
	     (not (INST-fetch-error-detected-p i)))
  :hints (("Goal" :in-theory (enable inst-inv-def wbuf-stg-p
				     INST-excpt? exception-relations
				     lift-b-ops)))))

(defthm not-fetch-error-detected-if-wbuf-stg
    (implies (and (inv MT MA)
		  (wbuf-stg-p (INST-stg i))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (INST-p i))
	     (not (INST-fetch-error-detected-p i))))
)

(encapsulate nil
(local
(defthm not-decode-error-detected-if-wbuf-stg-help
    (implies (and (INST-p i) (MA-state-p MA)
		  (MAETT-p MT)
		  (INST-inv i MA)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (wbuf-stg-p (INST-stg i)))
	     (not (INST-decode-error-detected-p i)))
  :hints (("Goal" :in-theory (enable inst-inv-def wbuf-stg-p
				     INST-excpt? lift-b-ops
				     exception-relations)))))

(defthm not-decode-error-detected-if-wbuf-stg
    (implies (and (inv MT MA)
		  (wbuf-stg-p (INST-stg i))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (not (INST-decode-error-detected-p i))))
)

(defthm not-INST-load-accs-error-detected-p-if-not-dispatched
    (implies (or (IFU-stg-p (INST-stg i))
		 (DQ-stg-p (INST-stg i)))
	     (not (INST-load-accs-error-detected-p i)))
  :hints (("goal" :in-theory (enable INST-load-accs-error-detected-p))))

(defthm not-INST-store-accs-error-detected-p-if-not-dispatched
    (implies (or (IFU-stg-p (INST-stg i))
		 (DQ-stg-p (INST-stg i)))
	     (not (INST-store-accs-error-detected-p i)))
  :hints (("goal" :in-theory (enable INST-store-accs-error-detected-p))))

(defthm not-INST-data-accs-error-detected-p-if-not-dispatched
    (implies (or (IFU-stg-p (INST-stg i))
		 (DQ-stg-p (INST-stg i)))
	     (not (INST-data-accs-error-detected-p i)))
  :hints (("goal" :in-theory (enable INST-data-accs-error-detected-p))))

(defthm not-INST-data-accs-error-detected-if-INST-IU
    (implies (and (INST-p i) (b1p (INST-IU? i)))
	     (not (INST-data-accs-error-detected-p i)))
  :hints (("goal" :in-theory (enable INST-data-accs-error-detected-p
				     INST-load-accs-error-detected-p
				     INST-store-accs-error-detected-p
				     INST-cntlv
				     INST-IU?))))

(defthm not-INST-data-accs-error-detected-if-INST-MU
    (implies (and (INST-p i) (b1p (INST-MU? i)))
	     (not (INST-data-accs-error-detected-p i)))
  :hints (("goal" :in-theory (enable INST-data-accs-error-detected-p
				     INST-load-accs-error-detected-p
				     INST-store-accs-error-detected-p
				     INST-cntlv
				     INST-MU?))))

(defthm not-INST-data-accs-error-detected-if-INST-BU
    (implies (and (INST-p i) (b1p (INST-BU? i)))
	     (not (INST-data-accs-error-detected-p i)))
  :hints (("goal" :in-theory (enable INST-data-accs-error-detected-p
				     INST-load-accs-error-detected-p
				     INST-store-accs-error-detected-p
				     INST-cntlv
				     INST-BU?))))

(defthm INST-load-accs-error-detected-p-if-complete
    (implies (and (b1p (INST-load-error? i))
		  (not (b1p (INST-fetch-error? i)))
		  (not (b1p (INST-decode-error? i)))		  
		  (or (complete-stg-p (INST-stg i))
		      (commit-stg-p (INST-stg i))
		      (retire-stg-p (INST-stg i))))
	     (INST-load-accs-error-detected-p i))
  :hints (("goal" :in-theory (enable INST-load-accs-error-detected-p
				     INST-load-error?
				     lift-b-ops inst-load-addr
				     INST-opcode INST-im INST-ra INST-rb))))

(defthm INST-store-accs-error-detected-p-if-complete
    (implies (and (b1p (INST-store-error? i))
		  (not (b1p (INST-fetch-error? i)))
		  (not (b1p (INST-decode-error? i)))		  
		  (or (complete-stg-p (INST-stg i))
		      (commit-stg-p (INST-stg i))
		      (retire-stg-p (INST-stg i))))
	     (INST-store-accs-error-detected-p i))
  :hints (("goal" :in-theory (enable INST-store-accs-error-detected-p
				     INST-store-error?
				     lift-b-ops inst-store-addr
				     INST-opcode INST-im INST-ra INST-rb))))

(defthm INST-data-accs-error-detected-p-if-complete
    (implies (and (b1p (INST-data-access-error? i))
		  (not (b1p (INST-fetch-error? i)))
		  (not (b1p (INST-decode-error? i)))		  
		  (or (complete-stg-p (INST-stg i))
		      (commit-stg-p (INST-stg i))
		      (retire-stg-p (INST-stg i))))
	     (INST-data-accs-error-detected-p i))
  :hints (("goal" :in-theory (enable INST-data-accs-error-detected-p
				     INST-data-access-error? lift-b-ops))))

(defthm not-INST-load-error-detected-p-if-not-INST-load-error
    (implies (not (b1p (INST-load-error? i)))
	     (not (INST-load-accs-error-detected-p i)))
  :hints (("goal" :in-theory (enable INST-load-accs-error-detected-p
				     lift-b-ops inst-load-error?
				     INST-opcode INST-load-addr
				     INST-function-def))))

(defthm not-INST-store-error-detected-p-if-not-INST-store-error
    (implies (not (b1p (INST-store-error? i)))
	     (not (INST-store-accs-error-detected-p i)))
  :hints (("goal" :in-theory (enable INST-store-accs-error-detected-p
				     lift-b-ops inst-store-error?
				     INST-opcode INST-store-addr
				     INST-function-def))))

(defthm not-INST-data-accs-error-detected-p-if-not-INST-decode-error
    (implies (not (b1p (INST-data-access-error? i)))
	     (not (INST-data-accs-error-detected-p i)))
  :hints (("goal" :in-theory (enable INST-data-accs-error-detected-p
				     lift-b-ops inst-data-access-error?))))

(defthm INST-excpt-detected-p-if-INST-excpt-completed
    (implies (and (b1p (INST-excpt? I))
		  (or (complete-stg-p (INST-stg i))
		      (commit-stg-p (INST-stg i))
		      (retire-stg-p (INST-stg i))))
	     (INST-excpt-detected-p i))
  :hints (("goal" :in-theory (enable INST-excpt? INST-excpt-detected-p
				     lift-b-ops)
		  :cases ((b1p (INST-fetch-error? i))))
	  ("subgoal 2" :cases ((b1p (INST-decode-error? i))))))

(defthm not-INST-excpt-detected-if-not-INST-excpt
    (implies (and (INST-p i) (not (b1p (INST-excpt? i))))
	     (not (INST-excpt-detected-p i)))
  :hints (("goal" :in-theory (enable INST-excpt? INST-excpt-detected-p
				     lift-b-ops))))

(defthm INST-fetch-error-detected-p-step-inst
    (equal (INST-fetch-error-detected-p (step-INST i MT MA sigs))
	   (INST-fetch-error-detected-p i))
  :hints (("goal" :in-theory (enable INST-fetch-error-detected-p))))

(defthm INST-data-decode-error-detected-step-INST-not-IFU
    (implies (not (IFU-stg-p (INST-stg i)))
	     (equal (INST-decode-error-detected-p (step-INST i MT MA sigs))
		    (INST-decode-error-detected-p i)))
  :hints (("goal" :in-theory (enable INST-decode-error-detected-p)
		  :use (:instance (:instance INST-is-at-one-of-the-stages)))))

(defthm INST-store-accs-error-detected-p-step-inst
    (implies (INST-store-accs-error-detected-p i)
	     (INST-store-accs-error-detected-p (step-INST i MT MA sigs)))
  :hints (("Goal" :in-theory (enable INST-store-accs-error-detected-p))))

(defthm INST-load-accs-error-detected-p-step-inst
    (implies (INST-load-accs-error-detected-p i)
	     (INST-load-accs-error-detected-p (step-INST i MT MA sigs)))
  :hints (("Goal" :in-theory (enable INST-load-accs-error-detected-p))))

(defthm INST-data-access-error-detected-p-step-inst
    (implies (INST-data-accs-error-detected-p i)
	     (INST-data-accs-error-detected-p (step-INST i MT MA sigs)))
  :hints (("Goal" :in-theory (enable INST-data-accs-error-detected-p))))

(defthm INST-excpt-detected-p-step-inst-if-not-advance
    (implies (equal (INST-stg (step-inst i MT MA sigs)) (INST-stg i))
	     (equal (INST-excpt-detected-p (step-INST i MT MA sigs))
		    (INST-excpt-detected-p i)))
  :hints (("goal" :in-theory (enable INST-excpt-detected-p
				     INST-data-accs-error-detected-p
				     INST-store-accs-error-detected-p
				     INST-load-accs-error-detected-p
				     INST-decode-error-detected-p
				     INST-fetch-error-detected-p))))

(defthm INST-excpt-step-INST
    (equal (INST-excpt? (step-INST i MT MA sigs)) (INST-excpt? i))
  :hints (("Goal" :in-theory (enable MT-def))))

(defthm INST-excpt-flags-step-inst-if-excpt-detected
    (implies (and (INST-p i) (inst-excpt-detected-p i))
	     (equal (INST-excpt-flags (step-INST i MT MA sigs))
		    (INST-excpt-flags i)))
  :hints (("Goal" :in-theory (e/d (INST-excpt-flags
				   INST-excpt-detected-p)
				  (INST-is-at-one-of-the-stages))
		  :use (:instance INST-is-at-one-of-the-stages))))

(defthm INST-excpt-flags-step-DQ-inst
    (implies (and (DQ-stg-p (INST-stg i))
		  (DQ-stg-p (INST-stg (step-INST i MT MA sigs))))
	     (equal (INST-excpt-flags (step-INST i MT MA sigs))
		    (INST-excpt-flags i)))
  :hints (("Goal" :in-theory (enable INST-excpt-flags))))

(defthm INST-excpt-flags-step-INST-if-complete
    (implies (and (inst-p i) (INST-in i MT)
		  (complete-stg-p (INST-stg i)))
	     (equal (INST-excpt-flags (step-INST i MT MA sigs))
		    (INST-excpt-flags i)))
  :Hints (("goal" :in-theory (enable INST-excpt-flags
				     INST-data-accs-error-detected-p
				     INST-load-accs-error-detected-p
				     INST-store-accs-error-detected-p))))

; INST-context-sync? does not change after step-INST.
(defthm inst-context-sync-step-INST
    (equal (inst-context-sync? (step-INST i MT MA sigs))
	   (inst-context-sync? i))
  :hints (("goal" :in-theory (enable inst-context-sync? lift-b-ops))))

(defthm INST-wrong-branch-step-INST-if-IFU
    (implies (and (INST-p i) (MA-state-p MA) (MAETT-p MT)
		  (MA-input-p sigs) (IFU-stg-p (INST-stg i))
		  (or (not (b1p (IFU-branch-predict? (MA-IFU MA) MA sigs)))
		      (b1p (DQ-full? (MA-DQ MA)))))
	     (equal (INST-wrong-branch? (step-INST i MT MA sigs))
		    (INST-wrong-branch? i)))
  :Hints (("goal" :in-theory (enable INST-wrong-branch? 
				     SIMPLIFY-BIT-FUNCTIONS-2
				     lift-b-ops))))

(defthm inst-wrong-branch-step-INST-if-not-IFU
    (implies (and (MA-state-p MA) (MAETT-p MT) (INST-p i)
		  (MA-input-p sigs)
		  (not (IFU-stg-p (INST-stg i))))
	     (equal (inst-wrong-branch? (step-INST i MT MA sigs))
		    (inst-wrong-branch? i)))
  :hints (("goal" :in-theory (e/d (inst-wrong-branch?
				   lift-b-ops
				   equal-b1p-converter) ()))))

;;;;;; MT-init-ISA of a MAETT is the pre-ISA of the first
;;;;;; instruction in the MAETT. 
(defthm INST-pre-ISA-car-MT-trace
    (implies (and (weak-inv MT)
		  (MAETT-p MT)
		  (consp (MT-trace MT)))
	     (equal (INST-pre-ISA (car (MT-trace MT)))
		    (MT-init-ISA MT)))
  :hints (("goal" :in-theory (enable weak-inv inv
				     ISA-step-chain-p))))

(encapsulate nil
(local
 (defthm not-inst-specultv-INST-in-if-committed-help
     (implies (and (trace-no-specultv-commit-p trace)
		   (member-equal i trace)
		   (INST-listp trace)
		   (INST-p i)
		   (committed-p i))
	      (equal (inst-specultv? i) 0))
   :hints (("goal" :in-theory (enable zbp committed-p)))))

;;;;;; Lemmas about MT-DQ-len
(deflabel begin-MT-DQ-len-lemmas)
(defthm mt-dq-len-0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))))
	     (equal (MT-DQ-len MT) 0))
  :hints (("goal" :in-theory (enable inv misc-inv
				     correct-entries-in-dq-p))))

(defthm mt-dq-len-1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))
		  (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))))
	     (equal (MT-DQ-len MT) 1))
  :hints (("goal" :in-theory (enable inv misc-inv
				     correct-entries-in-dq-p))))

(defthm mt-dq-len-2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))
		  (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))))
	     (equal (MT-DQ-len MT) 2))
  :hints (("goal" :in-theory (enable inv misc-inv
				     correct-entries-in-dq-p))))

(defthm mt-dq-len-3
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))
		  (not (b1p (DE-valid? (DQ-DE3 (MA-DQ MA))))))
	     (equal (MT-DQ-len MT) 3))
  :hints (("goal" :in-theory (enable inv misc-inv
				     correct-entries-in-dq-p))))

(defthm mt-dq-len-4
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (DE-valid? (DQ-DE3 (MA-DQ MA)))))
	     (equal (MT-DQ-len MT) 4))
  :hints (("goal" :in-theory (enable inv misc-inv
				     correct-entries-in-dq-p))))

(defthm mt-dq-len-ge-1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
	     (>= (MT-DQ-len MT) 1))
  :hints (("goal" :in-theory (enable inv misc-inv
				     correct-entries-in-dq-p)))
  :rule-classes :linear)

(defthm mt-dq-len-ge-2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (DE-valid? (DQ-DE1 (MA-DQ MA)))))
	     (>= (MT-DQ-len MT) 2))
  :hints (("goal" :in-theory (enable inv misc-inv
				     correct-entries-in-dq-p)))
  :rule-classes :linear)

(defthm mt-dq-len-lt-2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))))
	     (< (MT-DQ-len MT) 2))
  :hints (("goal" :in-theory (enable inv misc-inv
				     correct-entries-in-dq-p)))
  :rule-classes :linear)

(defthm mt-dq-len-ge-3
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (DE-valid? (DQ-DE2 (MA-DQ MA)))))
	     (>= (MT-DQ-len MT) 3))
  :hints (("goal" :in-theory (enable inv misc-inv
				     correct-entries-in-dq-p)))
  :rule-classes :linear)

(defthm mt-dq-len-lt-3
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))))
	     (< (MT-DQ-len MT) 3))
  :hints (("goal" :in-theory (enable inv misc-inv
				     correct-entries-in-dq-p)))
  :rule-classes :linear)

(defthm mt-dq-len-lt-4
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (DE-valid? (DQ-DE3 (MA-DQ MA))))))
	     (< (MT-DQ-len MT) 4))
  :hints (("goal" :in-theory (enable inv misc-inv
				     correct-entries-in-dq-p)))
  :rule-classes :linear)
(deflabel end-MT-DQ-len-lemmas)
(deftheory MT-DQ-len-lemmas
    (set-difference-theories (universal-theory 'end-MT-DQ-len-lemmas)
			     (universal-theory 'begin-MT-DQ-len-lemmas)))
(defthm MT-DQ-len-le-4
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (<= (MT-DQ-len MT) 4))
  :hints (("Goal" :in-theory (enable inv misc-inv)))
  :rule-classes :linear)

;;;;;; INST-specultv? is 0 if the instruction is committed.
(defthm not-inst-specultv-INST-in-if-committed
    (implies (and (committed-p i)
		  (inv MT MA)
		  (INST-in i MT)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (INST-p i))
	     (equal (inst-specultv? i) 0))
  :hints (("Goal" :in-theory (enable weak-inv inv
				     NO-SPECULTV-COMMIT-P
				     INST-in))))
)
(in-theory (disable not-inst-specultv-INST-in-if-committed))

(encapsulate nil
(local
(defthm INST-exintr-INST-in-if-not-retired-help
    (implies (and (trace-correct-exintr-p trace)
		  (INST-listp trace)
		  (INST-p i)
		  (member-equal i trace)
		  (not (retire-stg-p (INST-stg i))))
	     (equal (INST-exintr? i) 0))
  :hints (("Goal" :in-theory (enable b1p zbp)))))

; INST-exintr? flag is off for any instruction that are not retired.
(defthm INST-exintr-INST-in-if-not-retired
    (implies (and (inv MT MA)
		  (not (retire-stg-p (INST-stg i)))
		  (INST-in i MT)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (INST-p i))
	     (equal (INST-exintr? i) 0))
  :hints (("Goal" :in-theory (enable weak-inv
				     inv
				     INST-in correct-exintr-p))))
)
(in-theory (disable INST-exintr-INST-in-if-not-retired))

;;;;;  Lemmas about INST-word
(defthm read-mem-Inst-word
    (equal (READ-MEM (ISA-PC (INST-PRE-ISA i))
		     (ISA-MEM (INST-PRE-ISA i)))
	   (Inst-word i))
  :hints (("Goal" :in-theory (enable INST-word INST-in INST-pc INST-mem))))

;;;;;; Miscellaneous lemmas about INST-pre-ISA and INST-post-ISA.
;
; Relations between INST-post-ISA and INST-pre-ISA can be given
; by ISA-step.
; Note  We are not sure this rule is more useful than harmful.
(encapsulate nil
(local
 (defthm INST-post-ISA-INST-in-help
     (implies (and (ISA-chained-trace-p trace pre)
		   (member-equal i trace)
		   (INST-listp trace)
		   (INST-p i))
	      (equal (INST-post-ISA i)
		     (ISA-step (INST-pre-ISA i)
			       (ISA-input (INST-exintr? i)))))))

(defthm INST-post-ISA-INST-in
    (implies (and (weak-inv MT)
		  (INST-in i MT)
		  (MAETT-p MT)
		  (INST-p i))
	     (equal (INST-post-ISA i)
		    (ISA-step (INST-pre-ISA i)
			      (ISA-input (INST-exintr? i)))))
  :hints (("Goal" :in-theory (enable weak-inv inv
				     ISA-step-chain-p
				     INST-in ISA-chained-trace-p))))
)

(defthm INST-post-ISA-car-subtrace
    (implies (and (weak-inv MT)
		  (subtrace-p trace MT)
		  (MAETT-p MT)
		  (consp trace)
		  (INST-listp trace))
	     (equal (INST-post-ISA (car trace))
		    (ISA-step (INST-pre-ISA (car trace))
			      (ISA-input (INST-exintr? (car trace)))))))
(encapsulate nil
(local
(defthm INST-pre-ISA-cadr-subtrace-help
    (implies (and (ISA-chained-trace-p trace pre)
		  (tail-p sub trace)
		  (INST-listp sub)
		  (INST-listp trace)
		  (consp sub)
		  (consp (cdr sub)))
	     (equal (INST-pre-ISA (cadr sub))
		    (ISA-step (INST-pre-ISA (car sub))
			      (ISA-input (INST-exintr? (car sub))))))))

; The relations between INST-pre-ISA's of an instruction and its 
; immediately following instruction can be specified by ISA-step.
(defthm INST-pre-ISA-cadr-subtrace
    (implies (and (weak-inv MT)
		  (subtrace-p trace MT)
		  (MAETT-p MT)
		  (INST-listp trace)
		  (consp trace)
		  (consp (cdr trace)))
	     (equal (INST-pre-ISA (cadr trace))
		    (ISA-step (INST-pre-ISA (car trace))
			      (ISA-input (INST-exintr? (car trace))))))
  :hints (("Goal" :in-theory (enable weak-inv inv
				     ISA-step-chain-p subtrace-p))))
)

;;;;; Relations between ISA predicate and INST predicates
(defthm ISA-store-inst-p-INST-pre-ISA
    (implies (and (weak-inv MT)
		  (INST-p i)
		  (INST-in i MT))
	     (iff (ISA-store-inst-p (INST-pre-ISA i))
		  (b1p (INST-store? i))))
  :hints (("goal" :in-theory (enable INST-function-def lift-b-ops
				     ISA-store-inst-p
				     store-inst-p
				     decode rdb logbit*))))
					 
(defthm ISA-store-addr-INST-pre-ISA
    (implies (and (weak-inv MT)
		  (INST-p i)
		  (INST-in i MT))
	     (equal (ISA-store-addr (INST-pre-ISA i))
		    (INST-store-addr i)))
  :hints (("goal" :in-theory (enable INST-function-def lift-b-ops
				     ISA-store-addr
				     store-inst-p
				     decode rdb logbit*))))
(defthm ISA-excpt-p-INST-pre-ISA
    (implies (and (weak-inv MT)
		  (INST-p i)
		  (INST-in i MT))
	     (iff (ISA-excpt-p (INST-pre-ISA i))
		  (b1p (INST-excpt? i))))
  :hints (("goal" :in-theory (enable INST-function-def lift-b-ops
				     ISA-excpt-p
				     decode rdb logbit*
				     INST-function-def
				     ISA-functions
				     MA-def))))

(encapsulate nil
(local
(defthm no-tag-conflict-at-if-no-tag-conflict-under
    (implies (and (no-tag-conflict-under upper MT MA)
		  (rob-index-p rix)
		  (integerp upper)
		  (< rix upper))
	     (no-tag-conflict-at rix MT MA))))

(local
(defthm no-tag-conflict-at-if-no-tag-conflict
    (implies (and (no-tag-conflict MT MA)
		  (rob-index-p rix))
	     (no-tag-conflict-at rix MT MA))
  :hints (("Goal" :in-theory (enable no-tag-conflict rob-index-p)))))

;  ROB conflict should not appear at any ROB index.
(defthm no-tag-conflict-at-all-rix
    (implies (and (inv MT MA)
		  (rob-index-p rix))
	     (no-tag-conflict-at rix MT MA))
  :hints (("Goal" :in-theory (enable weak-inv inv))))
) ;encapsulate

;;;;;; Lemmas about subtraces and trace predicates.
(encapsulate nil
(local
(defthm trace-final-ISA-subtrace-help
    (implies (and (consp trace1) (tail-p trace1 trace2))
	     (equal (equal (trace-final-ISA trace1 pre1)
			   (trace-final-ISA trace2 pre2))
		    t))))

(defthm trace-final-ISA-subtrace
    (implies (and (consp trace) (subtrace-p trace MT))
	     (equal (trace-final-ISA trace pre)
		    (MT-final-ISA MT)))
  :hints (("Goal" :in-theory (enable MT-final-ISA subtrace-p)))
  :rule-classes nil)
)

(encapsulate nil
(local
(defthm trace-specultv-subtrace-help
    (implies (and (tail-p sub trace)
		  (not (b1p (trace-specultv? trace))))
	     (equal (trace-specultv? sub) 0))
  :hints (("goal" :in-theory (enable b1p zbp)))))

(defthm trace-specultv-subtrace
    (implies (and (inv MT MA)
		  (subtrace-p sub MT)
		  (not (b1p (MT-specultv? MT))))
	     (equal (trace-specultv? sub) 0))
  :hints (("Goal" :in-theory (enable weak-inv inv
				     subtrace-p MT-specultv?))))
)

(encapsulate nil
(local
(defthm ISA-chained-trace-p-subtrace-help
    (implies (and (tail-p sub trace)
		  (INST-listp trace)
		  (INST-listp sub)
		  (ISA-chained-trace-p trace (INST-pre-ISA (car trace)))
		  (consp sub))
	     (ISA-chained-trace-p sub (INST-pre-ISA (car sub))))
  :hints ((when-found (ISA-CHAINED-TRACE-P (CDR TRACE)
					   (INST-POST-ISA (CAR TRACE)))
		      (:expand (ISA-CHAINED-TRACE-P (CDR TRACE)
					   (INST-POST-ISA (CAR TRACE))))))))

(defthm ISA-chained-trace-p-subtrace
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (INST-listp trace)
		  (consp trace)
		  (subtrace-p trace MT))
	     (ISA-chained-trace-p trace (INST-pre-ISA (car trace))))
  :hints (("Goal" :in-theory (e/d (subtrace-p inv weak-inv
					      ISA-step-chain-p))
		  :cases ((consp (MT-trace MT))))))
)

(defthm ISA-chained-trace-p-INST-pre-ISA-of-car
    (implies (ISA-chained-trace-p trace whatever)
	     (ISA-chained-trace-p trace (INST-pre-ISA (car trace)))))

(encapsulate nil
(local	     
(defthm correct-exintr-p-subtrace-help
    (implies (and (trace-correct-exintr-p trace)
		  (tail-p sub trace))
	     (trace-correct-exintr-p sub)))
)
(defthm correct-exintr-p-subtrace
    (implies (and (inv MT MA)
		  (subtrace-p sub MT))
	     (trace-correct-exintr-p sub))
  :hints (("Goal" :in-theory (enable inv
				     weak-inv correct-exintr-p subtrace-p))))
)

(encapsulate nil
(local 
(defthm no-specultv-commit-p-subtrace-help
    (implies (and (trace-no-specultv-commit-p trace)
		  (tail-p sub trace))
	     (trace-no-specultv-commit-p sub))))

(defthm no-specultv-commit-p-subtrace
    (implies (and (inv MT MA)
		  (subtrace-p sub MT))
	     (trace-no-specultv-commit-p sub))
  :hints (("Goal" :in-theory (enable weak-inv inv
				     no-specultv-commit-p
				     subtrace-p))))
)

(defthm trace-INST-inv-subtrace
    (implies (and (inv MT MA)
		  (subtrace-p sub MT))
	     (trace-INST-inv sub MA)))

(encapsulate nil
(local
(defthm in-order-trace-p-subtrace-help
    (implies (and (in-order-trace-p trace)
		  (tail-p sub trace))
	     (in-order-trace-p sub))))

(defthm in-order-trace-p-subtrace
    (implies (and (inv MT MA)
		  (subtrace-p sub MT))
	     (in-order-trace-p sub))
  :hints (("goal" :in-theory (enable weak-inv inv
				     in-order-dispatch-commit-p
				     subtrace-p))))
)

(encapsulate nil
(local
(defthm in-order-trace-p-subtrace-help
    (implies (and (in-order-trace-p trace)
		  (tail-p sub trace))
	     (in-order-trace-p sub))))

(defthm no-stage-conflict-subtrace
    (implies (and (inv MT MA)
		  (subtrace-p sub MT))
	     (in-order-trace-p sub))
  :hints (("goal" :in-theory (enable weak-inv inv
				     in-order-dispatch-commit-p
				     subtrace-p))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Lemmas related to INST-at-stg
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; INST-at-stg is INST-p
(encapsulate nil
(local
(defthm INST-p-INST-at-stg-in-trace
    (implies (and (uniq-INST-at-stg-in-trace stg trace)
		  (INST-listp trace))
	     (INST-p (INST-at-stg-in-trace stg trace)))))

(defthm INST-p-INST-at-stg
    (implies (and (uniq-INST-at-stg stg MT)
		  (MAETT-p MT))
	     (INST-p (INST-at-stg stg MT)))
  :hints (("Goal" :in-theory (enable uniq-INST-at-stg INST-at-stg))))
)

(encapsulate nil
(local
(defthm INST-in-INST-at-stg-help
    (implies (uniq-INST-at-stg-in-trace stg trace)
	     (member-equal (INST-at-stg-in-trace stg trace) trace))))

;;; INST-at-stg belongs to a MAETT.
(defthm INST-in-INST-at-stg
    (implies (uniq-INST-at-stg stg MT)
	     (INST-in (INST-at-stg stg MT) MT))
  :hints (("goal" :in-theory (enable INST-in INST-at-stg uniq-INST-at-stg))))
)

(defthm uniq-INST-at-IFU-if-IFU-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (IFU-valid? (MA-IFU MA))))
	     (uniq-INST-at-stg '(IFU) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-IFU-stg-conflict))))

(encapsulate nil
(local
(defthm INST-p-INST-at-stgs-in-trace
    (implies (and (uniq-INST-at-stgs-in-trace stgs trace)
		  (INST-listp trace))
	     (INST-p (INST-at-stgs-in-trace stgs trace)))))

(defthm INST-p-INST-at-stgs
    (implies (and (uniq-INST-at-stgs stgs MT)
		  (MAETT-p MT))
	     (INST-p (INST-at-stgs stgs MT)))
  :hints (("Goal" :in-theory (enable uniq-INST-at-stgs INST-at-stgs))))
)

(encapsulate nil
(local
(defthm INST-in-INST-at-stgs-help
    (implies (uniq-INST-at-stgs-in-trace stgs trace)
	     (member-equal (INST-at-stgs-in-trace stgs trace) trace))))

;;; INST-at-stgs belongs to a MAETT.
(defthm INST-in-INST-at-stgs
    (implies (uniq-INST-at-stgs stgs MT)
	     (INST-in (INST-at-stgs stgs MT) MT))
  :hints (("goal" :in-theory (enable INST-in INST-at-stgs uniq-INST-at-stgs))))
)

(encapsulate nil
(local
(defthm equal-INST-stg-INST-at-stgs-in-trace
    (implies (and (stage-p stg)
		  (not (member-equal stg stgs)))
	     (not (equal (INST-stg (INST-at-stgs-in-trace stgs trace)) stg)))
  :rule-classes nil))

; The stage of the instruction returned by INST-at-stgs is one of the
; first argument.
(defthm equal-INST-stg-INST-at-stgs
    (implies (and (stage-p stg)
		  (not (member-equal stg stgs)))
	     (not (equal (INST-stg (INST-at-stgs stgs MT)) stg)))
  :hints (("goal" :In-theory (enable INST-at-stgs)
		  :use (:instance equal-INST-stg-INST-at-stgs-in-trace
				  (trace (MT-trace MT))))))
)

(encapsulate nil
(local
(defthm uniq-inst-at-stg-no-inst-at-stg-exclusive-help
    (implies (uniq-inst-at-stg-in-trace rix trace)
	     (not (no-inst-at-stg-in-trace rix trace)))))

(defthm uniq-inst-at-stg-no-inst-at-stg-exclusive
    (implies (uniq-inst-at-stg rix MT)
	     (not (no-inst-at-stg rix MT)))
  :hints (("goal" :in-theory (enable no-inst-at-stg uniq-inst-at-stg)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (no-inst-at-stg rix MT)
		      (not (uniq-inst-at-stg rix MT))))))
)

(encapsulate nil
(local
(defthm no-inst-at-stgs-in-trace-no-inst-at-stg-in-trace-1
    (implies (and (consp stgs)
		  (no-inst-at-stgs-in-trace stgs trace))
	     (no-inst-at-stg-in-trace (car stgs) trace))))

(local
(defthm no-inst-at-stgs-in-trace-no-inst-at-stg-in-trace-2
    (implies (and (consp stgs)
		  (no-inst-at-stgs-in-trace stgs trace))
	     (no-inst-at-stgs-in-trace (cdr stgs) trace))))

(local
(defthm not-uniq-inst-at-stg-in-trace-if-no-inst-at-stg-in-trace
    (implies (and (consp stgs)
		  (no-inst-at-stg-in-trace stg trace))
	     (not (uniq-inst-at-stg-in-trace stg trace)))))

(local
(defthm uniq-inst-at-stgs-in-trace-uniq-inst-at-stg-in-trace
    (implies (and (consp stgs)
		  (not (uniq-inst-at-stg-in-trace (car stgs) trace))
		  (not (uniq-inst-at-stgs-in-trace (cdr stgs) trace)))
	     (not (uniq-inst-at-stgs-in-trace stgs trace)))))

(local
 (defthm uniq-inst-at-stgs-in-trace-endp
     (implies (endp stgs)
	      (not (uniq-inst-at-stgs-in-trace stgs trace)))))

; Relations between uniq-inst-at-stg and uniq-inst-at-stgs.
(defthm uniq-inst-at-stgs*
    (implies (and (consp stgs) (uniq-inst-at-stgs stgs MT))
	     (or (uniq-inst-at-stg (car stgs) MT)
		 (uniq-inst-at-stgs (cdr stgs) MT)))
  :hints (("goal" :in-theory (enable uniq-inst-at-stg uniq-inst-at-stgs)))
  :rule-classes nil)

(local
(defthm inst-at-stgs-inst-at-stg-help
    (implies (uniq-inst-at-stgs-in-trace stgs trace)
	     (equal (inst-at-stgs-in-trace stgs trace)
		    (if (uniq-inst-at-stg-in-trace (car stgs) trace)
			(inst-at-stg-in-trace (car stgs) trace)
			(inst-at-stgs-in-trace (cdr stgs) trace))))))

; Relations between inst-at-stgs and inst-at-stg.
(defthm inst-at-stgs*
    (implies (uniq-inst-at-stgs stgs MT)
	     (equal (inst-at-stgs stgs MT)
		    (if (uniq-inst-at-stg (car stgs) MT)
			(inst-at-stg (car stgs) MT)
			(inst-at-stgs (cdr stgs) MT))))
  :hints (("goal" :in-theory (enable uniq-inst-at-stg uniq-inst-at-stgs
				     inst-at-stg inst-at-stgs))))

(in-theory (disable inst-at-stgs*))

(local
(defthm uniq-inst-at-stgs-singleton-help
    (equal (uniq-inst-at-stgs-in-trace (list stg) trace)
	   (uniq-inst-at-stg-in-trace stg trace))))

; uniq-inst-at-stgs can be reduced to uniq-inst-at-stg if the first 
; argument is a singleton of stages.
(defthm uniq-inst-at-stgs-singleton
    (equal (uniq-inst-at-stgs (list stg) MT)
	   (uniq-inst-at-stg stg MT))
  :hints (("goal" :in-theory (enable uniq-inst-at-stgs uniq-inst-at-stg))))

)    

(encapsulate nil
(local
(defthm no-inst-at-stgs-in-trace-remove-equal
    (implies (no-inst-at-stgs-in-trace stgs trace)
	     (no-inst-at-stgs-in-trace (remove-equal stg stgs) trace))))

(local
(defthm uniq-inst-at-stgs-remove-equal-help-help
    (implies (and (member-equal stg stgs)
		  (not (no-inst-at-stg-in-trace stg trace)))
	     (not (no-inst-at-stgs-in-trace stgs trace)))))

(local
(defthm uniq-inst-at-stgs-remove-equal-help
    (implies (and (uniq-inst-at-stgs-in-trace stgs trace)
		  (not (uniq-inst-at-stg-in-trace stg trace))
		  (member-equal stg stgs))
	     (uniq-inst-at-stgs-in-trace (remove-equal stg stgs) trace))))

(defthm uniq-inst-at-stgs-remove-equal
    (implies (and (uniq-inst-at-stgs stgs MT)
		  (not (uniq-inst-at-stg stg MT))
		  (member-equal stg stgs))
	     (uniq-inst-at-stgs (remove-equal stg stgs) MT))
  :hints (("Goal" :in-theory (enable uniq-inst-at-stgs uniq-inst-at-stg))))
)

(defthm no-INST-at-IFU-if-IFU-invalid
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (IFU-valid? (MA-IFU MA)))))
	     (no-INST-at-stg '(IFU) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-IFU-stg-conflict))))

(defthm IFU-valid-if-IFU-stg-p
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (IFU-stg-p (INST-stg i))
		  (INST-p i) (INST-in i MT))
	     (equal (IFU-valid? (MA-IFU MA)) 1))
  :hints (("goal" :use (:instance INST-INV-IF-INST-IN)
		  :in-theory (e/d (INST-inv-def lift-b-ops
						equal-b1p-converter)
				  (INST-INV-IF-INST-IN)))))

(defthm uniq-inst-at-stg-if-DQ-DE0-valid
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT)
		  (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
	     (uniq-inst-at-stg '(DQ 0) MT))
  :hints (("goal" :in-theory (enable inv NO-stage-conflict
				     no-dq-stg-conflict
				     lift-b-ops
				     MA-def))))

(defthm no-inst-at-stg-if-no-DQ-DE0-valid
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT)
		  (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))))
	     (no-inst-at-stg '(DQ 0) MT))
  :hints (("goal" :in-theory (enable inv NO-stage-conflict
				     no-dq-stg-conflict
				     lift-b-ops
				     MA-def))))
(defthm uniq-inst-at-stg-if-DQ-DE1-valid
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT)
		  (b1p (DE-valid? (DQ-DE1 (MA-DQ MA)))))
	     (uniq-inst-at-stg '(DQ 1) MT))
  :hints (("goal" :in-theory (enable inv NO-stage-conflict
				     no-dq-stg-conflict
				     lift-b-ops
				     MA-def))))

(defthm no-inst-at-stg-if-no-DQ-DE1-valid
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT)
		  (not (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))))
	     (no-inst-at-stg '(DQ 1) MT))
  :hints (("goal" :in-theory (enable inv NO-stage-conflict
				     no-dq-stg-conflict
				     lift-b-ops
				     MA-def))))

(defthm uniq-inst-at-stg-if-DQ-DE2-valid
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT)
		  (b1p (DE-valid? (DQ-DE2 (MA-DQ MA)))))
	     (uniq-inst-at-stg '(DQ 2) MT))
  :hints (("goal" :in-theory (enable inv NO-stage-conflict
				     no-dq-stg-conflict
				     lift-b-ops
				     MA-def))))

(defthm no-inst-at-stg-if-no-DQ-DE2-valid
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT)
		  (not (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))))
	     (no-inst-at-stg '(DQ 2) MT))
  :hints (("goal" :in-theory (enable inv NO-stage-conflict
				     no-dq-stg-conflict
				     lift-b-ops
				     MA-def))))

(defthm uniq-inst-at-stg-if-DQ-DE3-valid
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT)
		  (b1p (DE-valid? (DQ-DE3 (MA-DQ MA)))))
	     (uniq-inst-at-stg '(DQ 3) MT))
  :hints (("goal" :in-theory (enable inv NO-stage-conflict
				     no-dq-stg-conflict
				     lift-b-ops
				     MA-def))))

(defthm no-inst-at-stg-if-no-DQ-DE3-valid
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT)
		  (not (b1p (DE-valid? (DQ-DE3 (MA-DQ MA))))))
	     (no-inst-at-stg '(DQ 3) MT))
  :hints (("goal" :in-theory (enable inv NO-stage-conflict
				     no-dq-stg-conflict
				     lift-b-ops
				     MA-def))))

(encapsulate nil
(local
 (defthm INST-stg-INST-at-stg-help
     (implies (uniq-inst-at-stg-in-trace stg trace)
	      (equal (inst-stg (INST-at-stg-in-trace stg trace)) stg))))
		     
(defthm INST-stg-INST-at-stg
    (implies (uniq-inst-at-stg stg MT)
	     (equal (INST-stg (INST-at-stg stg MT)) stg))
  :hints (("Goal" :in-theory (enable uniq-inst-at-stg
				     INST-at-stg))))
)

(encapsulate nil
(local  
 (defthm not-no-INST-at-stg-INST-stg-if-member-equal
     (implies (and (member-equal i trace)
		   (equal (INST-stg i) stg))
	      (not (no-INST-at-stg-in-trace stg trace)))))

(local  
 (defthm INST-at-stg-INST-stg-help
     (implies (and (uniq-INST-at-stg-in-trace stg trace)
		   (member-equal i trace)
		   (equal (INST-stg i) stg))
	      (equal (INST-at-stg-in-trace stg trace) i))))

(defthm INST-at-stg-INST-stg-IFU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (IFU-stg-p (INST-stg i)))
	     (equal (INST-at-stg (INST-stg i) MT) i))
  :hints (("goal" :in-theory (enable inv
				     no-stage-conflict
				     no-IFU-stg-conflict
				     INST-in MA-stg-def
				     uniq-inst-at-stg
				     no-inst-at-stg
				     INST-at-stg))))

(defthm INST-at-stg-INST-stg-DQ
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (DQ-stg-p (INST-stg i)))
	     (equal (INST-at-stg (INST-stg i) MT) i))
  :hints (("goal" :in-theory (enable inv
				     no-stage-conflict
				     no-DQ-stg-conflict
				     INST-in MA-stg-def
				     uniq-inst-at-stg
				     no-inst-at-stg
				     INST-at-stg))))

(defthm INST-at-stg-INST-stg-IU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (IU-stg-p (INST-stg i)))
	     (equal (INST-at-stg (INST-stg i) MT) i))
  :hints (("goal" :in-theory (enable inv
				     no-stage-conflict
				     no-IU-stg-conflict
				     INST-in MA-stg-def
				     uniq-inst-at-stg
				     no-inst-at-stg
				     INST-at-stg))))

(defthm INST-at-stg-INST-stg-MU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (MU-stg-p (INST-stg i)))
	     (equal (INST-at-stg (INST-stg i) MT) i))
  :hints (("goal" :in-theory (enable inv
				     no-stage-conflict
				     no-MU-stg-conflict
				     INST-in MA-stg-def
				     uniq-inst-at-stg
				     no-inst-at-stg
				     INST-at-stg))))

(defthm INST-at-stg-INST-stg-BU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (BU-stg-p (INST-stg i)))
	     (equal (INST-at-stg (INST-stg i) MT) i))
  :hints (("goal" :in-theory (enable inv
				     no-stage-conflict
				     no-BU-stg-conflict
				     INST-in MA-stg-def
				     uniq-inst-at-stg
				     no-inst-at-stg
				     INST-at-stg))))
)

(defun all-LSU-stg-p (stgs)
  (if (endp stgs)
      T
      (and (LSU-stg-p (car stgs))
	   (all-LSU-stg-p (cdr stgs)))))

(defun all-execute-stg-p (stgs)
  (if (endp stgs)
      T
      (and (execute-stg-p (car stgs))
	   (all-execute-stg-p (cdr stgs)))))

(defun all-complete-stg-p (stgs)
  (if (endp stgs)
      T
      (and (complete-stg-p (car stgs))
	   (all-complete-stg-p (cdr stgs)))))

(defun all-commit-stg-p (stgs)
  (if (endp stgs)
      T
      (and (commit-stg-p (car stgs))
	   (all-commit-stg-p (cdr stgs)))))

(defun all-wbuf-stg-p (stgs)
  (if (endp stgs) t
      (and (wbuf-stg-p (car stgs))
	   (all-wbuf-stg-p (cdr stgs)))))

(defun all-wbuf0-stg-p (stgs)
  (if (endp stgs) t
      (and (wbuf0-stg-p (car stgs))
	   (all-wbuf0-stg-p (cdr stgs)))))

(defun all-wbuf1-stg-p (stgs)
  (if (endp stgs) t
      (and (wbuf1-stg-p (car stgs))
	   (all-wbuf1-stg-p (cdr stgs)))))  

(encapsulate nil
(local
(defthm LSU-stg-p-INST-at-stgs-in-trace
    (implies (and (all-LSU-stg-p stgs)
		  (uniq-inst-at-stgs-in-trace stgs trace))
	     (LSU-stg-p (INST-stg (INST-at-stgs-in-trace stgs trace))))))

(defthm LSU-stg-p-INST-at-stgs
    (implies (and (all-LSU-stg-p stgs)
		  (uniq-inst-at-stgs stgs MT))
	     (LSU-stg-p (INST-stg (INST-at-stgs stgs MT))))
  :hints (("goal" :in-theory (enable INST-at-stgs uniq-inst-at-stgs))))
)

(encapsulate nil
(local
 (defthm execute-stg-p-INST-at-stgs-in-trace
     (implies (and (all-execute-stg-p stgs)
		   (uniq-inst-at-stgs-in-trace stgs trace))
	      (execute-stg-p (INST-stg (INST-at-stgs-in-trace stgs trace))))))

(defthm execute-stg-p-INST-at-stgs
    (implies (and (all-execute-stg-p stgs)
		  (uniq-inst-at-stgs stgs MT))
	     (execute-stg-p (INST-stg (INST-at-stgs stgs MT))))
  :hints (("goal" :in-theory (enable INST-at-stgs uniq-inst-at-stgs))))
)

(encapsulate nil
(local
(defthm complete-stg-p-INST-at-stgs-in-trace
    (implies (and (all-complete-stg-p stgs)
		  (uniq-inst-at-stgs-in-trace stgs trace))
	     (complete-stg-p (INST-stg (INST-at-stgs-in-trace stgs trace))))))

(defthm complete-stg-p-INST-at-stgs
    (implies (and (all-complete-stg-p stgs)
		  (uniq-inst-at-stgs stgs MT))
	     (complete-stg-p (INST-stg (INST-at-stgs stgs MT))))
  :hints (("goal" :in-theory (enable uniq-inst-at-stgs INST-at-stgs))))

)

(encapsulate nil
(local
(defthm commit-stg-p-INST-at-stgs-in-trace
    (implies (and (all-commit-stg-p stgs)
		  (uniq-inst-at-stgs-in-trace stgs trace))
	     (commit-stg-p (INST-stg (INST-at-stgs-in-trace stgs trace))))))

(defthm commit-stg-p-INST-at-stgs
    (implies (and (all-commit-stg-p stgs)
		  (uniq-inst-at-stgs stgs MT))
	     (commit-stg-p (INST-stg (INST-at-stgs stgs MT))))
  :hints (("goal" :in-theory (enable uniq-inst-at-stgs INST-at-stgs))))
)

(encapsulate nil
(local
(defthm wbuf-stg-p-INST-at-stgs-help
    (implies (and (all-wbuf-stg-p stgs)
		  (uniq-inst-at-stgs-in-trace stgs trace))
	     (wbuf-stg-p (inst-stg (INST-at-stgs-in-trace stgs trace))))))

(defthm wbuf-stg-p-INST-at-stgs
    (implies (and (all-wbuf-stg-p stgs)
		  (uniq-inst-at-stgs stgs MT))
	     (wbuf-stg-p (inst-stg (INST-at-stgs stgs MT))))
  :hints (("goal" :in-theory (enable INST-at-stgs uniq-inst-at-stgs))))
)

(encapsulate nil
(local
(defthm wbuf0-stg-p-INST-at-stgs-help
    (implies (and (all-wbuf0-stg-p stgs)
		  (uniq-inst-at-stgs-in-trace stgs trace))
	     (wbuf0-stg-p (inst-stg (INST-at-stgs-in-trace stgs trace))))))

(defthm wbuf0-stg-p-INST-at-stgs
    (implies (and (all-wbuf0-stg-p stgs)
		  (uniq-inst-at-stgs stgs MT))
	     (wbuf0-stg-p (inst-stg (INST-at-stgs stgs MT))))
  :hints (("goal" :in-theory (enable INST-at-stgs uniq-inst-at-stgs))))
)

(encapsulate nil
(local
(defthm wbuf1-stg-p-INST-at-stgs-help
    (implies (and (all-wbuf1-stg-p stgs)
		  (uniq-inst-at-stgs-in-trace stgs trace))
	     (wbuf1-stg-p (inst-stg (INST-at-stgs-in-trace stgs trace))))))

(defthm wbuf1-stg-p-INST-at-stgs
    (implies (and (all-wbuf1-stg-p stgs)
		  (uniq-inst-at-stgs stgs MT))
	     (wbuf1-stg-p (inst-stg (INST-at-stgs stgs MT))))
  :hints (("goal" :in-theory (enable INST-at-stgs uniq-inst-at-stgs))))
)

(encapsulate nil
(local  
 (defthm strong-no-inst-at-stg-INST-stg-help
     (implies (and (member-equal i trace)
		   (equal (INST-stg i) stg))
	      (not (no-INST-at-stg-in-trace stg trace)))))

; If i is in MT, and i's stage is stg, then (no-INST-at-stg stg MT) is false.
(defthm strong-no-inst-at-stg-INST-stg
    (implies (and (INST-in i MT)
		  (equal (INST-stg i) stg))
	     (not (no-INST-at-stg stg MT)))
  :Hints (("goal" :in-theory (enable INST-in no-INST-at-stg))))

(local  
 (defthm INST-at-stg-INST-stg-help
     (implies (and (uniq-INST-at-stg-in-trace stg trace)
		   (member-equal i trace)
		   (equal (INST-stg i) stg))
	      (equal (INST-at-stg-in-trace stg trace) i))))

; If i is in MT, then (INST-at-stg (INST-stg i) MT) = i.
(defthm strong-INST-at-stg-inst-stg
    (implies (and (uniq-INST-at-stg stg MT)
		  (INST-in i MT)
		  (equal (INST-stg i) stg))
	     (equal (INST-at-stg stg MT) i))
  :hints (("goal" :in-theory (enable INST-at-stg uniq-INST-at-stg INST-in))))
)

(defthm INST-at-stg-inst-stg
    (implies (and (INST-in i MT) (uniq-INST-at-stg (INST-stg i) MT))
	     (equal (INST-at-stg (INST-stg i) MT) i))
  :hints (("goal" :restrict ((strong-INST-at-stg-inst-stg
			      ((i i)))))))
				   

(encapsulate nil
(local
(defthm not-no-inst-at-stgs-inst-stg-if-member-equal
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (member-equal i trace)
		  (member-equal (INST-stg i) stgs))
	     (not (no-inst-at-stgs-in-trace stgs trace))))) 

; If a MAETT contains an instruction whose stage is a member of stgs,
; (non-inst-at-stgs stgs MT) is false.
(defthm not-no-inst-at-stgs-inst-stg-if-INST-in
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (member-equal (INST-stg i) stgs))
	     (not (no-inst-at-stgs stgs MT)))
  :hints (("goal" :in-theory (enable no-inst-at-stgs INST-in) )))
)

(encapsulate nil
(local
(defthm uniq-inst-at-stg-if-uniq-inst-at-stgs-help-help
    (implies (and (member-equal i trace)
		  (member-equal (inst-stg i) stgs))
	     (not (no-inst-at-stgs-in-trace stgs trace)))))

(local
(defthm uniq-inst-at-stg-if-uniq-inst-at-stgs-help
    (implies (and (member-equal i trace)
		  (uniq-inst-at-stgs-in-trace stgs trace)
		  (equal (INST-stg i) stg)
		  (member-equal stg stgs))
	     (uniq-inst-at-stg-in-trace stg trace))))

(defthm uniq-inst-at-stg-if-uniq-inst-at-stgs
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (uniq-inst-at-stgs stgs MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg I) stg)
		  (member-equal stg stgs))
	     (uniq-inst-at-stg stg MT))
  :hints (("goal" :in-theory (enable uniq-inst-at-stg uniq-inst-at-stgs
				     INST-in))))
)

(deftheory strong-inst-at-stg-theory
    '(strong-no-inst-at-stg-INST-stg uniq-inst-at-stg-if-uniq-inst-at-stgs
      strong-INST-at-stg-inst-stg not-no-inst-at-stgs-inst-stg-if-INST-in))
(in-theory (disable strong-inst-at-stg-theory))

(encapsulate nil
(local
(defthm INST-at-stg-INST-stg-LSU-RS0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (equal (INST-stg I) '(LSU RS0)))
	     (equal (INST-at-stg '(LSU RS0) MT) i))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     strong-inst-at-stg-theory
				     no-LSU-stg-conflict)))))

(local
(defthm INST-at-stg-INST-stg-LSU-RS1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (equal (INST-stg I) '(LSU RS1)))
	     (equal (INST-at-stg '(LSU RS1) MT) i))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     strong-inst-at-stg-theory
				     no-LSU-stg-conflict)))))

(local
(defthm INST-at-stg-INST-stg-LSU-RBUF
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (equal (INST-stg I) '(LSU RBUF)))
	     (equal (INST-at-stg '(LSU RBUF) MT) i))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     strong-inst-at-stg-theory
				     no-LSU-stg-conflict)))))

(local
(defthm INST-at-stg-INST-stg-LSU-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (equal (INST-stg I) '(LSU wbuf0)))
	     (equal (INST-at-stg '(LSU wbuf0) MT) i))
  :hints (("goal" :in-theory (e/d (no-stage-conflict
				   strong-inst-at-stg-theory
				   no-LSU-stg-conflict)
				  (no-stage-conflict-p-forward))
		  :use ((:instance no-stage-conflict-p-forward (MA MA)))
		  :restrict ((uniq-inst-at-stg-if-uniq-inst-at-stgs
			      ((stgs '((LSU WBUF0)
				       (LSU WBUF0 LCH)
				       (COMPLETE WBUF0)
				       (COMMIT WBUF0))))))))))

(local
(defthm INST-at-stg-INST-stg-LSU-wbuf0-lch
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (equal (INST-stg I) '(LSU wbuf0 lch)))
	     (equal (INST-at-stg '(LSU wbuf0 lch) MT) i))
  :hints (("goal" :in-theory (e/d (no-stage-conflict
				   strong-inst-at-stg-theory
				   no-LSU-stg-conflict)
				  (no-stage-conflict-p-forward))
		  :use ((:instance no-stage-conflict-p-forward (MA MA)))
		  :restrict ((uniq-inst-at-stg-if-uniq-inst-at-stgs
			      ((stgs '((LSU WBUF0)
				       (LSU WBUF0 LCH)
				       (COMPLETE WBUF0)
				       (COMMIT WBUF0))))))))))

(local
(defthm INST-at-stg-INST-stg-LSU-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (equal (INST-stg I) '(LSU wbuf1)))
	     (equal (INST-at-stg '(LSU wbuf1) MT) i))
  :hints (("goal" :in-theory (e/d (no-stage-conflict
				   strong-inst-at-stg-theory
				   no-LSU-stg-conflict)
				  (no-stage-conflict-p-forward))
		  :use ((:instance no-stage-conflict-p-forward (MA MA)))
		  :restrict ((uniq-inst-at-stg-if-uniq-inst-at-stgs
			      ((stgs '((LSU WBUF1)
				       (LSU WBUF1 LCH)
				       (COMPLETE WBUF1)
				       (COMMIT WBUF1))))))))))

(local
(defthm INST-at-stg-INST-stg-LSU-wbuf1-lch
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (equal (INST-stg I) '(LSU wbuf1 lch)))
	     (equal (INST-at-stg '(LSU wbuf1 lch) MT) i))
  :hints (("goal" :in-theory (e/d (no-stage-conflict
				   strong-inst-at-stg-theory
				   no-LSU-stg-conflict)
				  (no-stage-conflict-p-forward))
		  :use ((:instance no-stage-conflict-p-forward (MA MA)))
		  :restrict ((uniq-inst-at-stg-if-uniq-inst-at-stgs
			      ((stgs '((LSU WBUF1)
				       (LSU WBUF1 LCH)
				       (COMPLETE WBUF1)
				       (COMMIT WBUF1))))))))))

(local
(defthm INST-at-stg-INST-stg-LSU-lch
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (equal (INST-stg I) '(LSU lch)))
	     (equal (INST-at-stg '(LSU lch) MT) i))
  :hints (("goal" :in-theory (e/d (no-stage-conflict
				   strong-inst-at-stg-theory
				   no-LSU-stg-conflict)
				  (no-stage-conflict-p-forward))
		  :use ((:instance no-stage-conflict-p-forward (MA MA)))
		  :restrict ((uniq-inst-at-stg-if-uniq-inst-at-stgs
			      ((stgs '((LSU LCH)
				       (LSU WBUF0 LCH)
				       (LSU WBUF1 LCH))))))))))

(defthm INST-at-stg-INST-stg-LSU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (LSU-stg-p (INST-stg i)))
	     (equal (INST-at-stg (INST-stg i) MT) i))
  :hints (("goal" :in-theory (enable LSU-stg-p))))
) ;encapsulate

(defthm INST-at-stg-inst-stg-execute
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (execute-stg-p (INST-stg i)))
	     (equal (INST-at-stg (INST-stg i) MT) i))
  :hints (("goal" :in-theory (enable execute-stg-p))))

(defthm INST-at-stg-inst-stg-execute-2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) stg)
		  (execute-stg-p stg))
	     (equal (INST-at-stg stg MT) i))
  :hints (("goal" :in-theory (enable execute-stg-p))))
(in-theory (disable INST-at-stg-inst-stg-execute-2))

(defthm INST-at-stg-INST-stg-complete-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (equal (INST-stg I) '(complete wbuf0)))
	     (equal (INST-at-stg '(complete wbuf0) MT) i))
  :hints (("goal" :in-theory (e/d (no-stage-conflict
				   strong-inst-at-stg-theory
				   no-LSU-stg-conflict)
				  (no-stage-conflict-p-forward))
		  :use ((:instance no-stage-conflict-p-forward (MA MA)))
		  :restrict ((uniq-inst-at-stg-if-uniq-inst-at-stgs
			      ((stgs '((LSU wbuf0)
				       (LSU WBUF0 LCH)
				       (complete wbuf0)
				       (commit wbuf0)))))))))

(defthm INST-at-stg-INST-stg-complete-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (equal (INST-stg I) '(complete wbuf1)))
	     (equal (INST-at-stg '(complete wbuf1) MT) i))
  :hints (("goal" :in-theory (e/d (no-stage-conflict
				   strong-inst-at-stg-theory
				   no-LSU-stg-conflict)
				  (no-stage-conflict-p-forward))
		  :use ((:instance no-stage-conflict-p-forward (MA MA)))
		  :restrict ((uniq-inst-at-stg-if-uniq-inst-at-stgs
			      ((stgs '((LSU wbuf1)
				       (LSU WBUF1 LCH)
				       (complete wbuf1)
				       (commit wbuf1)))))))))

(encapsulate nil
(local
(defthm INST-at-stg-INST-stg-commit-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (equal (INST-stg I) '(commit wbuf0)))
	     (equal (INST-at-stg '(commit wbuf0) MT) i))
  :hints (("goal" :in-theory (e/d (no-stage-conflict
				   strong-inst-at-stg-theory
				   no-LSU-stg-conflict)
				  (no-stage-conflict-p-forward))
		  :use ((:instance no-stage-conflict-p-forward (MA MA)))
		  :restrict ((uniq-inst-at-stg-if-uniq-inst-at-stgs
			      ((stgs '((LSU wbuf0)
				       (LSU WBUF0 LCH)
				       (complete wbuf0)
				       (commit wbuf0))))))))))

(local
(defthm INST-at-stg-INST-stg-commit-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (equal (INST-stg I) '(commit wbuf1)))
	     (equal (INST-at-stg '(commit wbuf1) MT) i))
  :hints (("goal" :in-theory (e/d (no-stage-conflict
				   strong-inst-at-stg-theory
				   no-LSU-stg-conflict)
				  (no-stage-conflict-p-forward))
		  :use ((:instance no-stage-conflict-p-forward (MA MA)))
		  :restrict ((uniq-inst-at-stg-if-uniq-inst-at-stgs
			      ((stgs '((LSU wbuf1)
				       (LSU WBUF1 LCH)
				       (complete wbuf1)
				       (commit wbuf1))))))))))

(defthm INST-at-stg-inst-stg-commit
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (commit-stg-p (INST-stg i)))
	     (equal (INST-at-stg (INST-stg i) MT) i))
  :hints (("goal" :in-theory (enable commit-stg-p))))
)

(encapsulate nil
(local
(defthm INST-at-stgs-if-INST-in-help-help
    (implies (and (member-equal i trace)
		  (member-equal (INST-stg i) stgs))
	     (not (no-inst-at-stgs-in-trace stgs trace)))))
  
(local
(defthm INST-at-stgs-if-INST-in-help
    (implies (and (member-equal i trace)
		  (uniq-inst-at-stgs-in-trace stgs trace)
		  (member-equal (INST-stg i) stgs))
	     (equal (INST-at-stgs-in-trace stgs trace) i))))

(defthm INST-at-stgs-if-INST-in
    (implies (and (inv MT MA)
		  (INST-p I) (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stgs stgs MT)
		  (member-equal (INST-stg i) stgs))
	     (equal (INST-at-stgs stgs MT) i))
  :Hints (("goal" :in-theory (enable INST-in uniq-inst-at-stgs
				     INST-at-stgs))))
)
(in-theory (disable INST-at-stgs-if-INST-in))
