;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; MI-inv.lisp
; Author  Jun Sawada, University of Texas at Austin
;
;  This book combines the proof of all properties and
;  actually proves that inv is an invariant. 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "ACL2")

(include-book "MA2-lemmas")
(include-book "MAETT-lemmas")
(local (include-book "wk-inv"))
(local (include-book "MI-inv"))
(local (include-book "ISA-comp"))
(local (include-book "misc-inv"))
(local (include-book "uniq-inv"))
(local (include-book "in-order"))
(local (include-book "reg-ref"))
(deflabel begin-invariant-proof)

(defthm inv-initial-MT
    (implies (and (MA-state-p MA) (flushed-p MA))
	     (inv (init-MT MA) MA))
  :hints (("goal" :expand (inv (init-MT MA) MA))))

(defthm inv-step
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (MA-input-p sigs)
		  (not (MT-CMI-p (MT-step MT MA sigs))))
	     (inv (MT-step MT MA sigs)
		  (MA-step MA sigs)))
  :hints (("Goal" :expand (inv (MT-step MT MA sigs)
				      (MA-step MA sigs))))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (MAETT-p MT)
			   (MA-state-p MA)
			   (MA-input-p sigs)
			   (not (inv (MT-step MT MA sigs)
				     (MA-step MA sigs))))
		      (MT-CMI-p (MT-step MT MA sigs))))))

;  Invariant proof is completed.  The reader can skip the following comment.

#|
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; An alternative definition of MT-step and its invariant proof
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  We have an alternative definition of MT-step, which is defined as
;  MT-step*.  MT-step and MT-stepn* are slightly different. 
;  
; From here, we try to modify the definition of
; INST-step and INST-init.  The original definition of MT-step and
; the functions used to define it are a little bit intended for the proof
; efficiency, and not for presentation.  Here we give a simpler definitions
; of INST-step and INST-init, hence, MT-step, which must be easier for the
; reader. This is proven for FMSD paper. 
; 
;  Inst-init returns the initial INST state. 
(defun INST-init* (MT MA sigs)
  (if (b1p (fetch-inst? MA sigs))
      (fetched-inst MT (MT-final-ISA MT)
		    (MT-specultv? MT)
		    (MT-self-modify? MT))
      (if (b1p (ex-intr? MA sigs))
	  (exintr-INST MT  (MT-final-ISA MT) (MT-self-modify? MT))
	  nil)))
      
(defun trace-pre-modified? (i trace smc)
  (if (endp trace)
      smc
      (if (equal (car trace) i)
	  smc
	  (trace-pre-modified? i (cdr trace) (INST-modified? (car trace))))))
      
; MT-pre-modified? determines if any instruction preceding i are
; modified. 
(defun MT-pre-modified? (i MT)
  (trace-pre-modified? i (MT-trace MT) 0))
(in-theory (disable MT-pre-modified?))

; INST-step updates INST.  In the original definition, we used
; both exintr-INST and INST-step to define the next state of INST.
(defun INST-step* (i MT MA sigs)
  (if (and (b1p (INST-exintr-now? i MA sigs))
	   (not (b1p (INST-cause-jmp? i MT MA sigs))))
      (exintr-INST MT (INST-pre-ISA i) (MT-pre-modified? i MT))
      (step-INST i MT MA sigs)))

; This is a simplified version of step-trace.
(defun step-trace* (trace MT MA sigs)
    (if (endp trace)
	(if (or (b1p (fetch-inst? MA sigs))
		(b1p (ex-intr? MA sigs)))
	    (list (INST-init* MT MA sigs))
	    nil)
	(b-if (INST-cause-jmp? (car trace) MT MA sigs)
	      (list (INST-step* (car trace) MT MA sigs))
	      (b-if (INST-exintr-now? (car trace) MA sigs)
		    (list (INST-step* (car trace) MT MA sigs))
		    (cons (INST-step* (car trace) MT MA sigs)
			  (step-trace* (cdr trace) MT MA sigs))))))

; This is a simplified version MT-step.
(defun MT-step* (MT MA sigs)
  (MAETT (MT-init-ISA MT)
	 (1+ (MT-new-ID MT))
	 (step-MT-dq-len MT MA sigs)
	 (step-MT-wb-len MT MA sigs)
	 (step-MT-rob-flg MT MA sigs)
	 (step-MT-rob-head MT MA sigs)
	 (step-MT-rob-tail MT MA sigs)
	 (step-trace* (MT-trace MT) MT MA sigs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;   Here is a proof for an alternative definition of MT-step
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
(local
(encapsulate nil
(local
(defthm INST-pre-ISA-car-ISA-before-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (consp sub)
		  (tail-p sub trace)
		  (INST-listp trace))
	     (equal (INST-pre-ISA (car sub))
		    (ISA-at-tail sub trace (INST-pre-ISA (car trace)))))
  :hints ((when-found (INST-PRE-ISA (CAR (CDR TRACE)))
		      (:cases ((consp (cdr trace))))))
  :rule-classes nil))

(defthm INST-pre-ISA-car-ISA-before
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (consp trace)
		  (subtrace-p trace MT)
		  (INST-listp trace))
	     (equal (ISA-before trace MT) (INST-pre-ISA (car trace))))
  :hints (("goal" :in-theory (enable subtrace-p ISA-before)
		  :use (:instance INST-pre-ISA-car-ISA-before-help
				  (sub trace) (trace (MT-trace MT))))
	  ("goal'" :cases ((consp (MT-trace MT))))))
))

(local
(encapsulate nil 
(local
(defthm INST-modified-car-ISA-before-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (consp sub)
		  (tail-p sub trace)
		  (INST-listp trace))
	     (equal (trace-pre-modified? (car sub) trace smc)
		    (modified-inst-before-tail sub trace smc)))
  :hints (("goal" :expand (TRACE-PRE-MODIFIED? (CAR SUB) TRACE SMC)))))

(defthm INST-modified-car-ISA-before
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (consp trace)
		  (subtrace-p trace MT)
		  (INST-listp trace))
	     (equal (modified-inst-before? trace MT)
		    (MT-pre-modified? (car trace) MT)))
  :hints (("goal" :in-theory (enable modified-inst-before? subtrace-p
				     MT-pre-modified?))))
))

(local
(defthm new-step-trace
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace))
	     (equal (step-trace trace MT MA sigs
				(ISA-before trace MT)
				(specultv-before? trace MT)
				(modified-inst-before? trace MT))
		    (step-trace* trace MT MA sigs)))
  :rule-classes nil))
		    

; This lemma shows that a simplified version of MT-step is equivalent to
; the original definition, 
(defthm MT-step-MT-step*
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MT-step* MT MA sigs)
		    (MT-step MT MA sigs)))
  :Hints (("goal" :in-theory (enable MT-step)
		  :use (:instance new-step-trace
				  (trace (MT-trace MT))))))

(defthm inv-step*
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (MA-input-p sigs)
		  (not (MT-CMI-p (MT-step MT MA sigs))))
	     (inv (MT-step* MT MA sigs)
		  (MA-step MA sigs))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  End of the proof of the invariant for the alternative definition.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
|#