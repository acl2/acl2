;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; in-order.lisp
; Author  Jun Sawada, University of Texas at Austin
;
;  This book contains the proof of the invariant properties
;  in-order-DQ-p, in-order-LSU-inst-p, and in-order-ROB-p.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "ACL2")

(include-book "MA2-lemmas")
(include-book "MAETT-lemmas")

(deflabel begin-in-order)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Proof about in-order-DQ-p
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Proof of in-order-DQ-p for initial states.
(defthm in-order-DQ-p-init-MT
    (in-order-DQ-p (init-MT MA))
  :hints (("goal" :in-theory (enable in-order-DQ-p init-MT))))

;;; Proof of in-order-dq-p-preserved.
(defthm INST-stg-step-inst-DQ-if-not-dispatch-inst
    (implies (and (inv MT MA)
		  (DQ-stg-p (INST-stg i))
		  (not (b1p (dispatch-inst? MA)))
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-stg (step-inst i MT MA sigs)) (INST-stg i)))
  :hints (("Goal" :in-theory (enable step-inst-dq-inst
				     step-inst-low-level-functions))))

(defthm DQ-stg-idx-new-DQ-stage
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (dispatch-inst? MA)))
		  (not (b1p (DQ-full? (MA-DQ MA)))))
	     (equal (DQ-stg-idx (new-DQ-stage MT MA))
		    (MT-DQ-len MT)))
  :hints (("Goal" :in-theory (enable new-DQ-stage DQ-STG-IDX
				     DQ-full? coerce-dq-stg))))

(defun last-DQ-index-before (sub trace count)
  (if (endp trace)
      count
      (if (equal sub trace)
	  count
	  (if (DQ-stg-p (INST-stg (car trace)))
	      (last-DQ-index-before sub (cdr trace)
				    (1+ (DQ-stg-idx (INST-stg (car trace)))))
	      (last-DQ-index-before sub (cdr trace) count)))))

(defun MT-last-DQ-index-before (sub MT)
  (last-DQ-index-before sub (MT-trace MT) 0))

(in-theory (disable MT-last-DQ-index-before))

(encapsulate nil
(local
(defthm MT-last-DQ-index-before-cdr-if-not-DQ-help
    (implies (and (consp sub) (not (dq-stg-p (INST-stg (car sub))))
		  (tail-p sub trace))
	     (equal (last-DQ-index-before (cdr sub) trace count)
		    (last-DQ-index-before sub trace count)))))

(defthm MT-last-DQ-index-before-cdr-if-not-DQ
    (implies (and (consp trace) (not (dq-stg-p (INST-stg (car trace))))
		  (subtrace-p trace MT))
	     (equal (MT-last-DQ-index-before (cdr trace) MT)
		    (MT-last-DQ-index-before trace MT)))
  :hints (("Goal" :in-theory (enable MT-last-DQ-index-before
				     subtrace-p))))
)

(encapsulate nil
(local
(defthm MT-last-DQ-index-before-cdr-if-DQ-help
    (implies (and (consp sub) (dq-stg-p (INST-stg (car sub)))
		  (tail-p sub trace))
	     (equal (last-DQ-index-before (cdr sub) trace count)
		    (1+ (DQ-stg-idx (INST-stg (car sub))))))))

(defthm MT-last-DQ-index-before-cdr-if-DQ
    (implies (and (consp trace) (dq-stg-p (INST-stg (car trace)))
		  (subtrace-p trace MT))
	     (equal (MT-last-DQ-index-before (cdr trace) MT)
		    (1+ (DQ-stg-idx (INST-stg (car trace))))))
  :hints (("Goal" :in-theory (enable MT-last-DQ-index-before
				     subtrace-p))))
)

(defthm MT-DQ-len-non-zero-if-DQ-inst-in
    (implies (and (inv MT MA)
		  (DQ-stg-p (INST-stg i))
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA))
	     (not (equal (MT-DQ-len MT) 0)))
  :hints (("Goal" :in-theory (enable DQ-stg-p))))
(in-theory (disable MT-DQ-len-non-zero-if-DQ-inst-in))

(encapsulate nil
(local
(defthm MT-last-DQ-index-before-if-car-is-IFU-if-DQ-len-zero-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (equal (MT-DQ-len MT) 0)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (last-DQ-index-before sub trace 0) 0))
  :hints (("Goal" :in-theory (enable MT-DQ-len-non-zero-if-DQ-inst-in)))))

(defthm MT-last-DQ-index-before-if-car-is-IFU-if-DQ-len-zero
    (implies (and (inv MT MA)
		  (consp trace)
		  (equal (MT-DQ-len MT) 0)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MT-last-DQ-index-before trace MT) 0))
  :hints (("Goal" :in-theory (enable MT-last-DQ-index-before))))
)
		    
(defun max-DQ-stg (MT) (list 'DQ (1- (MT-DQ-len MT))))
(in-theory (disable max-DQ-stg))

(defthm uniq-inst-at-max-DQ-stg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (MT-DQ-len MT) 0)))
	     (uniq-inst-at-stg (max-DQ-stg MT) MT))
  :hints (("Goal" :in-theory (enable max-DQ-stg))))

(defthm DQ-stg-idx-max-dq
    (equal (DQ-stg-idx (MAX-DQ-stg MT)) (1- (MT-DQ-len MT)))
  :hints (("Goal" :in-theory (enable max-DQ-stg dq-stg-idx))))

(defthm DQ-stg-p-max-DQ-stg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (MT-DQ-len MT) 0)))
	     (DQ-stg-p (max-DQ-stg MT)))
  :hints (("Goal" :in-theory (enable max-DQ-stg DQ-stg-p))))

(encapsulate nil
(local
(defthm hack-1
    (implies (equal stg (MAX-DQ-stg MT))
	     (equal (DQ-stg-idx stg) (1- (MT-DQ-len MT))))))

(local
(defthm DQ-stg-idx-lt-MT-DQ-len
    (implies (and (inv MT MA)
		  (INST-in j MT) (INST-p j) 
		  (MAETT-p MT) (MA-state-p MA)
		  (DQ-stg-p (INST-stg j)))
	     (< (DQ-stg-idx (INST-stg j)) (MT-DQ-len MT)))
  :hints (("Goal" :in-theory (enable DQ-stg-p)))
  :rule-classes :linear))

; Cf.  DQ0-is-earlier-than-other-DQ
(local
(defthm no-DQ-inst-after-DQ-max-stg
    (implies (and (inv MT MA)
		  (INST-in j MT) (INST-p j) 
		  (inst-in-order-p i j MT)
		  (equal (INST-stg i) (max-DQ-stg MT))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (DQ-stg-p (INST-stg j))))
  :hints (("Goal" :use ((:instance dq-stg-index-monotonic)
			(:instance DQ-stg-p-max-DQ-stg))
		  :in-theory (disable DQ-stg-p-max-DQ-stg)))))

(local
(defthm last-dq-index-before-if-trace-is-after-max-DQ
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (subtrace-p trace MT) (INST-listp trace)
		  (subtrace-after-p i trace MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) (max-DQ-stg MT)))
	     (equal (last-dq-index-before sub trace count) count))
  :hints (("Goal" :restrict ((no-DQ-inst-after-DQ-max-stg
			      ((i i))))))))

(local
 (defthm not-uniq-inst-at-max-dq-stg-if-car-is-IFU
     (implies (and (inv MT MA)
		   (subtrace-p trace MT) (INST-listp trace)
		   (dq-stg-p stg)
		   (consp trace) (IFU-stg-p (INST-stg (car trace)))
		   (MAETT-p MT) (MA-state-p MA))
	      (not (uniq-inst-at-stg-in-trace stg trace)))
   :Hints (("Goal" :do-not-induct t
		   :cases ((consp (cdr trace)))
		   :expand (uniq-inst-at-stg-in-trace stg trace)))))

(local
(defthm MT-last-DQ-index-before-if-car-is-IFU-if-DQ-len-pos-help
    (implies (and (inv MT MA)
		  (consp sub)
		  (IFU-stg-p (INST-stg (car sub)))
		  (uniq-inst-at-stg-in-trace (max-DQ-stg MT) trace)
		  (tail-p sub trace)
		  (not (equal (MT-DQ-len MT) 0))
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (last-DQ-index-before sub trace count)
		    (MT-DQ-len MT)))
  :Hints (("Goal" :restrict ((last-dq-index-before-if-trace-is-after-max-DQ
			      ((i (car trace)))))))))

(defthm MT-last-DQ-index-before-if-car-is-IFU-if-DQ-len-pos
    (implies (and (inv MT MA)
		  (consp trace)
		  (IFU-stg-p (INST-stg (car trace)))
		  (not (equal (MT-DQ-len MT) 0))
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MT-last-DQ-index-before trace MT)
		    (MT-DQ-len MT)))
  :hints (("Goal" :in-theory (e/d (MT-last-DQ-index-before
				   uniq-inst-at-stg subtrace-p)
				  (uniq-inst-at-max-DQ-stg))
		  :use (:instance uniq-inst-at-max-DQ-stg))))
)

(defthm MT-last-DQ-index-before-if-car-is-IFU
    (implies (and (inv MT MA)
		  (consp trace)
		  (IFU-stg-p (INST-stg (car trace)))
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MT-last-DQ-index-before trace MT)
		    (MT-DQ-len MT)))
  :hints (("Goal" :cases ((equal (MT-DQ-len MT) 0)))))

(defthm MT-last-DQ-index-before-MT-trace
    (equal (MT-last-DQ-index-before (MT-trace MT) MT) 0)
  :hints (("Goal" :in-theory (enable MT-last-DQ-index-before))))

(encapsulate nil
(local
(defthm DQ-stg-idx-car-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (IN-order-DQ-trace-p trace idx)
		  (consp sub) (DQ-stg-p (INST-stg (car sub)))
		  (tail-p sub trace) (MAETT-p MT) (MA-state-p MA))
	     (equal (last-DQ-index-before sub trace idx)
		    (DQ-stg-idx (INST-stg (car sub)))))
  :hints ((when-found (IFU-STG-P (INST-STG (CAR TRACE)))
		      (:cases ((consp (cdr trace))))))))

(defthm DQ-stg-idx-car
    (implies (and (inv MT MA)
		  (consp trace) (subtrace-p trace MT) (INST-listp trace) 
		  (DQ-stg-p (INST-stg (car trace)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (DQ-stg-idx (INST-stg (car trace)))
		    (MT-last-DQ-index-before trace MT)))
  :hints (("Goal" :in-theory (enable MT-last-DQ-index-before
				     subtrace-p
				     inv In-order-DQ-p)
		  :restrict ((DQ-stg-idx-car-help
			      ((MT MT) (MA MA)))))))
)

(defthm MT-last-DQ-index-before-if-car-trace-at-DQ-idx
    (implies (and (inv MT MA)
		  (consp trace) (subtrace-p trace MT) (INST-listp trace) 
		  (equal (INST-stg (car trace)) (list 'DQ idx))
		  (integerp idx) (<= 0 idx) (< idx 4)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MT-last-DQ-index-before trace MT) idx))
  :hints (("Goal" :use (:instance DQ-stg-idx-car)
		  :in-theory (e/d (DQ-stg-p dq-stg-idx) (DQ-stg-idx-car)))))

(encapsulate nil
(local
(defthm in-order-dq-p-induction-1
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (b1p (dispatch-inst? MA))
		  (MAETT-p MT) (MA-state-p MA))
	     (in-order-DQ-trace-p (step-trace trace MT MA sigs ISA spc smc)
				  (coerce-DQ-stg
				   (1- (MT-last-DQ-index-before trace MT)))))
  :hints (("Goal" :in-theory (enable MT-step in-order-DQ-p
				     new-dq-stage
				     DQ-stg-p))
	  (when-found (INST-STG (STEP-INST (CAR TRACE) MT MA SIGS))
		      (:cases ((IFU-stg-p (INST-stg (car trace)))
			       (DQ-stg-p (INST-stg (car trace))))))
	  (when-found (IFU-STG-P (INST-STG (CAR TRACE)))
		      (:cases ((consp (cdr trace))))))
  :rule-classes nil))

(local
(defthm in-order-dq-p-induction-2
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (not (b1p (dispatch-inst? MA)))
		  (MAETT-p MT) (MA-state-p MA))
	     (in-order-DQ-trace-p (step-trace trace MT MA sigs ISA spc smc)
				  (MT-last-DQ-index-before trace MT)))
  :hints (("Goal" :in-theory (enable MT-step in-order-DQ-p))
	  (when-found (IFU-STG-P (INST-STG (STEP-INST (CAR TRACE) MT MA SIGS)))
		      (:cases ((IFU-stg-p (INST-stg (car trace)))
			       (DQ-stg-p (INST-stg (car trace))))))
	  (when-found (IFU-STG-P (INST-STG (CAR TRACE)))
		      (:cases ((consp (cdr trace))))))
  :rule-classes nil))

(defthm in-order-dq-p-preserved
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (IN-order-DQ-p (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable MT-step in-order-DQ-p
				     inv)
		  :use ((:instance in-order-dq-p-induction-1
				   (trace (MT-trace MT))
				   (ISA (MT-init-ISA MT))
				   (spc 0) (smc 0))
			(:instance in-order-dq-p-induction-2
				   (trace (MT-trace MT))
				   (ISA (MT-init-ISA MT))
				   (spc 0) (smc 0))))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof about IN-order-rob-p
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Proof of in-order-rob-p for initial states
(defthm in-order-rob-p-init-MT
    (in-order-rob-p (init-MT MA))
  :hints (("goal" :in-theory (enable init-MT in-order-rob-p))))

;;;; Proof of in-order-rob-p-preserved
(defun ROB-index-at (sub trace rix)
  (if (endp trace) rix
      (if (equal sub trace) rix
	  (if (or (execute-stg-p (INST-stg (car trace)))
		  (complete-stg-p (INST-stg (car trace))))
	      (rob-index-at sub (cdr trace) (rob-index (1+ rix)))
	      (rob-index-at sub (cdr trace) rix)))))

(defun MT-ROB-index-at (sub MT)
  (ROB-index-at sub (MT-trace MT) (MT-ROB-head MT)))
  
(in-theory (disable MT-ROB-index-at))

(defthm MT-rob-index-at-MT-trace
    (equal (MT-rob-index-at (MT-trace MT) MT) (MT-rob-head MT))
  :hints (("Goal" :in-theory (enable MT-rob-index-at))))

(encapsulate nil
(local
 (defthm INST-rob-car-MT-rob-index-at-help-help
     (implies (and (inv MT MA)
		   (tail-p sub trace)
		   (subtrace-p trace MT) (INST-listp trace)
		   (consp trace)
		   (dispatched-p (car sub))
		   (consp sub)
		   (MAETT-p MT) (MA-state-p MA))
	      (not (DQ-stg-p (INST-stg (car trace)))))
   :hints (("Goal" :cases ((equal sub trace))
		   :in-theory (e/d (dispatched-p)
				   (inst-in-order-dispatched-undispatched)))
	   ("subgoal 2" :use (:instance inst-in-order-dispatched-undispatched
					(i (car sub)) (j (car trace)))))))

(local
(defthm INST-rob-car-MT-rob-index-at-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (in-order-rob-trace-p trace idx)
		  (consp sub)
		  (tail-p sub trace)
		  (not (committed-p (car sub)))
		  (dispatched-p (car sub))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (equal (INST-tag (car sub)) (rob-index-at sub trace idx))
		    T))
  :hints (("Goal" :in-theory (enable committed-p dispatched-p)
		  :restrict ((INST-rob-car-MT-rob-index-at-help-help
			      ((sub sub)))))
	  (when-found (IFU-STG-P (INST-STG (CAR TRACE)))
		      (:cases ((consp (cdr trace))))))))

(defthm INST-rob-car-MT-rob-index-at
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (consp trace)
		  (not (committed-p (car trace)))
		  (dispatched-p (car trace))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (equal (INST-tag (car trace)) (MT-rob-index-at trace MT))
		    T))
  :hints (("Goal" :in-theory (enable MT-rob-index-at subtrace-p
				     inv in-order-rob-p)
		  :restrict ((INST-rob-car-MT-rob-index-at-help
			      ((MT MT) (MA MA)))))))
)

(encapsulate nil
(local
(defthm MT-rob-index-at-=-MT-rob-head-if-rob-empty-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (b1p (rob-empty? (MA-rob MA)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (rob-index-at sub trace idx) idx))
  :hints (("Goal" :in-theory (enable dispatched-p committed-p)))))

(defthm MT-rob-index-at-=-MT-rob-head-if-rob-empty
    (implies (and (inv MT MA)
		  (b1p (rob-empty? (MA-rob MA)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (equal (MT-rob-head MT) (MT-rob-index-at trace MT)) t))
  :hints (("Goal" :in-theory (enable MT-rob-index-at))))
)

(defun MT-last-robe (MT)
  (if (equal (MT-rob-tail MT) 0) 7 (1- (MT-rob-tail MT))))
(in-theory (disable MT-last-robe))

(defthm rob-index-p-MT-last-robe
    (implies (MAETT-p MT) (rob-index-p (MT-last-robe MT)))
  :hints (("goal" :in-theory (enable MT-last-robe))))

(defthm MT-last-robe-+-1
    (implies (MAETT-p MT) 
	     (equal (rob-index (1+ (MT-last-robe MT))) (MT-rob-tail MT)))
  :hints (("Goal" :in-theory (enable MT-last-robe rob-index))))

(defthm uniq-inst-at-mt-last-robe-if-not-rob-empty
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (rob-empty? (MA-rob MA)))))
	     (uniq-inst-of-tag (MT-last-robe MT) MT))
  :hints (("Goal" :in-theory
		  (e/d (consistent-robe-p rob-empty?
			MT-last-robe equal-b1p-converter lift-b-ops)
		       (CONSISTENT-ROBE-P-NTH-ROBE))
		  :use (:instance CONSISTENT-ROBE-P-NTH-ROBE
				  (rix (MT-last-robe MT))))))

;; Proof of in-order-rob-p-preserved-if-flushed
(defthm not-MT-all-commit-before-execute-if-flush-all
    (implies (and (inv MT MA)
		  (consp trace)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (B1P (FLUSH-ALL? MA SIGS))
		  (EXECUTE-STG-P (INST-STG (CAR TRACE)))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (MT-ALL-COMMIT-BEFORE-TRACE TRACE MT)))
  :hints (("Goal" :in-theory (e/d (flush-all? lift-b-ops)
				  (not-all-commit-before-if-execute-stg-p))
		  :use (:instance not-all-commit-before-if-execute-stg-p
				  (i (car trace))))))

(defthm no-complete-stg-p-step-inst-if-inst-cause-jmp
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA)
		  (complete-stg-p (INST-stg i))
		  (b1p (INST-cause-jmp? i MT MA sigs)))
	     (not (complete-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("Goal" :in-theory
		  (disable committed-p-step-inst-if-INST-cause-jmp)
		  :use (:instance committed-p-step-inst-if-INST-cause-jmp))))

(defthm in-order-rob-p-preserved-if-flushed
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (in-order-ROB-trace-p trace rix)
		  (MT-all-commit-before-trace trace MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (flush-all? MA sigs)))
	     (in-order-ROB-trace-p (step-trace trace MT MA sigs ISA spc smc)
				   0))
  :hints (("Goal" :in-theory (enable committed-p* ))))

;;; Proof of in-order-rob-p-preserved-if-no-commit
(local
 (defthm in-order-rob-trace-p-mt-rob-head
     (implies (inv MT MA)
	      (in-order-rob-trace-p (MT-trace MT) (MT-rob-head MT)))
   :hints (("Goal" :in-theory (enable inv in-order-rob-p)))))

(local
(defthm rob-index-1+-inst-tag
    (implies (inst-p i)
	     (equal (rob-index (1+ (inst-tag i)))
		    (if (equal (inst-tag i) 7)
			0 (1+ (inst-tag i)))))
  :hints (("Goal" :in-theory (enable rob-index-p unsigned-byte-p)))))
(local (in-theory (disable rob-index-1+-inst-tag)))

(local
 (defthm not-j-lt-i+1-if-i-lt-j
     (implies (and (inv MT MA)
		   (<= (INST-tag i) (INST-tag j))
		   (not (equal i j))
		   (INST-in i MT) (INST-p i)
		   (INST-in j MT) (INST-p j) 
		   (MAETT-p MT) (MA-state-p MA)
		   (not (committed-p i)) (dispatched-p i)
		   (not (committed-p j)) (dispatched-p j))
	      (not (< (INST-tag j) (rob-index (1+ (INST-tag i))))))
   :hints (("Goal" :in-theory (e/d (rob-index-1+-inst-tag)
				   (tag-identity))
		   :use (:instance TAG-IDENTITY)))))

(encapsulate nil
(local
(defthm INST-in-order-inst-of-tag-if-not-rob-flg-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA) 
		  (in-order-rob-trace-p trace rix)
		  (member-equal i trace) (INST-p i)
		  (member-equal j trace) (INST-p j)
		  (not (committed-p i)) (dispatched-p i)
		  (not (committed-p j)) (dispatched-p j)
		  (not (b1p (MT-rob-flg MT)))
		  (<= rix (INST-tag i))
		  (< (INST-tag i) (INST-tag j)))
	     (member-in-order i j trace))
  :hints (("Goal" :in-theory (e/d ( committed-p dispatched-p
						member-in-order*)
				  (INST-IS-AT-ONE-OF-THE-STAGES
				   NOT-COMMITTED-P-IF-NOT-COMMIT-RETIRE)))) 
  :rule-classes nil))

(defthm INST-in-order-inst-of-tag-if-not-rob-flg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j) 
		  (not (committed-p i)) (dispatched-p i)
		  (not (committed-p j)) (dispatched-p j)
		  (not (b1p (MT-rob-flg MT)))
		  (< (INST-tag i) (INST-tag j)))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :use
		  ((:instance INST-in-order-inst-of-tag-if-not-rob-flg-help
			      (trace (MT-trace MT)) (rix (MT-rob-head MT)))
		   (:instance CONSISTENT-ROBE-P-NTH-ROBE
			      (rix (INST-tag i))))
		  :in-theory (e/d (inst-in-order-p INST-in in-order-rob-p
						   consistent-robe-p)
				  (consistent-robe-p-nth-robe)))))
)

(encapsulate nil
(local
 (defthm help-lemma1
     (implies (and (inv MT MA)
		   (<= (INST-tag j) (INST-tag i))
		   (INST-in i MT) (INST-p i)
		   (INST-in j MT) (INST-p j) 
		   (not (equal j i))
		   (<= (MT-rob-tail MT) (INST-tag j))
		   (not (committed-p i)) (dispatched-p i)
		   (not (committed-p j)) (dispatched-p j)
		   (MAETT-p MT) (MA-state-p MA))
	      (not (< (rob-index (+ 1 (INST-tag j)))
		      (MT-rob-tail MT))))
   :hints (("Goal" :in-theory (e/d (rob-index-1+-inst-tag)
				   (tag-identity))
		   :use (:instance tag-identity)))))

(local
(defthm INST-in-order-inst-of-tag-if-rob-flg-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (in-order-rob-trace-p trace rix)
		  (member-equal i trace)
		  (member-equal j trace)
		  (not (committed-p i)) (dispatched-p i)
		  (not (committed-p j)) (dispatched-p j)
		  (MAETT-p MT) (MA-state-p MA) 
		  (b1p (MT-rob-flg MT))
		  (<= rix (INST-tag i))
		  (<= (MT-rob-tail MT) rix)
		  (< (INST-tag j) (MT-rob-tail MT)))
	     (member-in-order i j trace))
  :hints (("Goal" :in-theory (e/d ( committed-p dispatched-p
						member-in-order*)
				  (INST-IS-AT-ONE-OF-THE-STAGES
				   NOT-COMMITTED-P-IF-NOT-COMMIT-RETIRE))))
  :rule-classes nil))

(defthm INST-in-order-inst-of-tag-if-rob-flg
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (INST-in j MT) (INST-p j) 
		  (not (committed-p i)) (dispatched-p i)
		  (not (committed-p j)) (dispatched-p j)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (MT-rob-flg MT))
		  (<= (MT-rob-head MT) (INST-tag i))
		  (< (INST-tag j) (MT-rob-tail MT)))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :use (:instance INST-in-order-inst-of-tag-if-rob-flg-help
				  (trace (MT-trace MT)) (rix (MT-rob-head MT)))
		  :in-theory (enable inst-in
				     inst-in-order-p))))
)

(encapsulate nil
(local
(defthm INST-in-order-inst-of-tag-if-gt-rob-head-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (in-order-rob-trace-p trace rix)
		  (MAETT-p MT) (MA-state-p MA) 
		  (not (committed-p i)) (dispatched-p i)
		  (not (committed-p j)) (dispatched-p j)
		  (member-equal i trace)
		  (member-equal j trace)
		  (<= rix (INST-tag i))
		  (< (INST-tag i) (INST-tag j)))
	     (member-in-order i j trace))
  :hints (("Goal" :in-theory (enable member-in-order* committed-p
				     dispatched-p)))
  :rule-classes nil))

(defthm INST-in-order-inst-of-tag-if-gt-rob-head
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (not (committed-p i)) (dispatched-p i)
		  (not (committed-p j)) (dispatched-p j)
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j) 
		  (<= (MT-rob-head MT) (INST-tag i))
		  (< (INST-tag i) (INST-tag j)))
	     (INST-in-order-p i j MT))
  :Hints (("Goal" :in-theory (enable inst-in INST-in-order-p)
		  :use (:instance
			INST-in-order-inst-of-tag-if-gt-rob-head-help
			(trace (MT-trace MT)) (rix (MT-rob-head MT))))))
)

(encapsulate nil
(local
(defthm rob-index-1+-INST-tag-=-0
    (implies (and (INST-p k) (<= (MT-rob-tail MT) (INST-tag k))
		  (< (rob-index (1+ (INST-tag k))) (MT-rob-tail MT)))
	     (equal (rob-index (1+ (INST-tag k))) 0))
  :hints (("Goal" :in-theory (enable rob-index-1+-inst-tag)))))

(local
(defthm INST-in-order-inst-of-tag-if-le-rob-tail-induct-2
    (implies (and (inv MT MA)
		  (in-order-rob-trace-p trace rix)
		  (MAETT-p MT) (MA-state-p MA) 
		  (<= rix (INST-tag i))
		  (subtrace-p trace MT) (INST-listp trace) 
		  (member-equal i trace) 
		  (member-equal j trace) 
		  (not (committed-p i)) (dispatched-p i)
		  (not (committed-p j)) (dispatched-p j)
		  (< (INST-tag i) (INST-tag j))
		  (< (INST-tag j) (MT-rob-tail MT)))
	     (member-in-order i j trace))
  :hints (("Goal" :in-theory (enable member-in-order* committed-p
				     dispatched-p)))))

(local
(defthm INST-in-order-inst-of-tag-if-le-rob-tail-induct
    (implies (and (inv MT MA)
		  (in-order-rob-trace-p trace rix)
		  (MAETT-p MT) (MA-state-p MA) 
		  (subtrace-p trace MT) (INST-listp trace) 
		  (member-equal i trace)
		  (member-equal j trace)
		  (not (committed-p i)) (dispatched-p i)
		  (not (committed-p j)) (dispatched-p j)
		  (<= (MT-rob-tail MT) rix)
		  (< (INST-tag i) (INST-tag j))
		  (< (INST-tag j) (MT-rob-tail MT)))
	     (member-in-order i j trace))
  :hints (("Goal" :in-theory (enable member-in-order* committed-p
				     dispatched-p)
	          :induct t
		  :expand (IN-ORDER-ROB-TRACE-P TRACE (INST-TAG (CAR TRACE)))))
  :rule-classes nil))

(local
(defthm INST-in-order-inst-of-tag-if-le-rob-tail-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j) 
		  (not (committed-p i)) (dispatched-p i)
		  (not (committed-p j)) (dispatched-p j)
		  (b1p (MT-rob-flg MT))
		  (< (INST-tag i) (INST-tag j))
		  (< (INST-tag j) (MT-rob-tail MT)))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :use (:instance
			INST-in-order-inst-of-tag-if-le-rob-tail-induct
			(trace (MT-trace MT)) (rix (MT-rob-head MT)))
		  :in-theory
		  (e/d (INST-in INST-in-order-p) ())))))

(defthm INST-in-order-inst-of-tag-if-le-rob-tail
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j) 
		  (not (committed-p i)) (dispatched-p i)
		  (not (committed-p j)) (dispatched-p j)
		  (< (INST-tag i) (INST-tag j))
		  (< (INST-tag j) (MT-rob-tail MT)))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :cases ((b1p (MT-rob-flg MT))))))
)

; If ROB index of instruction i and j satisfy tag-in-order,
; instruction i precedes j in program order.
(defthm INST-in-order-inst-of-tag-if-tag-in-order
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (not (committed-p i)) (dispatched-p i)
		  (not (committed-p j)) (dispatched-p j)
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j) 
		  (tag-in-order (INST-tag i) (INST-tag j) MT))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :in-theory (enable tag-in-order))))

(defthm tag-in-order-MT-last-robe
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (rob-index-p rix)
		  (b1p (robe-valid? (nth-robe rix (MA-rob MA))))
		  (not (equal (MT-last-robe MT) rix)))
	     (tag-in-order rix (MT-last-robe MT) MT))
  :hints (("Goal" :in-theory (e/d (tag-in-order MT-last-robe
						consistent-robe-p
						rob-index-p unsigned-byte-p)
				  (CONSISTENT-ROBE-P-NTH-ROBE))
		  :use (:instance CONSISTENT-ROBE-P-NTH-ROBE))))

; The instruction stored in ROB at the entry designated by
; (MT-last-robe MT) is the last instruction in the ROB.
(defthm INST-in-order-inst-of-tag-MT-last-robe
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (rob-index-p rix)
		  (uniq-inst-of-tag rix MT)
		  (not (equal (MT-last-robe MT) rix))
		  (uniq-inst-of-tag (MT-last-robe MT) MT))
	     (inst-in-order-p (inst-of-tag rix MT)
			      (inst-of-tag (MT-last-robe MT) MT)
			      MT))
  :hints (("Goal" :cases ((b1p (robe-valid? (nth-robe rix (MA-rob MA))))))))

(encapsulate nil
(local
(defthm not-undispatched-inst-after-mt-last-robe-help
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j) 
		  (MAETT-p MT) (MA-state-p MA)
		  (or (execute-stg-p (INST-stg i))
		      (complete-stg-p (INST-stg i)))
		  (or (execute-stg-p (INST-stg j))
		      (complete-stg-p (INST-stg j)))
		  (equal (INST-tag i) (MT-last-robe MT)))
	     (not (inst-in-order-p i j MT)))
  :hints (("Goal" :in-theory (disable INST-in-order-inst-of-tag-MT-last-robe)
		  :use (:instance INST-in-order-inst-of-tag-MT-last-robe
				  (rix (INST-tag j)))))))

(defthm not-undispatched-inst-after-mt-last-robe
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (INST-in j MT) (INST-p j) 
		  (MAETT-p MT) (MA-state-p MA) 
		  (dispatched-p j)
		  (equal (INST-tag i) (MT-last-robe MT))
		  (or (execute-stg-p (INST-stg i))
		      (complete-stg-p (INST-stg i))))
	     (not (inst-in-order-p i j MT)))
  :hints (("Goal" :use (:instance inst-is-at-one-of-the-stages (i j))
		  :in-theory (disable inst-is-at-one-of-the-stages)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (INST-in i MT) (INST-p i)
			   (INST-in j MT) (INST-p j) 
			   (MAETT-p MT) (MA-state-p MA) 
			   (inst-in-order-p i j MT)
			   (dispatched-p j)
			   (or (execute-stg-p (INST-stg i))
			       (complete-stg-p (INST-stg i))))
		      (not (equal (INST-tag i) (MT-last-robe MT)))))))
)

(defthm rob-index-at-subtrace-after-last-robe
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (subtrace-p trace MT) (INST-listp trace)
		  (subtrace-after-p i trace MT)
		  (equal (INST-tag i) (MT-last-robe MT))
		  (or (execute-stg-p (INST-stg i))
		      (complete-stg-p (INST-stg i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (rob-index-at sub trace idx) idx))
  :hints (("Goal" :restrict
		  (((:rewrite not-undispatched-inst-after-mt-last-robe . 2)
		    ((j (car trace))))))))
		   
(encapsulate nil
(local
(defthm MT-rob-index-at-MT-rob-tail-if-no-rob-empty-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (tail-p sub trace)
		  (in-order-rob-trace-p trace idx)
		  (uniq-inst-of-tag-in-trace (MT-last-robe MT) trace)
		  (consp sub)
		  (DQ-stg-p (INST-stg (car sub)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (rob-index-at sub trace idx) (MT-rob-tail MT)))
  :Hints (("Goal" :restrict ((rob-index-at-subtrace-after-last-robe
			      ((i (car trace)))))
		  :in-theory (enable committed-p dispatched-p)))))
  
(defthm MT-rob-index-at-MT-rob-tail-if-no-rob-empty
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (consp trace)
		  (not (b1p (rob-empty? (MA-rob MA))))
		  (DQ-stg-p (INST-stg (car trace)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (equal (MT-rob-tail MT) (MT-rob-index-at trace MT)) t))
  :hints (("Goal" :in-theory (enable MT-rob-index-at uniq-inst-of-tag
				     subtrace-p inv in-order-rob-p)
		  :use (:instance uniq-inst-at-mt-last-robe-if-not-rob-empty)
		  :restrict ((MT-rob-index-at-MT-rob-tail-if-no-rob-empty-help
			      ((MA MA) (MT MT)))))))
)

(defthm MT-rob-index-at-MT-rob-tail-if-DQ-stg-car
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (consp trace)
		  (DQ-stg-p (INST-stg (car trace)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (equal (MT-rob-tail MT) (MT-rob-index-at trace MT)) t))
  :hints (("Goal" :cases ((b1p (rob-empty? (MA-rob MA)))))))
		    
(defthm INST-tag-step-inst-when-dispatched
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (DQ-stg-p (INST-stg i))
		  (or (execute-stg-p (INST-stg (step-INST i MT MA sigs)))
		      (complete-stg-p (INST-stg (step-INST i MT MA sigs))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (step-INST i MT MA sigs))
		    (MT-rob-tail MT)))
  :hints (("Goal" :in-theory (enable step-inst-dq-inst step-inst-dq
				     dispatch-inst))))

(encapsulate nil
(local
(defthm not-subtrace-after-if-undispatched-dispatched
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (consp trace) (dispatched-p (car trace))
		  (not (dispatched-p i))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (subtrace-after-p i trace MT)))
  :hints (("Goal" :use (:instance inst-in-order-dispatched-undispatched
				  (i (car trace)) (j i))
		  :in-theory
		  (disable inst-in-order-dispatched-undispatched)))))

(defthm rob-index-at-subtrace-after-undispatched
    (implies (and (inv MT MA)
		  (not (dispatched-p i))
		  (subtrace-after-p i trace MT)
		  (INST-in i MT) (INST-p i) 
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (rob-index-at sub trace rix) rix))
  :hints (("Goal" :in-theory (enable dispatched-p))))
)

(encapsulate nil
(local
(defthm MT-rob-index-at-cdr-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (tail-p sub trace))
	     (equal (rob-index-at (cdr sub) trace rix)
		    (if (and (dispatched-p (car sub))
			     (not (committed-p (car sub))))
			(rob-index (1+ (rob-index-at sub trace rix)))
			(rob-index-at sub trace rix))))
  :hints (("Goal" :in-theory (enable dispatched-p)))))

(defthm MT-rob-index-at-cdr
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MT-rob-index-at (cdr trace) MT)
		    (if (and (dispatched-p (car trace))
			     (not (committed-p (car trace))))
			(rob-index (1+ (MT-rob-index-at trace MT)))
			(MT-rob-index-at trace MT))))
  :hints (("Goal" :in-theory (enable MT-rob-index-at subtrace-p))))

(defthm MT-rob-index-at-cdr-2
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (not (dispatched-p (car trace)))
		      (committed-p (car trace))))
	     (equal (MT-rob-index-at trace MT)
		    (MT-rob-index-at (cdr trace) MT))))

(defthm rob-index-1+-MT-mt-rob-index-at
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (dispatched-p (car trace))
		  (not (committed-p (car trace))))
	     (equal (rob-index (1+ (MT-rob-index-at trace MT)))
		    (MT-rob-index-at (cdr trace) MT))))
)
(in-theory (disable  rob-index-1+-MT-mt-rob-index-at
		     MT-rob-index-at-cdr-2))

; Matt K. mod: Modernize theory-invariant call below.
#|
(theory-invariant
 (not (and (member-equal '(:rewrite MT-rob-index-at-cdr) theory)
	   (or (member-equal '(:rewrite rob-index-1+-MT-mt-rob-index-at)
			     theory)
	       (member-equal '(:rewrite MT-rob-index-at-cdr-2) theory)))))
|#
(theory-invariant
 (not (and (active-runep '(:rewrite MT-rob-index-at-cdr))
	   (or (active-runep '(:rewrite rob-index-1+-MT-mt-rob-index-at))
	       (active-runep '(:rewrite MT-rob-index-at-cdr-2))))))

(defthm complete-stg-p-step-inst-if-not-commit-inst
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (complete-stg-p (INST-stg i))
		  (not (b1p (commit-inst? MA)))
		  (MAETT-p MT) (MA-state-p MA))
	     (complete-stg-p (INST-stg (step-INST i MT MA sigs))))
  :hints (("Goal" :in-theory (enable step-inst-complete-inst
				     step-inst-low-level-functions))))
   
(defthm not-execute-stg-step-inst-if-after-dq-stg
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j) 
		  (MAETT-p MT) (MA-state-p MA)
		  (DQ-stg-p (INST-stg i))
		  (INST-in-order-p i j MT))
	     (not (execute-stg-p (INST-stg (step-inst j MT MA sigs)))))
  :hints (("Goal" :use ((:instance inst-is-at-one-of-the-stages (i j))
			(:instance DQ-stg-index-monotonic))
		  :in-theory (e/d (step-inst-dq-inst
				   step-inst-low-level-functions)
				  (inst-is-at-one-of-the-stages)))))

(defthm not-complete-stg-step-inst-if-after-dq-stg
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j) 
		  (MAETT-p MT) (MA-state-p MA)
		  (DQ-stg-p (INST-stg i))
		  (INST-in-order-p i j MT))
	     (not (complete-stg-p (INST-stg (step-inst j MT MA sigs)))))
  :hints (("Goal" :use ((:instance inst-is-at-one-of-the-stages (i j))
			(:instance DQ-stg-index-monotonic))
		  :in-theory (e/d (step-inst-dq-inst
				   step-inst-low-level-functions)
				  (inst-is-at-one-of-the-stages)))))

(local
 (defthm in-order-rob-p-preserved-if-no-commit-help
     (implies (and (inv MT MA)
		   (DQ-stg-p (INST-stg i))
		   (subtrace-after-p i trace MT)
		   (INST-in i MT) (INST-p i) 
		   (subtrace-p trace MT) (INST-listp trace) 
		   (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	      (in-order-rob-trace-p (step-trace trace MT MA sigs
						ISA spc smc)
				    count))
   :hints (("Goal" :in-theory (disable INST-IS-AT-ONE-OF-THE-STAGES)))))
     

(defthm in-order-rob-p-preserved-if-no-commit
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (commit-inst? MA))))
	     (in-order-ROB-trace-p (step-trace trace MT MA sigs ISA spc smc)
				   (MT-rob-index-at trace MT)))
  :hints (("goal" :in-theory (enable DISPATCHED-P
				     committed-p))
	  (when-found (COMPLETE-STG-P (INST-STG (STEP-INST (CAR TRACE)
							   MT MA SIGS)))
		      (:cases ((DQ-stg-p (INST-stg (car trace))))))
	  (when-found (execute-STG-P (INST-STG (STEP-INST (CAR TRACE)
							  MT MA SIGS)))
		      (:cases ((DQ-stg-p (INST-stg (car trace)))))))
  :rule-classes nil)

;;; Proof of in-order-rob-p-preserved-if-commit-inst
(encapsulate nil
(local
(defthm mt-all-commit-before-cdr-if-car-is-not-commit-help
    (implies (and (consp sub) (tail-p sub trace)(INST-listp sub)
		  (not (committed-p (car sub))))
	     (not (trace-all-commit-before-trace (cdr sub) trace)))))

(defthm mt-all-commit-before-cdr-if-car-is-not-commit
    (implies (and (consp trace) (subtrace-p trace MT) (INST-listp trace)
		  (not (committed-p (car trace))))
	     (not (MT-all-commit-before-trace (cdr trace) MT)))
  :hints (("Goal" :in-theory (enable subtrace-p MT-all-commit-before-trace))))
)

(defthm not-MT-all-commit-before-DQ-if-commit-inst
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (DQ-stg-p (INST-stg i))
		  (b1p (commit-inst? MA))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (MT-all-commit-before i MT)))
  :hints (("goal" :cases ((uniq-inst-of-tag (MT-rob-head MT) MT)))
	  ("subgoal 1" :use (:instance
			     no-commit-inst-precedes-if-all-commit-before
			     (i i) (j (inst-of-tag (MT-rob-head MT) MT)))
		      :in-theory
		      (disable no-commit-inst-precedes-if-all-commit-before))))

(defthm not-MT-all-commit-before-execute-if-commit-inst
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (execute-stg-p (INST-stg i))
		  (b1p (commit-inst? MA))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (MT-all-commit-before i MT)))
  :hints (("goal" :cases ((uniq-inst-of-tag (MT-rob-head MT) MT)))
	  ("subgoal 1" :use
		       ((:instance
			 no-commit-inst-precedes-if-all-commit-before
			 (i i) (j (inst-of-tag (MT-rob-head MT) MT)))
			(:instance UNCOMMITTED-INST-P-IS-AFTER-MT-ROB-HEAD))
		       :in-theory
		       (disable no-commit-inst-precedes-if-all-commit-before
				UNCOMMITTED-INST-P-IS-AFTER-MT-ROB-HEAD))))

(defthm not-execute-stg-step-inst-if-MT-all-commit-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (b1p (commit-inst? MA))
		  (MT-all-commit-before i MT)
		  (MAETT-p MT) (MA-state-p MA)) 
	     (not (execute-stg-p (INST-stg (step-inst i MT MA sigs)))))
  :hints (("Goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (disable inst-is-at-one-of-the-stages))))

(defthm not-complete-stg-step-inst-if-MT-all-commit-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (b1p (commit-inst? MA))
		  (MT-all-commit-before i MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (not (complete-stg-p (INST-stg (step-inst i MT MA sigs)))))
  :hints (("Goal" :use
	      ((:instance inst-is-at-one-of-the-stages)
	       (:instance UNCOMMITTED-INST-P-IS-AFTER-MT-ROB-HEAD)
	       (:instance RETIRE-INST-STG-STEP-INST-IF-COMPLETE-ROBE-IS-HEAD))
	      :in-theory
	      (e/d (committed-p)
		   (RETIRE-INST-STG-STEP-INST-IF-COMPLETE-ROBE-IS-HEAD
		    inst-is-at-one-of-the-stages)))))

(defthm MT-all-commit-before-inst-commit
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (b1p (INST-commit? i MA))
		  (MAETT-p MT) (MA-state-p MA))
	     (MT-all-commit-before i MT))
  :hints (("Goal" :in-theory (enable INST-commit? lift-b-ops))))

(defthm complete-stg-p-step-inst-if-not-MT-all-commit-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (MT-all-commit-before i MT))
		  (complete-stg-p (INST-stg i))
		  (MAETT-p MT) (MA-state-p MA))
	     (complete-stg-p (INST-stg (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (enable step-inst-complete-inst
				     lift-b-ops
				     step-inst-low-level-functions))))

(encapsulate nil
(local
 (defthm in-order-rob-trace-p-cons-IFU
     (implies (IFU-stg-p (INST-stg i))
	      (in-order-rob-trace-p (cons (step-inst i MT MA sigs)
					  (step-trace trace mt ma sigs
						      isa spc smc))
				    count))
   :hints (("Goal" :expand
		   (in-order-rob-trace-p (cons (step-inst i MT MA sigs)
					       (step-trace trace mt ma sigs
							   isa spc smc))
					 count)))))

(local
(defthm in-order-rob-p-preserved-induction3-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (equal rix (MT-rob-index-at trace MT))
		  (in-order-rob-trace-p trace (MT-rob-index-at trace MT))
		  (not (MT-all-commit-before-trace trace MT))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (commit-inst? MA)))
	     (in-order-ROB-trace-p (step-trace trace MT MA sigs ISA spc smc)
				   (MT-rob-index-at trace MT)))
  :hints (("goal" :in-theory (e/d (DISPATCHED-P committed-p)
				  (ROBE-AT-HEAD-IF-MT-ALL-COMMIT-BEFORE)))
	  (when-found (COMPLETE-STG-P (INST-STG (STEP-INST (CAR TRACE)
							   MT MA SIGS)))
		      (:cases ((DQ-stg-p (INST-stg (car trace))))))
	  (when-found (execute-STG-P (INST-STG (STEP-INST (CAR TRACE)
							  MT MA SIGS)))
		      (:cases ((DQ-stg-p (INST-stg (car trace)))))))))

(defthm in-order-rob-p-preserved-if-commit-inst
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)   
		  (in-order-rob-trace-p trace (MT-rob-index-at trace MT))
		  (MT-all-commit-before-trace trace MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (commit-inst? MA)))
     (in-order-ROB-trace-p (step-trace trace MT MA sigs ISA spc smc)
			   (rob-index (+ 1 (MT-rob-index-at trace MT)))))
  :hints (("Goal" :in-theory (e/d (COMMITTED-P dispatched-p
					       MT-rob-index-at-cdr-2
					       ROB-INDEX-1+-MT-MT-ROB-INDEX-AT)
				  (IN-ORDER-ROB-TRACE-P-MT-ROB-HEAD
				   MT-rob-index-at-cdr)))
	  (when-found (FETCH-INST? MA SIGS)
		      (:in-theory (e/d (committed-p dispatched-p) ())))
	  (when-found-multiple ((MT-ROB-INDEX-AT (CDR TRACE) MT)
				(MT-ROB-INDEX-AT TRACE MT))
			       (:cases ((committed-p (car trace))
					(not (dispatched-p (car trace))))))
	  (when-found-multiple ((EXECUTE-STG-P (INST-STG (CAR TRACE)))
				(COMPLETE-STG-P (INST-STG (CAR TRACE)))
				(COMMIT-STG-P (INST-STG (CAR TRACE)))
				(RETIRE-STG-P (INST-STG (CAR TRACE))))
			       (:cases ((dq-stg-p (INST-stg (car trace)))
					(IFU-stg-p (INST-stg (car trace)))))))
  :rule-classes nil)
)

(defthm in-order-rob-p-preserved
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (in-order-ROB-p (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (e/d (in-order-rob-p MT-step
						  step-MT-rob-head
						  inv)
				  (in-order-rob-trace-p step-trace))
		  :use ((:instance in-order-rob-p-preserved-if-no-commit
				   (trace (MT-trace MT))
				   (ISA (MT-init-ISA MT))
				   (spc 0) (smc 0))
			(:instance in-order-rob-p-preserved-if-commit-inst
				   (trace (MT-trace MT))
				   (ISA (MT-init-ISA MT))
				   (spc 0) (smc 0))))))
		  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Proof about in-order-LSU-inst-p
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Proof of in-order-LSU-inst-p for initial states.
(defthm in-order-LSU-inst-p-init-MT
    (in-order-LSU-inst-p (init-MT MA) MA)
  :hints (("goal" :in-theory (enable init-MT in-order-LSU-inst-p
				     IN-ORDER-LOAD-STORE-P))))

;;;; Invariant proof
(defthm wbuf-stg-p*
    (equal (wbuf-stg-p stg)
	   (or (wbuf0-stg-p stg) (wbuf1-stg-p stg)))
  :hints (("goal" :in-theory (enable wbuf-stg-p wbuf0-stg-p wbuf1-stg-p)))
  :rule-classes :definition)
  

(defthm not-wbuf0-stg-p-new-dq-stage
    (not (wbuf0-stg-p (new-DQ-stage MT MA)))
  :hints (("Goal" :in-theory (enable new-DQ-stage wbuf0-stg-p))))

(defthm not-wbuf1-stg-p-new-dq-stage
    (not (wbuf1-stg-p (new-dq-stage mt ma)))
  :hints (("Goal" :in-theory (enable new-DQ-stage wbuf1-stg-p))))

(defthm not-wbuf0-stg-p-step-inst-if-not-LSU-RS
    (implies (and (INST-p i)
		  (not (equal (INST-stg i) '(LSU RS0)))
		  (not (equal (INST-stg i) '(LSU RS1)))
		  (not (wbuf0-stg-p (INST-stg i)))
		  (not (wbuf1-stg-p (INST-stg i))))
	     (not (wbuf0-stg-p (INST-stg (step-inst i MT MA sigs)))))
  :hints (("Goal" :in-theory (enable wbuf0-stg-p wbuf1-stg-p
				     complete-stg-p
				     commit-stg-p execute-stg-p
				     BU-stg-p MU-stg-p LSU-stg-p
				     step-inst-execute-inst
				     step-inst-low-level-functions 
				     IU-stg-p inst-stg-step-inst)
; Matt K. mod: add :expand hint.
                  :expand ((step-inst i MT MA sigs))
		  :use ((:instance inst-is-at-one-of-the-stages)))))

(defthm not-wbuf0-stg-p-step-inst-if-not-execute-stg
    (implies (and (INST-p i)
		  (not (execute-stg-p (INST-stg i)))
		  (not (wbuf0-stg-p (INST-stg i)))
		  (not (wbuf1-stg-p (INST-stg i))))
	     (not (wbuf0-stg-p (INST-stg (step-inst i MT MA sigs)))))
  :hints (("Goal" :in-theory (enable execute-stg-p LSU-stg-p))))

(defthm not-wbuf1-stg-p-step-inst-if-not-LSU-RS
    (implies (and (INST-p i)
		  (not (equal (INST-stg i) '(LSU RS0)))
		  (not (equal (INST-stg i) '(LSU RS1)))
		  (not (wbuf1-stg-p (INST-stg i))))
	     (not (wbuf1-stg-p (INST-stg (step-inst i MT MA sigs)))))
  :hints (("Goal" :in-theory (enable wbuf1-stg-p
				     complete-stg-p
				     commit-stg-p execute-stg-p
				     BU-stg-p MU-stg-p LSU-stg-p
				     step-inst-execute-inst
				     step-inst-low-level-functions 
				     IU-stg-p inst-stg-step-inst)
; Matt K. mod: add :expand hint.
                  :expand ((step-inst i MT MA sigs))
		  :use ((:instance inst-is-at-one-of-the-stages)))))

(defthm not-wbuf1-stg-p-step-inst-if-not-execute-stg
    (implies (and (INST-p i)
		  (not (execute-stg-p (INST-stg i)))
		  (not (wbuf1-stg-p (INST-stg i))))
	     (not (wbuf1-stg-p (INST-stg (step-inst i MT MA sigs)))))
  :hints (("Goal" :in-theory (enable execute-stg-p LSU-stg-p))))

(local
(defthm not-simultaneous-issue-to-wbuf0-wbuf1
    (implies (and (inv MT MA)
		  (wbuf0-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (or (equal (INST-stg i) '(LSU RS0))
		      (equal (INST-stg i) '(LSU RS1)))
		  (or (equal (INST-stg j) '(LSU RS0))
		      (equal (INST-stg j) '(LSU RS1))))
	     (not (wbuf1-stg-p (INST-stg (step-INST j MT MA sigs)))))
  :hints (("Goal" :in-theory (enable step-inst-execute-inst
				     step-inst-low-level-functions)))))

(defthm not-both-inst-at-wbuf-after-step-inst
    (implies (and (inv MT MA)
		  (wbuf0-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j) 
		  (MAETT-p MT) (MA-state-p MA)
		  (not (wbuf-stg-p (INST-stg i)))
		  (not (wbuf-stg-p (INST-stg j))))
	     (not (wbuf1-stg-p (INST-stg (step-INST j MT MA sigs)))))
  :hints (("goal" :in-theory (e/d (execute-stg-p BU-stg-p
						 IU-stg-p MU-stg-p LSU-stg-p )
				  (inst-is-at-one-of-the-stages))
		  :use ((:instance inst-is-at-one-of-the-stages)
			(:instance inst-is-at-one-of-the-stages (i j))))))

(defthm not-wbuf1-stg-step-inst-if-wbuf0-stg
    (implies (and (INST-p i) (wbuf0-stg-p (INST-stg i)))
	     (not (wbuf1-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("Goal" :in-theory (enable wbuf0-stg-p))))

(defthm inst-in-order-wbuf0-wbuf1-step-inst-help1
    (implies (and (inv MT MA)
		  (wbuf1-stg-p (INST-stg j))
		  (INST-in i MT) (INST-p i) 
		  (INST-in j MT) (INST-p j) 
		  (MAETT-p MT) (MA-state-p MA) 
		  (not (wbuf-stg-p (INST-stg i))))
	     (not (wbuf0-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("Goal" :in-theory (e/d (execute-stg-p LSU-stg-p BU-stg-p
 				   INST-SELECT-WBUF0? lift-b-ops
				   inst-stg-step-inst MU-stg-p IU-stg-p)
				   (inst-is-at-one-of-the-stages))
		  :use (:instance inst-is-at-one-of-the-stages))))

(defthm inst-in-order-wbuf0-wbuf1-step-inst-help2
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (INST-in j MT) (INST-p j)
		  (wbuf-stg-p (INST-stg i))
		  (not (wbuf-stg-p (INST-stg j)))
		  (wbuf1-stg-p (INST-stg (step-inst j MT MA sigs))))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :in-theory (e/d (wbuf-stg-p* wbuf0-stg-p wbuf1-stg-p
					       INST-IN-ORDER-P-LSU-ISSUED-RS)
				  (not-wbuf1-stg-p-step-inst-if-not-LSU-RS))
		  :use (:instance not-wbuf1-stg-p-step-inst-if-not-LSU-RS
				  (i j)))))

(defthm inst-in-order-wbuf0-wbuf1-step-inst-help3
    (implies (and (inv MT MA)
		  (wbuf0-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (wbuf1-stg-p (INST-stg i))
		  (wbuf1-stg-p (INST-stg j)))
	     (not (wbuf1-stg-p (INST-stg (step-INST j MT MA sigs)))))
  :hints (("Goal" :in-theory (enable inst-stg-step-inst lift-b-ops
				     wbuf1-stg-p wbuf0-stg-p
				     RELEASE-WBUF0?))))
		   
(defthm inst-in-order-wbuf0-wbuf1-step-inst
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (MAETT-p MT) (MA-state-p MA) 
		  (wbuf0-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (wbuf1-stg-p (INST-stg (step-INST j MT MA sigs))))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :cases ((wbuf0-stg-p (INST-stg i))
			  (wbuf1-stg-p (INST-stg i)))
		  :in-theory (enable wbuf-stg-p* INST-IN-ORDER-P-WBUF0-WBUF1)
		  :restrict ((inst-in-order-wbuf0-wbuf1-step-inst-help1
			      ((j j)))))
	  (use-hint-always (:cases ((wbuf0-stg-p (INST-stg j))
				    (wbuf1-stg-p (INST-stg j))))))
  :rule-classes
  ((:rewrite :corollary
     (implies (and (inv MT MA)
		   (wbuf1-stg-p (INST-stg (step-INST j MT MA sigs)))
		   (INST-in i MT) (INST-p i)
		   (INST-in j MT) (INST-p j) 
		   (MAETT-p MT) (MA-state-p MA) 
		   (INST-in-order-p j i MT))
	      (not (wbuf0-stg-p (INST-stg (step-INST i MT MA sigs))))))))

(encapsulate nil
(local
(defthm in-order-wb-trace-p-mt-trace-MT-step-help
    (implies (and (inv MT MA)
		  (subtrace-after-p i trace MT)
		  (INST-in i MT) (INST-p i)
		  (subtrace-p trace MT) (INST-listp trace)
		  (wbuf1-stg-p (INST-stg (step-inst i MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA))
	     (no-inst-at-wbuf0-p (step-trace trace MT MA sigs ISA spc smc)))))

(defthm in-order-wb-trace-p-mt-trace-MT-step
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA))
	     (in-order-wb-trace-p (step-trace trace MT MA sigs ISA spc smc)))
  :hints (("Goal" :restrict ((in-order-wb-trace-p-mt-trace-MT-step-help
			      ((i (car trace))))))))
)

(defthm not-simultaneous-issue-to-wbuf0-rbuf
    (implies (and (inv MT MA)
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (or (equal (INST-stg i) '(LSU RS0))
		      (equal (INST-stg i) '(LSU RS1)))
		  (or (equal (INST-stg j) '(LSU RS0))
		      (equal (INST-stg j) '(LSU RS1))))
	     (not (wbuf0-stg-p (INST-stg (step-INST j MT MA sigs)))))
  :hints (("Goal" :in-theory (enable step-inst-execute-inst lift-b-ops
				     step-inst-low-level-functions
				     LSU-RS0-ISSUE-READY?
				     LSU-RS1-ISSUE-READY?
				     ISSUE-LSU-RS0? ISSUE-LSU-RS1?))))

(defthm not-simultaneous-issue-to-wbuf1-rbuf
    (implies (and (inv MT MA)
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (or (equal (INST-stg i) '(LSU RS0))
		      (equal (INST-stg i) '(LSU RS1)))
		  (or (equal (INST-stg j) '(LSU RS0))
		      (equal (INST-stg j) '(LSU RS1))))
	     (not (wbuf1-stg-p (INST-stg (step-INST j MT MA sigs)))))
  :hints (("Goal" :in-theory (enable step-inst-execute-inst lift-b-ops
				     step-inst-low-level-functions
				     LSU-RS0-ISSUE-READY?
				     LSU-RS1-ISSUE-READY?
				     ISSUE-LSU-RS0? ISSUE-LSU-RS1?))))

(defthm rbuf-wbuf0-step-LSU-off-if-wbuf0-issued
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))
		  (equal (INST-stg i) '(LSU rbuf))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (or (equal (INST-stg j) '(LSU RS0))
		      (equal (INST-stg j) '(LSU RS1)))
		  (b1p (rbuf-wbuf0? (LSU-rbuf (step-LSU MA sigs)))))
	     (not (wbuf0-stg-p (INST-stg (step-INST j MT MA sigs)))))
  :hints (("Goal" :in-theory (enable step-inst-execute-inst
				     step-LSU step-rbuf lift-b-ops
				     RELEASE-RBUF?
				     ISSUE-LSU-RS1? ISSUE-LSU-RS0?
				     LSU-RS0-ISSUE-READY?
				     LSU-RS1-ISSUE-READY?
				     INST-SELECT-WBUF0?
				     RELEASE-WBUF0?
				     step-inst-low-level-functions)))) 

(defthm INST-in-order-wbuf0-rbuf-step-INST-help1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (not (wbuf-stg-p (INST-stg j)))
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))
		  (wbuf0-stg-p (INST-stg (step-INST j MT MA sigs)))
		  (b1p (rbuf-wbuf0? (LSU-rbuf (step-LSU MA sigs)))))
	     (INST-in-order-p j i MT))
  :hints (("Goal" :use ((:instance stages-reachable-to-LSU-rbuf)
			(:instance not-wbuf0-stg-p-step-inst-if-not-LSU-RS
				   (i j)))
		  :in-theory (e/d (INST-IN-ORDER-P-LSU-ISSUED-RS)
				  (not-wbuf0-stg-p-step-inst-if-not-LSU-RS)))))

(defthm LSU-rbuf-wbuf0-step-LSU
    (implies (and (b1p (rbuf-valid? (LSU-rbuf (MA-LSU MA))))
		  (not (b1p (release-rbuf? (MA-LSU MA) MA sigs))))
	     (equal (rbuf-wbuf0? (LSU-rbuf (step-LSU MA sigs)))
		    (rbuf-wbuf0? (LSU-rbuf (MA-LSU MA)))))
  :hints (("Goal" :in-theory (enable step-LSU step-rbuf lift-b-ops))))

(defthm INST-in-order-wbuf0-rbuf-step-INST-help2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (wbuf0-stg-p (INST-stg j))
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))
		  (wbuf0-stg-p (INST-stg (step-INST j MT MA sigs)))
		  (b1p (rbuf-wbuf0? (LSU-rbuf (step-LSU MA sigs)))))
	     (INST-in-order-p j i MT))
  :hints (("Goal" :use ((:instance stages-reachable-to-LSU-rbuf))
		  :restrict ((LSU-RBUF-VALID-IF-INST-IN ((i i)))
			     (INST-IN-ORDER-P-WBUF0-RBUF ((i j) (j i))))
		  :in-theory (e/d (INST-IN-ORDER-P-LSU-ISSUED-RS
				   INST-IN-ORDER-P-WBUF0-RBUF
				   INST-stg-step-inst
				   wbuf0-stg-p lift-b-ops)
				  ()))))

(defthm INST-in-order-wbuf0-rbuf-step-INST-help3
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (wbuf1-stg-p (INST-stg j))
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))
		  (wbuf0-stg-p (INST-stg (step-INST j MT MA sigs)))
		  (b1p (rbuf-wbuf0? (LSU-rbuf (step-LSU MA sigs)))))
	     (INST-in-order-p j i MT))
  :hints (("Goal" :use ((:instance stages-reachable-to-LSU-rbuf))
		  :restrict ((LSU-RBUF-VALID-IF-INST-IN ((i i)))
			     (INST-IN-ORDER-P-WBUF1-RBUF ((i j) (j i))))
		  :in-theory (e/d (INST-IN-ORDER-P-LSU-ISSUED-RS
				   INST-IN-ORDER-P-WBUF0-RBUF
				   INST-IN-ORDER-P-WBUF1-RBUF
				   RELEASE-WBUF0?
				   INST-stg-step-inst wbuf1-stg-p
				   wbuf0-stg-p lift-b-ops)
				  ()))))

(defthm INST-in-order-wbuf0-rbuf-step-INST
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))
		  (wbuf0-stg-p (INST-stg (step-INST j MT MA sigs)))
		  (b1p (rbuf-wbuf0? (LSU-rbuf (step-LSU MA sigs)))))
	     (INST-in-order-p j i MT))
  :hints (("Goal" :cases ((wbuf0-stg-p (INST-stg j))
			  (wbuf1-stg-p (INST-stg j)))))
  :rule-classes
  ((:rewrite :corollary
     (implies (and (inv MT MA)
		   (equal (INST-stg (step-INST i MT MA sigs))
			  '(LSU rbuf))
		   (INST-in i MT) (INST-p i)
		   (INST-in j MT) (INST-p j)
		   (b1p (rbuf-wbuf0? (LSU-rbuf (step-LSU MA sigs))))
		   (INST-in-order-p i j MT)
		   (MAETT-p MT) (MA-state-p MA))
	      (not (wbuf0-stg-p (INST-stg (step-INST j MT MA sigs))))))))

(encapsulate nil
(local  
(defthm in-order-wbuf0-rbuf-step-trace-help
    (implies (and (inv MT MA)
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))
		  (INST-in i MT) (INST-p i) 
		  (subtrace-p trace MT) (INST-listp trace) 
		  (subtrace-after-p i trace MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (rbuf-valid? (LSU-rbuf (step-LSU MA sigs))))
		  (b1p (rbuf-wbuf0? (LSU-rbuf (step-LSU MA sigs))))
		  (b1p (wbuf-valid? (LSU-wbuf0 (step-LSU MA sigs)))))
	     (no-inst-at-wbuf0-p (step-trace trace MT MA sigs ISA spc smc)))))

(defthm in-order-wbuf0-rbuf-step-trace
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (rbuf-valid? (LSU-rbuf (step-LSU MA sigs))))
		  (b1p (rbuf-wbuf0? (LSU-rbuf (step-LSU MA sigs))))
		  (b1p (wbuf-valid? (LSU-wbuf0 (step-LSU MA sigs)))))
     (in-order-wbuf0-rbuf-p (step-trace trace MT MA sigs ISA spc smc))))
)

(defthm in-order-rbuf-wbuf0-step-inst-help1
    (implies (and (inv MT MA)
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))
		  (wbuf0-stg-p (INST-stg (step-INST j MT MA sigs)))
		  (not (wbuf-stg-p (INST-stg j)))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (not (b1p (rbuf-wbuf0? (LSU-rbuf (step-LSU MA sigs))))))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :use ((:instance stages-reachable-to-LSU-rbuf)
			(:instance not-wbuf0-stg-p-step-inst-if-not-LSU-RS
				   (i j)))
		  :in-theory (e/d (INST-IN-ORDER-P-LSU-ISSUED-RS)
				  (not-wbuf0-stg-p-step-inst-if-not-LSU-RS)))))

(defthm rbuf-wbuf0-step-LSU-unchanged-if-load-not-released
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))
		  (wbuf0-stg-p (INST-stg (step-INST j MT MA sigs)))
		  (wbuf0-stg-p (INST-stg j))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (equal (INST-stg i) '(LSU rbuf)))
	     (equal (rbuf-wbuf0? (LSU-rbuf (step-LSU MA sigs)))
		    (rbuf-wbuf0? (LSU-rbuf (MA-LSU MA)))))
  :hints (("Goal" :in-theory (enable step-LSU step-rbuf lift-b-ops
				     inst-stg-step-inst wbuf0-stg-p)
		  :restrict ((LSU-RBUF-VALID-IF-INST-IN ((i i)))))))

(defthm rbuf-wbuf0-step-LSU-on-if-wbuf0-not-released
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))
		  (wbuf0-stg-p (INST-stg (step-INST j MT MA sigs)))
		  (wbuf0-stg-p (INST-stg j))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (or (equal (INST-stg i) '(LSU RS0))
		      (equal (INST-stg i) '(LSU RS1))))
	     (equal (rbuf-wbuf0? (LSU-rbuf (step-LSU MA sigs))) 1))
  :hints (("Goal" :in-theory (enable step-LSU step-rbuf lift-b-ops
				     ISSUE-LSU-RS0? ISSUE-LSU-RS1?
				     RELEASE-WBUF0? RELEASE-WBUF0-READY?
				     inst-stg-step-inst wbuf0-stg-p))))

(defthm in-order-rbuf-wbuf0-step-inst-help2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))
		  (wbuf0-stg-p (INST-stg (step-INST j MT MA sigs)))
		  (wbuf0-stg-p (INST-stg j))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (not (b1p (rbuf-wbuf0? (LSU-rbuf (step-LSU MA sigs))))))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :use ((:instance stages-reachable-to-LSU-rbuf))
		  :restrict ((LSU-RBUF-VALID-IF-INST-IN ((i i)))
			     (INST-IN-ORDER-P-LSU-ISSUED-RS ((i j) (j i)))
			     (INST-IN-ORDER-P-RBUF-WBUF0 ((i i) (j j))))
		  :in-theory (e/d (INST-IN-ORDER-P-LSU-ISSUED-RS
				   INST-IN-ORDER-P-RBUF-WBUF0)
				  ()))))

(defthm wbuf1-not-advance-if-rbuf-inst-in
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (wbuf1-stg-p (INST-stg j))
		  (equal (INST-stg i) '(LSU rbuf))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j))
	     (not (wbuf0-stg-p (INST-stg (step-INST j MT MA sigs)))))
  :hints (("Goal" :in-theory (enable inst-stg-step-inst
				     wbuf1-stg-p RELEASE-WBUF0?
				     RELEASE-WBUF0-READY?
				     lift-b-ops)
		  :restrict ((LSU-RBUF-VALID-IF-INST-IN ((i i)))))))

(defthm rbuf-wbuf0-step-LSU-on-if-wbuf1-advance
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))
		  (wbuf0-stg-p (INST-stg (step-INST j MT MA sigs)))
		  (wbuf1-stg-p (INST-stg j))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (or (equal (INST-stg i) '(LSU RS0))
		      (equal (INST-stg i) '(LSU RS1))))
	     (equal (rbuf-wbuf0? (LSU-rbuf (step-LSU MA sigs))) 1))
  :hints (("Goal" :in-theory (enable step-LSU step-rbuf lift-b-ops
				     wbuf1-stg-p RELEASE-WBUF0?
				     inst-stg-step-inst))))

(defthm in-order-rbuf-wbuf0-step-inst-help3
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))
		  (wbuf0-stg-p (INST-stg (step-INST j MT MA sigs)))
		  (wbuf1-stg-p (INST-stg j))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (not (b1p (rbuf-wbuf0? (LSU-rbuf (step-LSU MA sigs))))))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :use ((:instance stages-reachable-to-LSU-rbuf))
		  :restrict ((LSU-RBUF-VALID-IF-INST-IN ((i i)))
			     (INST-IN-ORDER-P-LSU-ISSUED-RS ((i j) (j i)))
			     (INST-IN-ORDER-P-RBUF-WBUF0 ((i i) (j j)))
			     (wbuf1-not-advance-if-rbuf-inst-in ((i i))))
		  :in-theory (e/d (INST-IN-ORDER-P-LSU-ISSUED-RS
				   INST-IN-ORDER-P-RBUF-WBUF0)
				  ()))))

(defthm in-order-rbuf-wbuf0-step-inst
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))
		  (wbuf0-stg-p (INST-stg (step-INST j MT MA sigs)))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (not (b1p (rbuf-wbuf0? (LSU-rbuf (step-LSU MA sigs))))))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :cases ((wbuf0-stg-p (INST-stg j))
			  (wbuf1-stg-p (INST-stg j)))
		  :in-theory (enable wbuf-stg-p*)))
  :rule-classes 
  ((:rewrite :corollary
     (implies (and (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA) 
		   (equal (INST-stg (step-INST i MT MA sigs))
			  '(LSU rbuf))
		   (INST-in i MT) (INST-p i)
		   (INST-in j MT) (INST-p j)
		   (INST-in-order-p j i MT)
		   (not (b1p (rbuf-wbuf0? (LSU-rbuf (step-LSU MA sigs))))))
	      (not (wbuf0-stg-p (INST-stg (step-INST j MT MA sigs))))))))

(encapsulate nil
(local
(defthm in-order-rbuf-wbuf0-step-trace-help
    (implies (and (inv MT MA)
		  (wbuf0-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (INST-in i MT) (INST-p i)  
		  (subtrace-p trace MT) (INST-listp trace) 
		  (subtrace-after-p i trace MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (rbuf-valid? (LSU-rbuf (step-LSU MA sigs))))
		  (not (b1p (rbuf-wbuf0? (LSU-rbuf (step-LSU MA sigs)))))
		  (b1p (wbuf-valid? (LSU-wbuf0 (step-LSU MA sigs)))))
     (no-inst-at-stg-in-trace '(LSU rbuf)
			      (step-trace trace MT MA sigs ISA spc smc)))))

(defthm in-order-rbuf-wbuf0-step-trace
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (rbuf-valid? (LSU-rbuf (step-LSU MA sigs))))
		  (not (b1p (rbuf-wbuf0? (LSU-rbuf (step-LSU MA sigs)))))
		  (b1p (wbuf-valid? (LSU-wbuf0 (step-LSU MA sigs)))))
     (in-order-rbuf-wbuf0-p (step-trace trace MT MA sigs ISA spc smc))))
)

(defthm LSU-rbuf-wbuf1-step-LSU
    (implies (and (b1p (rbuf-valid? (LSU-rbuf (MA-LSU MA))))
		  (not (b1p (release-rbuf? (MA-LSU MA) MA sigs))))
	     (equal (rbuf-wbuf1? (LSU-rbuf (step-LSU MA sigs)))
		    (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA)))))
  :hints (("Goal" :in-theory (enable step-LSU step-rbuf lift-b-ops))))

(defthm INST-in-order-wbuf1-rbuf-step-inst-help1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (INST-in j MT) (INST-p j) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (wbuf1-stg-p (INST-stg i)))
		  (equal (INST-stg (step-inst j MT MA sigs))
			 '(LSU rbuf))
		  (wbuf1-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (b1p (rbuf-wbuf1? (LSU-rbuf (step-LSU MA sigs)))))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :use ((:instance stages-reachable-to-LSU-rbuf
				   (i j))
			(:instance not-wbuf1-stg-p-step-inst-if-not-LSU-RS
				   (i i)))
		  :in-theory (e/d (INST-IN-ORDER-P-LSU-ISSUED-RS
				   lift-b-ops ISSUE-LSU-RS0?
				   ISSUE-LSU-RS1?
				   LSU-RS0-ISSUE-READY?
				   LSU-RS1-ISSUE-READY?
				   RELEASE-WBUF0?
				   inst-stg-step-inst)
				  (not-wbuf0-stg-p-step-inst-if-not-LSU-RS)))))

(defthm INST-in-order-wbuf1-rbuf-step-inst-help2
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (INST-in j MT) (INST-p j) 
		  (MAETT-p MT) (MA-state-p MA)
		  (wbuf1-stg-p (INST-stg i))
		  (equal (INST-stg (step-inst j MT MA sigs))
			 '(LSU rbuf))
		  (wbuf1-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (b1p (rbuf-wbuf1? (LSU-rbuf (step-LSU MA sigs)))))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :use ((:instance stages-reachable-to-LSU-rbuf
				   (i j)))
		  :in-theory (enable inst-stg-step-inst WBUF1-STG-P
				     INST-IN-ORDER-P-WBUF1-RBUF
				     INST-IN-ORDER-P-LSU-ISSUED-RS))))

(defthm INST-in-order-wbuf1-rbuf-step-inst
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (INST-in j MT) (INST-p j) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (equal (INST-stg (step-inst j MT MA sigs))
			 '(LSU rbuf))
		  (wbuf1-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (b1p (rbuf-wbuf1? (LSU-rbuf (step-LSU MA sigs)))))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :cases ((wbuf1-stg-p (INST-stg i)))
		  :in-theory (enable wbuf-stg-p*)))
  :rule-classes 
  ((:rewrite :corollary
     (implies (and (inv MT MA)
		   (equal (INST-stg (step-inst j MT MA sigs))
			  '(LSU rbuf))
		   (INST-in i MT) (INST-p i) 
		   (INST-in j MT) (INST-p j) 
		   (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		   (INST-in-order-p j i MT)
		   (b1p (rbuf-wbuf1? (LSU-rbuf (step-LSU MA sigs)))))
	      (not (wbuf1-stg-p (INST-stg (step-INST i MT MA sigs))))))))

(encapsulate nil
(local
(defthm in-order-wbuf1-rbuf-step-trace-help
    (implies (and (inv MT MA)
		  (equal (INST-stg (step-inst i MT MA sigs))
			 '(LSU rbuf))
		  (INST-in i MT) (INST-p i) 
		  (subtrace-p trace MT) (INST-listp trace) 
		  (subtrace-after-p i trace MT)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (b1p (rbuf-valid? (LSU-rbuf (step-LSU MA sigs))))
		  (b1p (rbuf-wbuf1? (LSU-rbuf (step-LSU MA sigs))))
		  (b1p (wbuf-valid? (LSU-wbuf1 (step-LSU MA sigs)))))
	     (no-inst-at-wbuf1-p (step-trace trace MT MA sigs ISA spc smc)))))

(defthm in-order-wbuf1-rbuf-step-trace
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (b1p (rbuf-valid? (LSU-rbuf (step-LSU MA sigs))))
		  (b1p (rbuf-wbuf1? (LSU-rbuf (step-LSU MA sigs))))
		  (b1p (wbuf-valid? (LSU-wbuf1 (step-LSU MA sigs)))))
     (in-order-wbuf1-rbuf-p (step-trace trace MT MA sigs ISA spc smc))))
)

(defthm INST-in-order-rbuf-wbuf1-step-INST-help1
    (implies (and (inv MT MA)
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j) 
		  (MAETT-p MT) (MA-state-p MA)
		  (not (wbuf1-stg-p (INST-stg j)))
		  (wbuf1-stg-p (INST-stg (step-INST j MT MA sigs)))
		  (not (b1p (rbuf-wbuf1? (LSU-rbuf (step-LSU MA sigs))))))
	     (INST-in-order-p i j MT))
  :hints (("Goal"  :use ((:instance stages-reachable-to-LSU-rbuf
				    (i i))
			 (:instance not-wbuf1-stg-p-step-inst-if-not-LSU-RS
				    (i j)))
		   :in-theory (e/d
			       (INST-IN-ORDER-P-LSU-ISSUED-RS)
			       (not-wbuf1-stg-p-step-inst-if-not-LSU-RS)))))

(defthm LSU-rbuf-wbuf1-step-LSU-if-wbuf1-not-advance
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))
		  (wbuf1-stg-p (INST-stg (step-INST j MT MA sigs)))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (wbuf1-stg-p (INST-stg J))
		  (or (equal (INST-stg i) '(LSU RS0))
		      (equal (INST-stg i) '(LSU RS1))))
	     (equal (rbuf-wbuf1? (LSU-rbuf (step-LSU MA sigs))) 1))
  :hints (("Goal" :in-theory (enable step-LSU step-rbuf lift-b-ops
				     ISSUE-LSU-RS0? ISSUE-LSU-RS1?
				     RELEASE-WBUF0?
				     wbuf1-stg-p inst-stg-step-inst))))

(defthm LSU-rbuf-wbuf1-step-LSU-if-rbuf-not-released
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))
		  (wbuf1-stg-p (INST-stg (step-INST j MT MA sigs)))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (wbuf1-stg-p (INST-stg J))
		  (equal (INST-stg i) '(LSU rbuf)))
	     (equal (rbuf-wbuf1? (LSU-rbuf (step-LSU MA sigs)))
		    (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA)))))
  :hints (("Goal" :in-theory (enable step-LSU step-rbuf lift-b-ops
				     LSU-RBUF-VALID-IF-INST-IN
				     inst-stg-step-inst wbuf1-stg-p)
		  :restrict ((LSU-RBUF-VALID-IF-INST-IN ((i i)))))))

(defthm INST-in-order-rbuf-wbuf1-step-INST-help2
    (implies (and (inv MT MA)
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j) 
		  (MAETT-p MT) (MA-state-p MA)
		  (wbuf1-stg-p (INST-stg j))
		  (wbuf1-stg-p (INST-stg (step-INST j MT MA sigs)))
		  (not (b1p (rbuf-wbuf1? (LSU-rbuf (step-LSU MA sigs))))))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :use ((:instance stages-reachable-to-LSU-rbuf
				   (i i)))
		  :in-theory (enable	
			      INST-IN-ORDER-P-RBUF-WBUF1
			      INST-IN-ORDER-P-LSU-ISSUED-RS))))

(defthm INST-in-order-rbuf-wbuf1-step-INST
    (implies (and (inv MT MA)
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU rbuf))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j) 
		  (MAETT-p MT) (MA-state-p MA)
		  (wbuf1-stg-p (INST-stg (step-INST j MT MA sigs)))
		  (not (b1p (rbuf-wbuf1? (LSU-rbuf (step-LSU MA sigs))))))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :cases ((wbuf1-stg-p (INST-stg j)))))
  :rule-classes
  ((:rewrite :corollary
     (implies (and (inv MT MA)
		   (equal (INST-stg (step-INST i MT MA sigs))
			  '(LSU rbuf))
		   (INST-in i MT) (INST-p i)
		   (INST-in j MT) (INST-p j) 
		   (INST-in-order-p j i MT)
		   (MAETT-p MT) (MA-state-p MA)
		   (not (b1p (rbuf-wbuf1? (LSU-rbuf (step-LSU MA sigs))))))
	      (not (wbuf1-stg-p (INST-stg (step-INST j MT MA sigs))))))))

(encapsulate nil
(local
(defthm in-order-rbuf-wbuf1-step-trace-help
    (implies (and (inv MT MA)
		  (wbuf1-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (INST-in i MT) (INST-p i)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (subtrace-after-p i trace MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (rbuf-valid? (LSU-rbuf (step-LSU MA sigs))))
		  (not (b1p (rbuf-wbuf1? (LSU-rbuf (step-LSU MA sigs)))))
		  (b1p (wbuf-valid? (LSU-wbuf1 (step-LSU MA sigs)))))
     (no-inst-at-stg-in-trace '(LSU rbuf)
			      (step-trace trace MT MA sigs ISA spc smc)))))

(defthm in-order-rbuf-wbuf1-step-trace
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (rbuf-valid? (LSU-rbuf (step-LSU MA sigs))))
		  (not (b1p (rbuf-wbuf1? (LSU-rbuf (step-LSU MA sigs)))))
		  (b1p (wbuf-valid? (LSU-wbuf1 (step-LSU MA sigs)))))
     (in-order-rbuf-wbuf1-p (step-trace trace MT MA sigs ISA spc smc))))
)

(defthm in-order-load-store-p-mt-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (in-order-load-store-p (MT-step MT MA sigs) (MA-step MA sigs)))
  :hints (("Goal" :in-theory (enable in-order-load-store-p))))

(in-theory (disable INST-IN-ORDER-RBUF-WBUF1-STEP-INST-HELP2
		    INST-IN-ORDER-RBUF-WBUF1-STEP-INST-HELP1
		    INST-IN-ORDER-WBUF1-RBUF-STEP-INST-HELP2
		    INST-IN-ORDER-WBUF1-RBUF-STEP-INST-HELP1
		    IN-ORDER-RBUF-WBUF0-STEP-INST-HELP3
		    IN-ORDER-RBUF-WBUF0-STEP-INST-HELP2
		    IN-ORDER-RBUF-WBUF0-STEP-INST-HELP1
		    INST-IN-ORDER-WBUF0-RBUF-STEP-INST-HELP3
		    INST-IN-ORDER-WBUF0-RBUF-STEP-INST-HELP2
		    INST-IN-ORDER-WBUF0-RBUF-STEP-INST-HELP1
		    INST-IN-ORDER-WBUF0-WBUF1-STEP-INST-HELP2))

(in-theory (disable INST-IN-ORDER-INST-OF-TAG-IF-ROB-FLG
		    INST-IN-ORDER-INST-OF-TAG-IF-NOT-ROB-FLG
		    INST-IN-ORDER-INST-OF-TAG-IF-TAG-IN-ORDER
		    INST-IN-ORDER-INST-OF-TAG-IF-GT-ROB-HEAD
		    INST-IN-ORDER-INST-OF-TAG-IF-LE-ROB-TAIL
		    INST-IN-ORDER-P-TOTAL
		    DE-VALID-CONSISTENT))

(defthm INST-in-order-p-step-INST-LSU-issued-RS0-help2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg j) '(LSU RS0))
		  (LSU-stg-p (INST-stg i))
		  (equal (INST-stg (step-INST j MT MA sigs)) '(LSU RS0))
		  (LSU-issued-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (INST-in i MT) (INST-p i) 
		  (INST-in j MT) (INST-p j))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :in-theory (enable LSU-stg-p LSU-issued-stg-p
				     INST-IN-ORDER-P-LSU-ISSUED-RS
				     INST-in-order-p-LSU-RS1-RS0
				     ISSUE-LSU-RS0? lift-b-ops
				     LSU-RS0-ISSUE-READY?
				     ISSUE-LSU-RS1?
				     LSU-RS1-ISSUE-READY?
				     inst-stg-step-inst))))

(defthm INST-in-order-p-step-INST-LSU-issued-RS0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg (step-INST j MT MA sigs)) '(LSU RS0))
		  (LSU-issued-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (INST-in i MT) (INST-p i) 
		  (INST-in j MT) (INST-p j))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :use ((:instance reachable-stages-to-LSU-issued-stg-p)
			(:instance stages-reachable-to-LSU-RS0 (i j)))
		  :in-theory (e/d (LSU-stg-p INST-IN-ORDER-P-LSU-ISSUED-RS
					     LSU-issued-stg-p)
				  (INST-STG-STEP-IFU-INST-IF-DQ-FULL))))
  :rule-classes 
  ((:rewrite :corollary
     (implies (and (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (equal (INST-stg (step-INST j MT MA sigs)) '(LSU RS0))
		   (INST-in i MT) (INST-p i) 
		   (INST-in j MT) (INST-p j)
		   (INST-in-order-p j i MT))
	      (not (LSU-issued-stg-p (INST-stg (step-INST i MT MA sigs))))))))

(defthm INST-in-order-p-step-INST-LSU-issued-RS1-help2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg j) '(LSU RS1))
		  (LSU-stg-p (INST-stg i))
		  (equal (INST-stg (step-INST j MT MA sigs)) '(LSU RS1))
		  (LSU-issued-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (INST-in i MT) (INST-p i) 
		  (INST-in j MT) (INST-p j))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :in-theory (enable LSU-stg-p LSU-issued-stg-p
				     INST-IN-ORDER-P-LSU-ISSUED-RS
				     INST-in-order-p-LSU-RS0-RS1
				     ISSUE-LSU-RS0? lift-b-ops
				     LSU-RS0-ISSUE-READY?
				     ISSUE-LSU-RS1?
				     LSU-RS1-ISSUE-READY?
				     inst-stg-step-inst))))

(defthm INST-in-order-p-step-INST-LSU-issued-RS1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg (step-INST j MT MA sigs)) '(LSU RS1))
		  (LSU-issued-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (INST-in i MT) (INST-p i) 
		  (INST-in j MT) (INST-p j))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :use ((:instance reachable-stages-to-LSU-issued-stg-p)
			(:instance stages-reachable-to-LSU-RS1 (i j)))
		  :in-theory (e/d (LSU-stg-p INST-IN-ORDER-P-LSU-ISSUED-RS
					     LSU-issued-stg-p)
				  (INST-STG-STEP-IFU-INST-IF-DQ-FULL))))
  
  :rule-classes
  ((:rewrite :corollary
     (implies (and (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (equal (INST-stg (step-INST j MT MA sigs)) '(LSU RS1))
		   (INST-in i MT) (INST-p i)
		   (INST-in j MT) (INST-p j)
		   (INST-in-order-p j i MT))
	      (not (LSU-issued-stg-p (INST-stg (step-INST i MT MA sigs))))))))

(encapsulate nil
(local
(defthm in-order-LSU-issue-p-step-trace-help1
    (implies (and (inv MT MA)
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU RS0))
		  (INST-in i MT) (INST-p i) 
		  (subtrace-p trace MT) (INST-listp trace) 
		  (subtrace-after-p i trace MT)
		  (MAETT-p MT) (MA-state-p MA))
     (no-issued-LSU-inst-p (step-trace trace MT MA sigs ISA spc smc)))))

(local
(defthm in-order-LSU-issue-p-step-trace-help2
    (implies (and (inv MT MA)
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU RS1))
		  (INST-in i MT) (INST-p i) 
		  (subtrace-p trace MT) (INST-listp trace) 
		  (subtrace-after-p i trace MT)
		  (MAETT-p MT) (MA-state-p MA))
     (no-issued-LSU-inst-p (step-trace trace MT MA sigs ISA spc smc)))))

(defthm in-order-LSU-issue-p-step-trace
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA))
	     (in-order-LSU-issue-p (step-trace trace MT MA sigs ISA spc smc))))
)

(defthm INST-in-order-RS1-RS0-if-RS1-head
    (implies (and (inv MT MA)
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU RS1))
		  (equal (INST-stg (step-INST j MT MA sigs))
			 '(LSU RS0))
		  (INST-in i MT) (INST-p i) 
		  (INST-in j MT) (INST-p j)
		  (b1p (LSU-RS1-head? (step-LSU MA sigs)))
		  (MAETT-p MT) (MA-state-p MA))
	     (INST-in-order-p i j MT))
  :hints (("goal" :use ((:instance stages-reachable-to-LSU-RS1)
			(:instance stages-reachable-to-LSU-RS0
				   (i j)))
		  :in-theory (enable step-inst-dq-inst step-inst-execute-inst
				     step-inst-low-level-functions
				     INST-in-order-p-LSU-RS1-RS0
				     lift-b-ops LSU-READY?
				     DISPATCH-TO-LSU? STEP-LSU
				     step-RS1-head?
				     DISPATCH-INST?)))
  :rule-classes
  ((:rewrite :corollary 
	     (implies (and (inv MT MA)
			   (equal (INST-stg (step-INST j MT MA sigs))
				  '(LSU RS0))
			   (INST-in i MT) (INST-p i) 
			   (INST-in j MT) (INST-p j)
			   (INST-in-order-p j i MT)
			   (b1p (LSU-RS1-head? (step-LSU MA sigs)))
			   (MAETT-p MT) (MA-state-p MA))
		      (not (equal (INST-stg (step-INST i MT MA sigs))
				  '(LSU RS1)))))))

(defthm INST-in-order-RS0-RS1-if-not-RS1-head
    (implies (and (inv MT MA)
		  (equal (INST-stg (step-INST j MT MA sigs))
			 '(LSU RS1))
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU RS0))
		  (INST-in i MT) (INST-p i) 
		  (INST-in j MT) (INST-p j)
		  (not (b1p (LSU-RS1-head? (step-LSU MA sigs))))
		  (MAETT-p MT) (MA-state-p MA))
	     (INST-in-order-p i j MT))
  :hints (("goal" :use ((:instance stages-reachable-to-LSU-RS1 (i j))
			(:instance stages-reachable-to-LSU-RS0))
		  :in-theory (enable step-inst-dq-inst step-inst-execute-inst
				     step-inst-low-level-functions
				     INST-in-order-p-LSU-RS0-RS1
				     lift-b-ops LSU-READY?
				     DISPATCH-TO-LSU? STEP-LSU
				     step-RS1-head?
				     DISPATCH-INST?)))
  :rule-classes
  ((:rewrite :corollary 
	     (implies (and (inv MT MA)
			   (equal (INST-stg (step-INST j MT MA sigs))
				  '(LSU RS1))
			   (INST-in i MT) (INST-p i) 
			   (INST-in j MT) (INST-p j)
			   (INST-in-order-p j i MT)
			   (not (b1p (LSU-RS1-head? (step-LSU MA sigs))))
			   (MAETT-p MT) (MA-state-p MA))
		      (not (equal (INST-stg (step-INST i MT MA sigs))
				  '(LSU RS0)))))))

(encapsulate nil
(local
(defthm in-order-LSU-RS-p-MT-trace-MT-step-help1
    (implies (and (inv MT MA)
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU RS0))
		  (INST-in i MT) (INST-p i) 
		  (subtrace-p trace MT) (INST-listp trace)
		  (subtrace-after-p i trace MT)
		  (b1p (LSU-RS1-head? (step-LSU MA sigs)))
		  (MAETT-p MT) (MA-state-p MA))
	     (no-inst-at-stg-in-trace '(LSU RS1)
				      (step-trace trace MT MA sigs
						  ISA spc smc)))))

(local
(defthm in-order-LSU-RS-p-MT-trace-MT-step-help2
    (implies (and (inv MT MA)
		  (equal (INST-stg (step-INST i MT MA sigs))
			 '(LSU RS1))
		  (INST-in i MT) (INST-p i) 
		  (subtrace-p trace MT) (INST-listp trace)
		  (subtrace-after-p i trace MT)
		  (not (b1p (LSU-RS1-head? (step-LSU MA sigs))))
		  (MAETT-p MT) (MA-state-p MA))
	     (no-inst-at-stg-in-trace '(LSU RS0)
				      (step-trace trace MT MA sigs
						  ISA spc smc))))) 

(defthm in-order-LSU-RS-p-MT-trace-MT-step
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA))
	     (in-order-LSU-RS-p (step-trace trace MT MA sigs ISA spc smc) 
				(MA-step MA sigs))))
)

(defthm not-wbuf0-step-inst-if-rob-wbuf-empty
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (b1p (ROB-empty? (MA-rob MA)))
		  (not (b1p (LSU-pending-writes? (MA-LSU MA))))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (wbuf0-stg-p (INST-stg (step-inst i MT MA sigs)))))
  :hints (("Goal" :use ((:instance stages-reachable-to-LSU-wbuf0)
			(:instance stages-reachable-to-LSU-wbuf0-lch)
			(:instance stages-reachable-to-complete-wbuf0)
			(:instance stages-reachable-to-commit-wbuf0))
		  :in-theory (enable wbuf0-stg-p)
		  :restrict (((:REWRITE NOT-ROB-EMPTY-IF-INST-IS-EXECUTED . 1)
			      ((i i)))))))

(defthm not-INST-commit-if-LSU-wbuf0
    (implies (and (inv MT MA)
		  (equal (INST-stg j) '(LSU wbuf0))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (equal (INST-stg i) '(complete wbuf1))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-commit? i MA) 0))
  :hints (("goal" :in-theory (e/d (INST-commit? lift-b-ops
						equal-b1p-converter
						INST-IN-ORDER-P-WBUF0-WBUF1)
				  (UNCOMMITTED-INST-P-IS-AFTER-MT-ROB-HEAD))
		  :use (:instance UNCOMMITTED-INST-P-IS-AFTER-MT-ROB-HEAD
				  (i j)))))

(defthm INST-in-order-if-INST-commit
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (execute-stg-p (INST-stg j))
		  (b1p (INST-commit? i MA)))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :in-theory (e/d (INST-commit? lift-b-ops)
				  (UNCOMMITTED-INST-P-IS-AFTER-MT-ROB-HEAD))
		  :use (:instance UNCOMMITTED-INST-P-IS-AFTER-MT-ROB-HEAD
				  (i j)))))

(defthm INST-in-order-if-INST-commit-before-complete
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (not (equal i j))
		  (complete-stg-p (INST-stg j))
		  (b1p (INST-commit? i MA)))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :in-theory (e/d (INST-commit? lift-b-ops)
				  (UNCOMMITTED-INST-P-IS-AFTER-MT-ROB-HEAD))
		  :use (:instance UNCOMMITTED-INST-P-IS-AFTER-MT-ROB-HEAD
				  (i j)))))

(defthm INST-in-order-retire-LSU-wbuf0-step-inst
    (implies (and (inv MT MA)
		  (retire-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (equal (INST-stg (step-inst j MT MA sigs))
			 '(LSU wbuf0))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j) 
		  (b1p (INST-store? i))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :use ((:instance stages-reachable-to-retire-stg)
			(:instance stages-reachable-to-LSU-wbuf0
				   (i j))
			(:instance uniq-wbuf0-inst)
			(:instance uniq-wbuf1-inst))
		  :in-theory (enable wbuf0-stg-p
				     INST-stg-step-inst lift-b-ops
				     NOT-INST-STORE-IF-COMPLETE
				     INST-IN-ORDER-P-RETIRE-WBUF1
				     INST-IN-ORDER-P-RETIRE-WBUF0
				     INST-IN-ORDER-P-LSU-ISSUED-RS
				     INST-IN-ORDER-P-WBUF0-WBUF1))))

(defthm INST-in-order-retire-LSU-wbuf0-lch-step-inst
    (implies (and (inv MT MA)
		  (retire-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (equal (INST-stg (step-inst j MT MA sigs))
			 '(LSU wbuf0 lch))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j) 
		  (b1p (INST-store? i))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :use ((:instance stages-reachable-to-retire-stg)
			(:instance stages-reachable-to-LSU-wbuf0-lch
				   (i j))
			(:instance uniq-wbuf0-inst)
			(:instance uniq-wbuf1-inst))
		  :in-theory (enable wbuf0-stg-p
				     INST-stg-step-inst lift-b-ops
				     NOT-INST-STORE-IF-COMPLETE
				     INST-IN-ORDER-P-RETIRE-WBUF1
				     INST-IN-ORDER-P-RETIRE-WBUF0
				     INST-IN-ORDER-P-LSU-ISSUED-RS
				     INST-IN-ORDER-P-WBUF0-WBUF1))))

(defthm INST-in-order-retire-complete-wbuf0-lch-step-inst
    (implies (and (inv MT MA)
		  (retire-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (equal (INST-stg (step-inst j MT MA sigs))
			 '(complete wbuf0))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j) 
		  (b1p (INST-store? i))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :use
		  ((:instance stages-reachable-to-retire-stg)
		   (:instance stages-reachable-to-complete-wbuf0
			      (i j))
		   (:instance INST-in-order-if-INST-commit-before-complete)
		   (:instance uniq-wbuf0-inst)
		   (:instance uniq-wbuf1-inst))
		  :in-theory (enable wbuf0-stg-p
				     INST-stg-step-inst lift-b-ops
				     NOT-INST-STORE-IF-COMPLETE
				     INST-IN-ORDER-P-RETIRE-WBUF1
				     INST-IN-ORDER-P-RETIRE-WBUF0
				     INST-IN-ORDER-P-LSU-ISSUED-RS
				     INST-IN-ORDER-P-WBUF0-WBUF1))))

(encapsulate nil
(defthm not-INST-commit-if-store-inst-is-at-complete-help
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(complete))
		  (b1p (INST-store? i))
		  (b1p (LSU-pending-writes? (MA-LSU MA)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-commit? i MA) 0))
  :hints (("Goal" :cases ((INST-fetch-error-detected-p i)
			  (INST-decode-error-detected-p i))
		  :in-theory (enable NOT-INST-STORE-IF-COMPLETE
				     INST-COMMIT? lift-b-ops
				     equal-b1p-converter
				     INST-EXCPT-DETECTED-P
				     commit-inst?))))

(defthm not-INST-commit-if-store-inst-is-at-complete
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(complete))
		  (b1p (INST-store? i))
		  (b1p (LSU-pending-writes? (MA-LSU MA)))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (INST-commit? i MA) 0))
  :hints (("Goal" :cases ((b1p (inst-specultv? i))
			  (b1p (INST-modified? i)))
		  :in-theory (enable equal-b1p-converter))))
)

(defthm not-enter-excpt-if-LSU-pending-writes
    (implies (b1p (LSU-pending-writes? (MA-LSU MA)))
	     (equal (enter-excpt? MA) 0))
  :hints (("Goal" :in-theory (enable enter-excpt? lift-b-ops
				     equal-b1p-converter))))

(defthm INST-in-order-retire-commit-wbuf0-lch-step-inst
    (implies (and (inv MT MA)
		  (retire-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (equal (INST-stg (step-inst j MT MA sigs))
			 '(commit wbuf0))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j) 
		  (b1p (INST-store? i))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :use
		  ((:instance stages-reachable-to-retire-stg)
		   (:instance stages-reachable-to-commit-wbuf0
			      (i j))
		   (:instance INST-in-order-if-INST-commit-before-complete)
		   (:instance uniq-wbuf0-inst)
		   (:instance uniq-wbuf1-inst))
		  :restrict ((LSU-pending-writes-if-wbuf-inst-in
			      ((i j))))
		  :in-theory (enable wbuf0-stg-p
				     INST-stg-step-inst lift-b-ops
				     NOT-INST-STORE-IF-COMPLETE
				     INST-IN-ORDER-P-RETIRE-WBUF1
				     INST-IN-ORDER-P-RETIRE-WBUF0
				     INST-IN-ORDER-P-LSU-ISSUED-RS
				     INST-IN-ORDER-P-WBUF0-WBUF1))))

(defthm INST-in-order-retire-wbuf0-step-inst
    (implies (and (inv MT MA)
		  (retire-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (wbuf0-stg-p (INST-stg (step-inst j MT MA sigs)))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j) 
		  (b1p (INST-store? i))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :in-theory (enable wbuf0-stg-p)))
  :rule-classes
  ((:rewrite :corollary
     (implies (and (inv MT MA)
		   (wbuf0-stg-p (INST-stg (step-inst j MT MA sigs)))
		   (INST-in i MT) (INST-p i)
		   (INST-in j MT) (INST-p j) 
		   (INST-in-order-p j i MT)
		   (not (MT-CMI-p (MT-step MT MA sigs)))
		   (b1p (INST-store? i))
		   (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	      (not (retire-stg-p (INST-stg (step-INST i MT MA sigs))))))))

(encapsulate nil
(local
(defthm in-order-wb-retire-p-MT-trace-MT-step-help
    (implies (and (inv MT MA)
		  (wbuf0-stg-p (INST-stg (step-inst i MT MA sigs)))
		  (INST-in i MT) (INST-p i)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (subtrace-after-p i trace MT)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (no-retired-store-p (step-trace trace MT MA sigs ISA spc smc)))
  :hints (("Goal" :in-theory (enable INST-exintr-now? lift-b-ops
				     ex-intr?)))))

(defthm in-order-wb-retire-p-MT-trace-MT-step
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (in-order-wb-retire-p (step-trace trace MT MA sigs ISA spc smc))))
) 

(defthm in-order-LSU-inst-p-preserved
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (MT-CMI-p (MT-step MT MA sigs))))
	     (in-order-LSU-inst-p (MT-step MT MA sigs) (MA-step MA sigs)))
  :hints (("Goal" :in-theory (e/d (in-order-LSU-inst-p) ()))))
