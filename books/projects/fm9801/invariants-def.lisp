;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; invariants.lisp:
; Author  Jun Sawada, University of Texas at Austin
;
;  The definition of the invariant condition of the FM9801.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "ACL2")

(include-book "MAETT-def")

; Starting the definition of various invariants
(deflabel begin-invariants-def)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  Definition of weak-inv.
;  Weak invariants are well-formedness predicate. 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun trace-correct-modified-first (trace)
  (declare (xargs :guard  (INST-listp trace)))
  (if (endp trace) t
      (if (endp (cdr trace)) t
	  (and (implies (and (b1p (INST-modified? (cadr trace)))
			     (not (b1p (INST-modified? (car trace)))))
			(b1p (INST-first-modified? (cadr trace))))
	       (trace-correct-modified-first (cdr trace))))))

(defun correct-modified-first (MT)
  (declare (xargs :guard  (MAETT-p MT)))
  (trace-correct-modified-first (MT-trace MT)))

(defun ID-lt-all-p (trace ID)
  (declare (xargs :guard (and (INST-listp trace) (integerp ID) (<= 0 ID))))
  (if (endp trace)
      T
      (and (< (INST-ID (car trace)) ID)
	   (ID-lt-all-p (cdr trace) ID))))

(defun MT-new-ID-distinct-p (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (ID-lt-all-p (MT-trace MT) (MT-new-ID MT)))

(defun member-eq-ID (i trace)
  (declare (xargs :guard (and (INST-p i) (INST-listp trace))))
  (if (endp trace)
      nil
      (if (equal (INST-ID i) (INST-ID (car trace)))
	  trace
	  (member-eq-ID i (cdr trace)))))
	  
; All ID of INST's are different.
(defun distinct-IDs-p (trace)
  (declare (xargs :guard (and (INST-listp trace))))
  (if (endp trace)
      T
      (and (not (member-eq-ID (car trace) (cdr trace)))
	   (distinct-IDs-p (cdr trace)))))

(defun MT-distinct-IDs-p (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (distinct-IDs-p (MT-trace MT)))

(defun distinct-member-p (trace)
  (declare (xargs :guard (and (INST-listp trace))))
  (if (endp trace)
      T
      (and (not (member-equal (car trace) (cdr trace)))
	   (distinct-member-p (cdr trace)))))

; No INST entry of MT equals to other INST's. 
(defun MT-distinct-INST-p (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (distinct-member-p (MT-trace MT)))

(defun ISA-chained-trace-p (INST-list ISA)
  (declare (xargs :guard (and (INST-listp INST-list) (ISA-state-p ISA))))
  (if (endp INST-list)
      T
      (and (equal ISA (INST-pre-ISA (car INST-list)))
	   (equal (ISA-step (INST-pre-ISA (car INST-list))
			    (ISA-input (INST-exintr? (car INST-list))))
		  (INST-post-ISA (car INST-list)))
	   (ISA-chained-trace-p (cdr INST-list)
				(INST-post-ISA (car INST-list))))))

; Pre-ISA and post-ISA states form a chain.
(defun ISA-step-chain-p (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (ISA-chained-trace-p (MT-trace MT) (MT-init-ISA MT)))

(defun trace-all-modified-p (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace) T
      (and (b1p (INST-modified? (car trace)))
	   (trace-all-modified-p (cdr trace)))))

(defun trace-modified-flg-sticky-p (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace) t
      (if (b1p (INST-modified? (car trace)))
	  (trace-all-modified-p (cdr trace))
	  (trace-modified-flg-sticky-p (cdr trace)))))

(defun INST-modify-p (i j)
  (declare (xargs :guard (and (INST-p i) (INST-p j))))
  (and (b1p (INST-store? i))
       (equal (INST-store-addr i)
	      (ISA-pc (INST-pre-ISA j)))
       (not (b1p (INST-excpt? i)))
       (not (b1p (INST-exintr? i)))
       (not (b1p (INST-exintr? j)))))

(defun trace-modify-p (i trace)
  (declare (xargs :guard (and (INST-p i) (INST-listp trace))))
  (if (endp trace) nil
      (if (equal (car trace) i)
	  nil
	  (or (INST-modify-p (car trace) i)
	      (trace-modify-p i (cdr trace))))))

(defun MT-modify-p (i MT)
  (declare (xargs :guard (and (INST-p i) (MAETT-p MT))))
  (trace-modify-p i (MT-trace MT)))

(defun trace-correct-modified-flgs-p (trace MT sticky)
  (declare (xargs :guard (and (INST-listp trace) (MAETT-p MT) (bitp sticky))))
  (if (endp trace)
      T
      (if (MT-modify-p (car trace) MT)
	  (and (equal (INST-modified? (car trace)) 1)
	       (trace-correct-modified-flgs-p (cdr trace) MT 1))
	  (and (equal (INST-modified? (car trace)) sticky)
	       (trace-correct-modified-flgs-p (cdr trace) MT sticky)))))

; Modified? bit of each INST is sticky.
(defun correct-modified-flgs-p (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-correct-modified-flgs-p (MT-trace MT) MT 0))

; Definition of weak invariants. Most of the invariants are
; about the well-formedness of the MAETT.
(defun weak-inv (MT)
  (declare (xargs :guard  (MAETT-p MT)))
  (and (MT-new-ID-distinct-p MT)
       (MT-distinct-IDs-p MT)
       (MT-distinct-INST-p MT)
       (ISA-step-chain-p MT)
       (correct-modified-flgs-p MT)
       (correct-modified-first MT)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Definition of Strong Invariants (or what we usually call invariants).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(defun trace-final-ISA (trace pre)
  (declare (xargs :guard (and (INST-listp trace) (ISA-state-p pre))))
  (if (endp trace)
      pre
      (trace-final-ISA (cdr trace) (INST-post-ISA (car trace)))))

(defthm ISA-state-p-trace-final-ISA
    (implies (and (INST-listp trace) (ISA-state-p pre))
	     (ISA-state-p (trace-final-ISA trace pre))))

(defun MT-final-ISA (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-final-ISA (MT-trace MT) (MT-init-ISA MT)))

; MT-all-retired-p is a predicate to check whether all instructions in 
; a MAETT are retired.
(defun trace-all-retired (INST-list)
  (declare (xargs :guard (INST-listp INST-list)))
  (if (endp INST-list)
      T
      (and (retire-stg-p (INST-stg (car INST-list)))
	   (trace-all-retired (cdr INST-list)))))

(defun MT-all-retired-p (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-all-retired (MT-trace MT)))
    
(in-theory (disable MT-all-retired-p))

(defthm ISA-state-p-MT-final-ISA
    (implies (MAETT-p MT) (ISA-state-p (MT-final-ISA MT)))
  :hints (("Goal" :in-theory (enable MT-final-ISA))))

(defun trace-self-modify? (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace)
      0
      (b-if (INST-modified? (car trace))
	    1
	    (trace-self-modify? (cdr trace)))))

(defthm bitp-trace-self-modify?
    (bitp (trace-self-modify? trace)))

(defun MT-self-modify? (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-self-modify? (MT-trace MT)))

(defthm bitp-MT-self-modify?
    (bitp (MT-self-modify? MT)))

(defun MT-self-modify-p (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (b1p (MT-self-modify? MT)))

; MT-CMI-p checks whether MT contains a committed self-modified
; instruction.  The recursive function trace-CMI-p only checks the
; continuous segment of instructions in MAETT, which are all
; committed.  Since instructions commit in-order, we don't have to
; look further once we encounter a non-committed instruction.
(defun trace-CMI-p (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace)
      nil
      (or  (and (committed-p (car trace))
		(b1p (INST-modified? (car trace)))) 
	   (and (committed-p (car trace))
		(trace-CMI-p (cdr trace))))))

(defun MT-CMI-p (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-CMI-p (MT-trace MT)))

(defun trace-specultv? (INST-list)
  (declare (xargs :guard (INST-listp INST-list)))
  (if (endp INST-list)
      0
      (b-if (b-ior (inst-specultv? (car INST-list))
		   (INST-start-specultv? (car INST-list)))
	    1
	    (trace-specultv? (cdr INST-list)))))
      
(defthm bitp-trace-specultv?
    (bitp (trace-specultv? trace)))

(defun MT-specultv? (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-specultv? (MT-trace MT)))

(defthm bitp-MT-specultv?
    (bitp (MT-specultv? MT))
  :hints (("Goal" :in-theory (enable MT-specultv?))))

(defun MT-specultv-p (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (b1p (MT-specultv? MT)))

(defun trace-specultv-at-dispatch? (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace)
      0
      (if (not (dispatched-p (car trace)))
	  0
	  (if (committed-p (car trace))
	      (trace-specultv-at-dispatch? (cdr trace))
	      (b-if (b-ior (inst-specultv? (car trace))
			   (INST-start-specultv? (car trace)))
		    1
		    (trace-specultv-at-dispatch? (cdr trace)))))))

(defthm bitp-trace-specultv-at-dispatch?
    (bitp (trace-specultv-at-dispatch? trace)))

(defun MT-specultv-at-dispatch? (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-specultv-at-dispatch? (MT-trace MT)))

(defthm bitp-MT-specultv-at-dispatch?
    (bitp (MT-specultv-at-dispatch? MT)))

(defun trace-modified-at-dispatch? (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace)
      0
      (if (not (dispatched-p (car trace)))
	  0
	  (b-if (INST-modified? (car trace))
		1
		(trace-modified-at-dispatch? (cdr trace))))))

(defthm bitp-trace-modified-at-dispatch?
    (bitp (trace-modified-at-dispatch? trace)))

(defun MT-modified-at-dispatch? (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-modified-at-dispatch? (MT-trace MT)))

(defthm bitp-MT-modified-at-dispatch?
    (bitp (MT-modified-at-dispatch? MT)))

(defun trace-pc (INST-list pre-pc)
  (declare (xargs :guard (and (INST-listp INST-list) (addr-p pre-pc))))
  (if (endp INST-list)
      pre-pc
      (trace-pc (cdr INST-list) (ISA-pc (INST-post-ISA (car INST-list))))))

(defthm addr-p-trace-pc
    (implies (and (addr-p pc) (INST-listp trace))
	     (addr-p (trace-pc trace pc))))

(defun MT-pc (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-pc (MT-trace MT) (ISA-pc (MT-init-ISA MT))))

(defthm addr-p-MT-pc
    (implies (MAETT-p MT) (addr-p (MT-pc MT)))
  :hints (("Goal" :in-theory (enable MT-pc))))

; The pc in MA is in the correct state. 
(defun pc-match-p (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))  
  (implies (not (or (MT-specultv-p MT)
		    (MT-self-modify-p MT)))
	   (equal (MT-pc MT) (MA-pc MA))))

(defun trace-RF (INST-list RF)
  (declare (xargs :guard (and (INST-listp INST-list) (RF-p RF))))
  (if (endp INST-list) 
      RF
      (if (not (or (retire-stg-p (INST-stg (car INST-list)))
		   (commit-stg-p (INST-stg (car INST-list)))))
	  RF
	  (trace-RF (cdr INST-list)
		    (ISA-RF (INST-post-ISA (car INST-list)))))))

(defthm trace-RF* 
    (equal (trace-RF INST-list RF)
	   (if (endp INST-list) 
	       RF
	       (if (not (committed-p (car INST-list)))
		   RF
		   (trace-RF (cdr INST-list)
			     (ISA-RF (INST-post-ISA (car INST-list)))))))
  :rule-classes (:definition))

(defthm RF-p-trace-RF
    (implies (and (INST-listp trace) (RF-p RF))
	     (RF-p (trace-RF trace RF))))

(defun MT-RF (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-RF (MT-trace MT) (ISA-RF (MT-init-ISA MT))))
  
(defthm RF-p-MT-RF
    (implies (MAETT-p MT) (RF-p (MT-RF MT))))

; The register file in MA is in the correct state. 
(defun RF-match-p (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))  
  (equal (MT-RF MT) (MA-RF MA)))

(defun trace-SRF (INST-list SRF)
  (declare (xargs :guard (and (INST-listp INST-list) (SRF-p SRF))))
  (if (endp INST-list) 
      SRF
      (if (not (or (retire-stg-p (INST-stg (car INST-list)))
		   (commit-stg-p (INST-stg (car INST-list)))))
	  SRF
	  (trace-SRF (cdr INST-list)
		     (ISA-SRF (INST-post-ISA (car INST-list)))))))

(defthm SRF-p-trace-SRF
    (implies (and (SRF-p SRF) (INST-listp trace))
	     (SRF-p (trace-SRF trace SRF))))

(defun MT-SRF (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-SRF (MT-trace MT) (ISA-SRF (MT-init-ISA MT))))

(defthm SRF-p-MT-SRF
    (implies (MAETT-p MT) (SRF-p (MT-SRF MT))))
  
; The SRF in MA is in the correct state.
(defun SRF-match-p (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))  
  (equal (MT-SRF MT) (MA-SRF MA)))

(defun trace-mem (INST-list mem)
  (declare (xargs :guard (and (INST-listp INST-list) (mem-p mem))))
  (if (endp INST-list) 
      mem
      (if (not (retire-stg-p (INST-stg (car INST-list))))
	  mem
	  (trace-mem (cdr INST-list)
		     (ISA-mem (INST-post-ISA (car INST-list)))))))

(defthm mem-p-trace-mem
    (implies (and (mem-p mem) (INST-listp trace))
	     (mem-p (trace-mem trace mem))))

(defun MT-mem (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-mem (MT-trace MT) (ISA-mem (MT-init-ISA MT))))

(defthm mem-p-MT-mem
    (implies (MAETT-p MT) (mem-p (MT-mem MT))))

; The memory in MA is in the correct state. 
(defun mem-match-p (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))  
  (equal (MT-mem MT) (MA-mem MA)))

(defun trace-no-specultv-commit-p (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace)
      T
      (and (implies (committed-p (car trace))
		    (zbp (inst-specultv? (car trace))))
	   (trace-no-specultv-commit-p (cdr trace)))))

; No speculatively executed instructions are committed. 
(defun no-specultv-commit-p (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-no-specultv-commit-p (MT-trace MT)))

(defun trace-all-specultv-p (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace)
      t
      (and (b1p (inst-specultv? (car trace)))
	   (trace-all-specultv-p (cdr trace)))))

(defun trace-correct-speculation-p (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace) T
      (and (not (b1p (inst-specultv? (car trace))))
	   (if (b1p (INST-start-specultv? (car trace)))
	       (trace-all-specultv-p (cdr trace))
	       (trace-correct-speculation-p (cdr trace))))))
      

; Speculatively executed instructions follows an instruction that
; satisfies INST-start-specultv?
(defun correct-speculation-p (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-correct-speculation-p (MT-trace MT)))

(defun trace-correct-exintr-p (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace) t
      (and (implies (b1p (INST-exintr? (car trace)))
		    (retire-stg-p (INST-stg (car trace))))
	   (trace-correct-exintr-p (cdr trace)))))

; External interrupt field is set only for a retired instruction.
(defun correct-exintr-p (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (trace-correct-exintr-p (MT-trace MT)))

; From here we define MT-INST-inv.
(deflabel begin-inst-inv-def)
	   
; The condition that instruction i should satisfy at stage IFU.
; Following predicates are for other stages.
(defun IFU-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))
  (and (b1p (IFU-valid? (MA-IFU MA)))
       ; This condition is added later.
       ; If this instruction is modified by a previous instruction,
       ; but no preceding instruction is neither modified or speculatively 
       ; executed, at least the program counter value is correct. 
       (implies (and (not (b1p (inst-specultv? i)))
		     (implies (b1p (INST-modified? i))
			      (b1p (INST-first-modified? i))))
		(equal (IFU-pc (MA-IFU MA)) (ISA-pc (INST-pre-ISA i))))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	(and (equal (IFU-pc (MA-IFU MA)) (ISA-pc (INST-pre-ISA i)))
	     (equal (IFU-excpt (MA-IFU MA)) (INST-excpt-flags i))
	     (equal (IFU-word (MA-IFU MA))
		    (if (INST-fetch-error-detected-p i) 0 (INST-word i)))))))
  
(defun DQ0-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))  
  (and (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))
       (implies (and (not (b1p (inst-specultv? i)))
		     (implies (b1p (INST-modified? i))
			      (b1p (INST-first-modified? i))))
		(equal (DE-pc (DQ-DE0 (MA-DQ MA))) (ISA-pc (INST-pre-ISA i))))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	(and (equal (DE-excpt (DQ-DE0 (MA-DQ MA))) (INST-excpt-flags i))
	     (equal (DE-pc (DQ-DE0 (MA-DQ MA))) (ISA-pc (INST-pre-ISA i)))
	     (implies (not (INST-fetch-error-detected-p i))
	      (and (equal (DE-cntlv (DQ-DE0 (MA-DQ MA))) (INST-cntlv i))
		   (equal (DE-rc (DQ-DE0 (MA-DQ MA)))
			  (rc (INST-word i)))
		   (equal (DE-ra (DQ-DE0 (MA-DQ MA)))
			  (ra (INST-word i)))
		   (equal (DE-rb (DQ-DE0 (MA-DQ MA)))
			  (rb (INST-word i)))
		   (equal (DE-im (DQ-DE0 (MA-DQ MA)))
			  (im (INST-word i)))
		   (equal (DE-br-target (DQ-DE0 (MA-DQ MA)))
			  (INST-br-target i))))
	     (implies (INST-fetch-error-detected-p i)
		      (equal (DE-cntlv (DQ-DE0 (MA-DQ MA)))
			     (decode 0 (INST-br-predict? i))))))))

(defun DQ1-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))  
  (and (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))
       (implies (and (not (b1p (inst-specultv? i)))
		     (implies (b1p (INST-modified? i))
			      (b1p (INST-first-modified? i))))
		(equal (DE-pc (DQ-DE1 (MA-DQ MA))) (ISA-pc (INST-pre-ISA i))))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	(and (equal (DE-excpt (DQ-DE1 (MA-DQ MA))) (INST-excpt-flags i))
	     (implies (not (INST-fetch-error-detected-p i))	     
	      (and (equal (DE-cntlv (DQ-DE1 (MA-DQ MA)))
			  (INST-cntlv i))
		   (equal (DE-rc (DQ-DE1 (MA-DQ MA)))
			  (rc (INST-word i)))
		   (equal (DE-ra (DQ-DE1 (MA-DQ MA)))
			  (ra (INST-word i)))
		   (equal (DE-rb (DQ-DE1 (MA-DQ MA)))
			  (rb (INST-word i)))
		   (equal (DE-im (DQ-DE1 (MA-DQ MA)))
			  (im (INST-word i)))
		   (equal (DE-br-target (DQ-DE1 (MA-DQ MA)))
			  (INST-br-target i))))
	     (implies (INST-fetch-error-detected-p i)
		      (equal (DE-cntlv (DQ-DE1 (MA-DQ MA)))
			     (decode 0 (INST-br-predict? i))))))))
	     
(defun DQ2-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))  
  (and (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))
       (implies (and (not (b1p (inst-specultv? i)))
		     (implies (b1p (INST-modified? i))
			      (b1p (INST-first-modified? i))))
		(equal (DE-pc (DQ-DE2 (MA-DQ MA))) (ISA-pc (INST-pre-ISA i))))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	(and (equal (DE-excpt (DQ-DE2 (MA-DQ MA))) (INST-excpt-flags i))
	     (implies (not (INST-fetch-error-detected-p i))	     	     
	      (and (equal (DE-cntlv (DQ-DE2 (MA-DQ MA)))
			  (INST-cntlv i))
		   (equal (DE-rc (DQ-DE2 (MA-DQ MA)))
			  (rc (INST-word i)))
		   (equal (DE-ra (DQ-DE2 (MA-DQ MA)))
			  (ra (INST-word i)))
		   (equal (DE-rb (DQ-DE2 (MA-DQ MA)))
			  (rb (INST-word i)))
		   (equal (DE-im (DQ-DE2 (MA-DQ MA)))
			  (im (INST-word i)))
		   (equal (DE-br-target (DQ-DE2 (MA-DQ MA)))
			  (INST-br-target i))))
	     (implies (INST-fetch-error-detected-p i)
		      (equal (DE-cntlv (DQ-DE2 (MA-DQ MA)))
			     (decode 0 (INST-br-predict? i))))))))

(defun DQ3-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))  
  (and (b1p (DE-valid? (DQ-DE3 (MA-DQ MA))))
       (implies (and (not (b1p (inst-specultv? i)))
		     (implies (b1p (INST-modified? i))
			      (b1p (INST-first-modified? i))))
		(equal (DE-pc (DQ-DE3 (MA-DQ MA))) (ISA-pc (INST-pre-ISA i))))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	(and (equal (DE-excpt (DQ-DE3 (MA-DQ MA))) (INST-excpt-flags i))
	     (implies (not (INST-fetch-error-detected-p i))	     	     
	      (and (equal (DE-cntlv (DQ-DE3 (MA-DQ MA))) (INST-cntlv i))
		   (equal (DE-rc (DQ-DE3 (MA-DQ MA)))
			  (rc (INST-word i)))
		   (equal (DE-ra (DQ-DE3 (MA-DQ MA)))
			  (ra (INST-word i)))
		   (equal (DE-rb (DQ-DE3 (MA-DQ MA)))
			  (rb (INST-word i)))
		   (equal (DE-im (DQ-DE3 (MA-DQ MA)))
			  (im (INST-word i)))
		   (equal (DE-br-target (DQ-DE3 (MA-DQ MA)))
			  (INST-br-target i))))
	     (implies (INST-fetch-error-detected-p i)
		      (equal (DE-cntlv (DQ-DE3 (MA-DQ MA)))
			     (decode 0 (INST-br-predict? i))))))))

(defun DQ-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))  
  (cond ((equal (INST-stg i) '(DQ 0))
	 (DQ0-inst-inv i MA))
	((equal (INST-stg i) '(DQ 1))
	 (DQ1-inst-inv i MA))
	((equal (INST-stg i) '(DQ 2))
	 (DQ2-inst-inv i MA))
	((equal (INST-stg i) '(DQ 3))
	 (DQ3-inst-inv i MA))
	(t nil)))
  

(defun IU-RS0-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))
  (and (b1p (RS-valid? (IU-RS0 (MA-IU MA))))
       ; This may not be provable.
       (equal (RS-tag (IU-RS0 (MA-IU MA))) (INST-tag i))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	 (and (b1p (INST-IU? i))
	      (not (INST-excpt-detected-p i))
	      (implies (b1p (logbit 3 (cntlv-operand (INST-cntlv i))))
		       (srname-p (INST-ra i)))
	      (equal (RS-op (IU-RS0 (MA-IU MA))) (INST-IU-op? i))
	      (implies (b1p (RS-ready1? (IU-RS0 (MA-IU MA))))
		       (equal (RS-val1 (IU-RS0 (MA-IU MA)))
			      (INST-src-val1 i)))
	      (implies (and (b1p (RS-ready2? (IU-RS0 (MA-IU MA))))
			    (not (b1p (INST-IU-op? i))))
		       (equal (RS-val2 (IU-RS0 (MA-IU MA)))
			      (INST-src-val2 i)))))))
  
(defun IU-RS1-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))
  (and (b1p (RS-valid? (IU-RS1 (MA-IU MA))))
       ; This tag field is related to the control of instructions.
       ; not the output of data.  Should be independent of speculative
       ; execution.
       (equal (RS-tag (IU-RS1 (MA-IU MA))) (INST-tag i))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	 (and (b1p (INST-IU? i))
	      (not (INST-excpt-detected-p i))
	      (implies (b1p (logbit 3 (cntlv-operand (INST-cntlv i))))
		       (srname-p (INST-ra i)))
	      (equal (RS-op (IU-RS1 (MA-IU MA))) (INST-IU-op? i))
	      (implies (b1p (RS-ready1? (IU-RS1 (MA-IU MA))))
		       (equal (RS-val1 (IU-RS1 (MA-IU MA)))
			      (INST-src-val1 i)))
	      (implies (and (b1p (RS-ready2? (IU-RS1 (MA-IU MA))))
			    (not (b1p (INST-IU-op? i))))
		       (equal (RS-val2 (IU-RS1 (MA-IU MA)))
			      (INST-src-val2 i)))))))
       

(defun IU-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))    
  (cond ((equal (INST-stg i) '(IU RS0))
	 (IU-RS0-inst-inv i MA))
	((equal (INST-stg i) '(IU RS1))
	 (IU-RS1-inst-inv i MA))
	(t nil)))

(defun BU-RS0-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))
  (and (b1p (BU-RS-valid? (BU-RS0 (MA-BU MA))))
       (equal (BU-RS-tag (BU-RS0 (MA-BU MA))) (INST-tag i))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	 (and (b1p (INST-BU? i))
	      (not (INST-excpt-detected-p i))
	      (implies (b1p (BU-RS-ready? (BU-RS0 (MA-BU MA))))
		       (equal (BU-RS-val (BU-RS0 (MA-BU MA)))
			      (INST-src-val3 i)))))))

(defun BU-RS1-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))
  (and (b1p (BU-RS-valid? (BU-RS1 (MA-BU MA))))
       (equal (BU-RS-tag (BU-RS1 (MA-BU MA))) (INST-tag i))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	 (and (b1p (INST-BU? i))
	      (not (INST-excpt-detected-p i))
	      (implies (b1p (BU-RS-ready? (BU-RS1 (MA-BU MA))))
		       (equal (BU-RS-val (BU-RS1 (MA-BU MA)))
			      (INST-src-val3 i)))))))
			    
(defun BU-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))    
  (cond ((equal (INST-stg i) '(BU RS0))
	 (BU-RS0-inst-inv i MA))
	((equal (INST-stg i) '(BU RS1))
	 (BU-RS1-inst-inv i MA))
	(t nil)))

(defun MU-RS0-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))    
  (and (b1p (RS-valid? (MU-RS0 (MA-MU MA))))
       (equal (RS-tag (MU-RS0 (MA-MU MA))) (INST-tag i))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	  (and (b1p (INST-MU? i))
	       (not (INST-excpt-detected-p i))
	       (equal (RS-op (MU-RS0 (MA-MU MA))) 0)
	       (implies (b1p (RS-ready1? (MU-RS0 (MA-MU MA))))
			(equal (RS-val1 (MU-RS0 (MA-MU MA)))
			       (INST-src-val1 i)))
	       (implies (b1p (RS-ready2? (MU-RS0 (MA-MU MA))))
			(equal (RS-val2 (MU-RS0 (MA-MU MA)))
			       (INST-src-val2 i)))))))

(defun MU-RS1-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))    
  (and (b1p (RS-valid? (MU-RS1 (MA-MU MA))))
       (equal (RS-tag (MU-RS1 (MA-MU MA))) (INST-tag i))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	  (and (b1p (INST-MU? i))
	       (not (INST-excpt-detected-p i))
	       (equal (RS-op (MU-RS1 (MA-MU MA))) 0)
	       (implies (b1p (RS-ready1? (MU-RS1 (MA-MU MA))))
			(equal (RS-val1 (MU-RS1 (MA-MU MA)))
			       (INST-src-val1 i)))
	       (implies (b1p (RS-ready2? (MU-RS1 (MA-MU MA))))
			(equal (RS-val2 (MU-RS1 (MA-MU MA)))
			       (INST-src-val2 i)))))))
				

(defun MU-lch1-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))    
  (and (b1p (MU-latch1-valid? (MU-lch1 (MA-MU MA))))
       (equal (MU-latch1-tag (MU-lch1 (MA-MU MA))) (INST-tag i))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	(and (b1p (INST-MU? i))
	     (not (INST-excpt-detected-p i))
	     (equal (MU-latch1-data (MU-lch1 (MA-MU MA)))
		    (ML1-output (INST-src-val1 i) (INST-src-val2 i)))))))

(defun MU-lch2-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))    
  (and (b1p (MU-latch2-valid? (MU-lch2 (MA-MU MA))))
       (equal (MU-latch2-tag (MU-lch2 (MA-MU MA))) (INST-tag i))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	(and (b1p (INST-MU? i))
	     (not (INST-excpt-detected-p i))
	     (equal (MU-latch2-data (MU-lch2 (MA-MU MA)))
		    (ML2-output
		     (ML1-output (INST-src-val1 i) (INST-src-val2 i))))))))
  
(defun MU-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))    
  (cond ((equal (INST-stg i) '(MU RS0))
	 (MU-RS0-inst-inv i MA))
	((equal (INST-stg i) '(MU RS1))
	 (MU-RS1-inst-inv i MA))
	((equal (INST-stg i) '(MU lch1))
	 (MU-lch1-inst-inv i MA))
	((equal (INST-stg i) '(MU lch2))
	 (MU-lch2-inst-inv i MA))
	(t nil)))

(defun LSU-RS0-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))    
  (and (b1p (LSU-RS-valid? (LSU-RS0 (MA-LSU MA))))
       (equal (LSU-RS-tag (LSU-RS0 (MA-LSU MA))) (INST-tag i))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	 (and (b1p (INST-LSU? i))
	      (not (INST-excpt-detected-p i))
	      (equal (LSU-RS-op (LSU-RS0 (MA-LSU MA)))
		     (INST-LSU-op? i))
	      (equal (LSU-RS-ld-st? (LSU-RS0 (MA-LSU MA)))
		     (INST-ld-st? i))
	      (implies (b1p (INST-LSU-op? i))
		       (b1p (LSU-RS-rdy1? (LSU-RS0 (MA-LSU MA)))))
	      (implies (b1p (LSU-RS-rdy1? (LSU-RS0 (MA-LSU MA))))
		       (equal (LSU-RS-val1 (LSU-RS0 (MA-LSU MA)))
			      (INST-src-val1 i)))
	      (implies (b1p (LSU-RS-rdy2? (LSU-RS0 (MA-LSU MA))))
		       (equal (LSU-RS-val2 (LSU-RS0 (MA-LSU MA)))
			      (INST-src-val2 i)))
	      (implies (b1p (LSU-RS-rdy3? (LSU-RS0 (MA-LSU MA))))
		       (equal (LSU-RS-val3 (LSU-RS0 (MA-LSU MA)))
			      (INST-src-val3 i)))))))

(defun LSU-RS1-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))    
  (and (b1p (LSU-RS-valid? (LSU-RS1 (MA-LSU MA))))
       (equal (LSU-RS-tag (LSU-RS1 (MA-LSU MA))) (INST-tag i))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	 (and (b1p (INST-LSU? i))
	      (not (INST-excpt-detected-p i))
	      (equal (LSU-RS-op (LSU-RS1 (MA-LSU MA)))
		     (INST-LSU-op? i))
	      (equal (LSU-RS-ld-st? (LSU-RS1 (MA-LSU MA)))
		     (INST-ld-st? i))
	      (implies (b1p (INST-LSU-op? i))
		       (b1p (LSU-RS-rdy1? (LSU-RS1 (MA-LSU MA)))))
	      (implies (b1p (LSU-RS-rdy1? (LSU-RS1 (MA-LSU MA))))
		       (equal (LSU-RS-val1 (LSU-RS1 (MA-LSU MA)))
			      (INST-src-val1 i)))
	      (implies (b1p (LSU-RS-rdy2? (LSU-RS1 (MA-LSU MA))))
		       (equal (LSU-RS-val2 (LSU-RS1 (MA-LSU MA)))
			      (INST-src-val2 i)))
	      (implies (b1p (LSU-RS-rdy3? (LSU-RS1 (MA-LSU MA))))
		       (equal (LSU-RS-val3 (LSU-RS1 (MA-LSU MA)))
			      (INST-src-val3 i)))))))

(defun LSU-rbuf-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))    
  (and (b1p (rbuf-valid? (LSU-rbuf (MA-LSU MA))))
       (equal (rbuf-tag (LSU-rbuf (MA-LSU MA))) (INST-tag i))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	(and (b1p (INST-load? i))
	     (not (INST-excpt-detected-p i))
	     (equal (rbuf-addr (LSU-rbuf (MA-LSU MA)))
		    (INST-load-addr i))))))

(defun LSU-lch-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))    
  (and (b1p (LSU-latch-valid? (LSU-lch (MA-LSU MA))))
       (equal (LSU-latch-tag (LSU-lch (MA-LSU MA))) (INST-tag i))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
        (and (b1p (INST-load? i))
	     (not (INST-fetch-error-detected-p i))
	     (not (INST-decode-error-detected-p i))
	     (equal (LSU-latch-excpt (LSU-lch (MA-LSU MA)))
		    (INST-excpt-flags i))
	     (implies (not (INST-load-accs-error-detected-p i))
		      (equal (LSU-latch-val (LSU-lch (MA-LSU MA)))
			     (INST-dest-val i)))))))

(defun LSU-wbuf0-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))    
  (and (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))  
       (not (b1p (wbuf-complete? (LSU-wbuf0 (MA-LSU MA)))))
       (not (b1p (wbuf-commit? (LSU-wbuf0 (MA-LSU MA)))))
       (equal (wbuf-tag (LSU-wbuf0 (MA-LSU MA))) (INST-tag i))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	(and (b1p (INST-store? i))
	     (not (INST-excpt-detected-p i))
	     (equal (wbuf-addr (LSU-wbuf0 (MA-LSU MA))) (INST-store-addr i))
	     (equal (wbuf-val (LSU-wbuf0 (MA-LSU MA))) (INST-src-val3 i))))))

(defun LSU-wbuf1-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))    
  (and (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
       (not (b1p (wbuf-complete? (LSU-wbuf1 (MA-LSU MA)))))
       (not (b1p (wbuf-commit? (LSU-wbuf1 (MA-LSU MA)))))
       (equal (wbuf-tag (LSU-wbuf1 (MA-LSU MA))) (INST-tag i))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	(and (b1p (INST-store? i))
	     (not (INST-excpt-detected-p i))
	     (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) (INST-store-addr i))
	     (equal (wbuf-val (LSU-wbuf1 (MA-LSU MA))) (INST-src-val3 i))))))

(defun LSU-wbuf0-lch-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))    
  (and (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))  
       (b1p (wbuf-complete? (LSU-wbuf0 (MA-LSU MA))))
       (not (b1p (wbuf-commit? (LSU-wbuf0 (MA-LSU MA)))))
       (b1p (LSU-latch-valid? (LSU-lch (MA-LSU MA))))
       (equal (wbuf-tag (LSU-wbuf0 (MA-LSU MA))) (INST-tag i))
       (equal (LSU-latch-tag (LSU-lch (MA-LSU MA))) (INST-tag i))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	(and (b1p (INST-store? i))
	     (not (INST-fetch-error-detected-p i))
	     (not (INST-decode-error-detected-p i))
	     (equal (wbuf-addr (LSU-wbuf0 (MA-LSU MA))) (INST-store-addr i))
	     (equal (wbuf-val (LSU-wbuf0 (MA-LSU MA))) (INST-src-val3 i))
	     (equal (LSU-latch-excpt (LSU-lch (MA-LSU MA)))
		    (INST-excpt-flags i))))))

(defun LSU-wbuf1-lch-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))    
  (and (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))  
       (b1p (wbuf-complete? (LSU-wbuf1 (MA-LSU MA))))
       (not (b1p (wbuf-commit? (LSU-wbuf1 (MA-LSU MA)))))
       (b1p (LSU-latch-valid? (LSU-lch (MA-LSU MA))))
       (equal (wbuf-tag (LSU-wbuf1 (MA-LSU MA))) (INST-tag i))
       (equal (LSU-latch-tag (LSU-lch (MA-LSU MA))) (INST-tag i))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	(and (b1p (INST-store? i))
	     (not (INST-fetch-error-detected-p i))
	     (not (INST-decode-error-detected-p i))
	     (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) (INST-store-addr i))
	     (equal (wbuf-val (LSU-wbuf1 (MA-LSU MA))) (INST-src-val3 i))
	     (equal (LSU-latch-excpt (LSU-lch (MA-LSU MA)))
		    (INST-excpt-flags i))))))

(defun LSU-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))    
  (cond ((equal (INST-stg i) '(LSU RS0))
	 (LSU-RS0-inst-inv i MA))
	((equal (INST-stg i) '(LSU RS1))
	 (LSU-RS1-inst-inv i MA))
	((equal (INST-stg i) '(LSU rbuf))
	 (LSU-rbuf-inst-inv i MA))
	((equal (INST-stg i) '(LSU lch))
	 (LSU-lch-inst-inv i MA))
	((equal (INST-stg i) '(LSU wbuf0))
	 (LSU-wbuf0-inst-inv i MA))
	((equal (INST-stg i) '(LSU wbuf1))
	 (LSU-wbuf1-inst-inv i MA))
	((equal (INST-stg i) '(LSU wbuf0 lch))
	 (LSU-wbuf0-lch-inst-inv i MA))
	((equal (INST-stg i) '(LSU wbuf1 lch))
	 (LSU-wbuf1-lch-inst-inv i MA))
	(t nil)))

(defun execute-inst-robe-inv (i robe)
  (declare (xargs :guard (and (INST-p i) (rob-entry-p robe))))
  (and (b1p (robe-valid? robe))
       (not (b1p (robe-complete? robe)))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	     (equal (robe-pc robe) (ISA-pc (INST-pre-ISA i))))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i)))
		     (or (b1p (INST-fetch-error? i))
			 (b1p (INST-decode-error? i))))
		(equal (robe-excpt robe) (INST-excpt-flags i)))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i)))
		     (INST-fetch-error-detected-p i))
		(and (equal (robe-branch? robe) 0)
		     (equal (robe-sync? robe) 0)
		     (equal (robe-rfeh? robe) 0)))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i)))
		     (not (INST-fetch-error-detected-p i)))
	(and (equal (robe-wb? robe) (INST-wb? i))
	     (equal (robe-wb-sreg? robe) (INST-wb-sreg? i))
	     (equal (robe-sync? robe) (INST-sync? i))
	     (equal (robe-branch? robe) (INST-BU? i))
	     (equal (robe-rfeh? robe) (INST-rfeh? i))
	     (equal (robe-br-predict? robe) (INST-br-predict? i))
	     (implies (INST-writeback-p i)
		      (equal (robe-dest robe) (INST-dest-reg i)))
	     (implies (b1p (INST-bu? i))
		      (equal (robe-val robe) (INST-br-target i)))))))
       
(in-theory (disable IU-inst-inv MU-inst-inv BU-inst-inv LSU-inst-inv
		    execute-inst-robe-inv))

(defun execute-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))    
  (and (cond ((IU-stg-p (INST-stg i))
	      (IU-inst-inv i MA))
	     ((MU-stg-p (INST-stg i))
	      (MU-inst-inv i MA))
	     ((BU-stg-p (INST-stg i))
	      (BU-inst-inv i MA))
	     ((LSU-stg-p (INST-stg i))
	      (LSU-inst-inv i MA))
	     (t nil))
       (execute-inst-robe-inv i (nth-robe (INST-tag i) (MA-rob MA)))))

(defun complete-normal-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA)))
; Matt K. mod: Added necessary ignorable declaration.
           (ignorable MA))
  (implies (and (not (b1p (inst-specultv? i)))
		(not (b1p (INST-modified? i)))
		(not (INST-fetch-error-detected-p i))
		(not (INST-decode-error-detected-p i)))
	   (not (b1p (INST-store? i)))))
  
(defun complete-wbuf0-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))
  (and (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))  
       (b1p (wbuf-complete? (LSU-wbuf0 (MA-LSU MA))))
       (not (b1p (wbuf-commit? (LSU-wbuf0 (MA-LSU MA)))))
       (equal (wbuf-tag (LSU-wbuf0 (MA-LSU MA))) (INST-tag i))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	(and (b1p (INST-store? i))
	     (not (INST-fetch-error-detected-p i))
	     (not (INST-decode-error-detected-p i))
	     (equal (wbuf-addr (LSU-wbuf0 (MA-LSU MA))) (INST-store-addr i))
	     (equal (wbuf-val (LSU-wbuf0 (MA-LSU MA))) (INST-src-val3 i))))))

(defun complete-wbuf1-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))
  (and (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))  
       (b1p (wbuf-complete? (LSU-wbuf1 (MA-LSU MA))))
       (not (b1p (wbuf-commit? (LSU-wbuf1 (MA-LSU MA)))))
       (equal (wbuf-tag (LSU-wbuf1 (MA-LSU MA))) (INST-tag i))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	(and (b1p (INST-store? i))
	     (not (INST-fetch-error-detected-p i))
	     (not (INST-decode-error-detected-p i))
	     (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) (INST-store-addr i))
	     (equal (wbuf-val (LSU-wbuf1 (MA-LSU MA))) (INST-src-val3 i))))))
  
(defun complete-inst-robe-inv (i robe)
  (declare (xargs :guard (and (INST-p i) (rob-entry-p robe))))
  (and (b1p (robe-valid? robe))
       (b1p (robe-complete? robe))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
		(and (equal (robe-excpt robe) (INST-excpt-flags i))
		     (equal (robe-pc robe) (ISA-pc (INST-pre-ISA i)))))  
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i)))
		     (INST-fetch-error-detected-p i))
		(and (equal (robe-branch? robe) 0)
		     (equal (robe-sync? robe) 0)
		     (equal (robe-rfeh? robe) 0)))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i)))
		     (not (INST-fetch-error-detected-p i)))
	(and (equal (robe-wb? robe) (INST-wb? i))
	     (equal (robe-wb-sreg? robe) (INST-wb-sreg? i))
	     (equal (robe-sync? robe) (INST-sync? i))
	     (equal (robe-branch? robe) (INST-BU? i))
	     (equal (robe-rfeh? robe) (INST-rfeh? i))
	     (equal (robe-br-predict? robe) (INST-br-predict? i))
	     (implies (b1p (INST-BU? i))
		      (equal (robe-br-actual? robe) (INST-branch-taken? i)))
	     (implies (INST-writeback-p i)
		      (equal (robe-dest robe) (INST-dest-reg i)))
	     (implies (and (INST-writeback-p i)
			   (not (INST-decode-error-detected-p i))
			   (not (INST-data-accs-error-detected-p i)))
		      (equal (robe-val robe) (INST-dest-val i)))
	     (implies (b1p (INST-bu? i))
		      (equal (robe-val robe) (INST-br-target i)))))))

(defun complete-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))
  (and (cond ((equal (INST-stg i) '(complete))
	      (complete-normal-inst-inv i MA))
	     ((equal (INST-stg i) '(complete wbuf0))
	      (complete-wbuf0-inst-inv i MA))
	     ((equal (INST-stg i) '(complete wbuf1))
	      (complete-wbuf1-inst-inv i MA))
	     (t nil))
       (complete-inst-robe-inv i (nth-robe (INST-tag i) (MA-rob MA)))))

(defun commit-wbuf0-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))
  (and (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))  
       (not (b1p (INST-excpt? i)))
       (b1p (wbuf-complete? (LSU-wbuf0 (MA-LSU MA))))
       (b1p (wbuf-commit? (LSU-wbuf0 (MA-LSU MA))))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	(and (b1p (INST-store? i))
	     (equal (wbuf-addr (LSU-wbuf0 (MA-LSU MA))) (INST-store-addr i))
	     (equal (wbuf-val (LSU-wbuf0 (MA-LSU MA))) (INST-src-val3 i))))))

(defun commit-wbuf1-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))
  (and (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))  
       (not (b1p (INST-excpt? i)))
       (b1p (wbuf-complete? (LSU-wbuf1 (MA-LSU MA))))
       (b1p (wbuf-commit? (LSU-wbuf1 (MA-LSU MA))))
       (implies (and (not (b1p (inst-specultv? i)))
		     (not (b1p (INST-modified? i))))
	(and (b1p (INST-store? i))
	     (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA))) (INST-store-addr i))
	     (equal (wbuf-val (LSU-wbuf1 (MA-LSU MA))) (INST-src-val3 i))))))
  
(defun commit-inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))
  (cond ((equal (INST-stg i) '(commit wbuf0))
	 (commit-wbuf0-inst-inv i MA))
	((equal (INST-stg i) '(commit wbuf1))
	 (commit-wbuf1-inst-inv i MA))
	(t nil)))

; The predicates above are the stage-dependent condition that
; individual instructions should satisfy at the stage.  The following
; predicate inst-inv is true for any instruction i regardless of its
; stage. Basically, it is the conjunction of all the stage-dependent
; conditions.
(defun inst-inv (i MA)
  (declare (xargs :guard (and (INST-p i) (MA-state-p MA))))
  (cond ((IFU-stg-p (INST-stg i))
	 (IFU-inst-inv i MA))
	((DQ-stg-p (INST-stg i))
	 (DQ-inst-inv i MA))
	((execute-stg-p (INST-stg i))
	 (execute-inst-inv i MA))
	((complete-stg-p (INST-stg i))
	 (complete-inst-inv i MA))
	((commit-stg-p (INST-stg i))
	 (commit-inst-inv i MA))
	(t ; retire
	 T)))
(deflabel end-inst-inv-def)

(deftheory inst-inv-def
    (set-difference-theories (universal-theory 'end-inst-inv-def)
			     (universal-theory 'begin-inst-inv-def)))

(defun trace-INST-inv (trace MA)
  (declare (xargs :guard (and (INST-listp trace) (MA-state-p MA))))
  (if (endp trace)
      T
      (and (inst-inv (car trace) MA)
	   (trace-INST-inv (cdr trace) MA))))

; The property that intermediate results in the pipeline are correct.
(defun MT-INST-inv (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))  
  (trace-INST-inv (MT-trace MT) MA))

; ROB-flg, ROB-head and ROB-tail determines which entries in ROB are
; occupied.  If ROB-flg is on, ROB-tail is less than or equal to ROB-head,
; and a ROB entry is occupied if its index is less than ROB-tail, or it is
; larger than or equal to ROB-head.  If ROB-flg is off, ROB-tail is
; larger than or equal to ROB-head.  An entry is occupied if
; its index is less than ROB-tail and larger or equal to ROB-head.
; Note: 
; When an branch instruction is in a ROB entry, it should not have
; caused an exception.  However, this turned out to be difficult to
; verify, so we commented it out and postponed the verification.  Since
; we have completed the verification it was not a necessary condition
; for the verification of our correctness criterion.
(defun consistent-robe-p (robe idx ROB)
  (declare (xargs :guard (and (rob-entry-p robe)
			      (rob-index-p idx) (rob-p ROB))))
  (and (equal (robe-valid? robe)
	      (if (b1p (ROB-flg ROB))
		  (if (or (<= (ROB-head ROB) idx) (< idx (ROB-tail ROB)))
		      1 0)
		  (if (and (<= (ROB-head ROB) idx) (< idx (ROB-tail ROB)))
		      1 0)))
       (implies (b1p (robe-valid? robe))
;		     (not (b1p (b-and (robe-branch? robe)
;				      (excpt-raised? (robe-excpt robe)))))
		(and (not (b1p (b-and (robe-branch? robe) (robe-sync? robe))))
		     (not (b1p (b-and (robe-wb? robe) (robe-sync? robe))))))))

(defun consistent-rob-entries-p (entries idx ROB)
  (declare (xargs :guard (and (rob-p rob) (rob-index-p idx)
			      (ROBE-listp entries))))
  (if (endp entries)
      T
    (and (consistent-robe-p (car entries) idx ROB)
	 (consistent-rob-entries-p (cdr entries) (rob-index (1+ idx)) ROB))))

(defun consistent-rob-flg-p (ROB)
  (declare (xargs :guard (rob-p rob)))
  (if (b1p (ROB-flg ROB))
      (<= (ROB-tail ROB) (ROB-head ROB))
      (<= (ROB-head ROB) (ROB-tail ROB))))

(defun consistent-rob-p (ROB)
  (declare (xargs :guard (rob-p rob)))
  (and (consistent-rob-entries-p (ROB-entries ROB) 0 ROB)
       (consistent-rob-flg-p ROB)))

(defun consistent-cntlv-p (cntlv)
  (declare (xargs :guard (cntlv-p cntlv)))
  (not (b1p (bs-ior (b-and (logbit 0 (cntlv-exunit cntlv))
			   (logbit 1 (cntlv-exunit cntlv)))
		    (b-and (logbit 0 (cntlv-exunit cntlv))
			   (logbit 2 (cntlv-exunit cntlv)))
		    (b-and (logbit 0 (cntlv-exunit cntlv))
			   (logbit 3 (cntlv-exunit cntlv)))
		    (b-and (logbit 0 (cntlv-exunit cntlv))
			   (logbit 4 (cntlv-exunit cntlv)))
		    (b-and (logbit 1 (cntlv-exunit cntlv))
			   (logbit 2 (cntlv-exunit cntlv)))
		    (b-and (logbit 1 (cntlv-exunit cntlv))
			   (logbit 3 (cntlv-exunit cntlv)))
		    (b-and (logbit 1 (cntlv-exunit cntlv))
			   (logbit 4 (cntlv-exunit cntlv)))
		    (b-and (logbit 2 (cntlv-exunit cntlv))
			   (logbit 3 (cntlv-exunit cntlv)))
		    (b-and (logbit 2 (cntlv-exunit cntlv))
			   (logbit 4 (cntlv-exunit cntlv)))
		    (b-and (logbit 3 (cntlv-exunit cntlv))
			   (logbit 4 (cntlv-exunit cntlv)))
		    (b-and (logbit 3 (cntlv-exunit cntlv))
			   (cntlv-sync? cntlv))
		    (b-and (cntlv-wb? cntlv)
			   (cntlv-sync? cntlv))))))

(defun consistent-DQ-cntlv-p (DQ)
  (declare (xargs :guard (DQ-p DQ)))
  (and (implies (b1p (DE-valid? (DQ-DE0 DQ)))
		(consistent-cntlv-p (DE-cntlv (DQ-DE0 DQ))))
       (implies (b1p (DE-valid? (DQ-DE1 DQ)))
		(consistent-cntlv-p (DE-cntlv (DQ-DE1 DQ))))
       (implies (b1p (DE-valid? (DQ-DE2 DQ)))
		(consistent-cntlv-p (DE-cntlv (DQ-DE2 DQ))))
       (implies (b1p (DE-valid? (DQ-DE3 DQ)))
		(consistent-cntlv-p (DE-cntlv (DQ-DE3 DQ))))))
       
(defun consistent-LSU-p (LSU)
  (declare (xargs :guard (load-store-unit-p LSU)))
  (and (implies (and (b1p (rbuf-valid? (LSU-rbuf LSU)))
		     (b1p (rbuf-wbuf0? (LSU-rbuf LSU))))
		(b1p (wbuf-valid? (LSU-wbuf0 LSU))))
       (implies (and (b1p (rbuf-valid? (LSU-rbuf LSU)))
		     (b1p (rbuf-wbuf1? (LSU-rbuf LSU))))
		(b1p (wbuf-valid? (LSU-wbuf1 LSU))))
       (implies (b1p (wbuf-valid? (LSU-wbuf1 LSU)))
		(b1p (wbuf-valid? (LSU-wbuf0 LSU))))))
		
		
; A miscellaneous conditions. 
(defun consistent-MA-p (MA)
  (declare (xargs :guard (MA-state-p MA)))
  (and (consistent-DQ-cntlv-p (MA-DQ MA))
       (consistent-rob-p (MA-ROB MA))
       (consistent-LSU-p (MA-LSU MA))))

(defun no-dispatched-inst-p (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace)
      T
      (and (not (dispatched-p (car trace)))
	   (no-dispatched-inst-p (cdr trace)))))

(defun no-commit-inst-p (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace)
      T
      (and (not (committed-p (car trace)))
	   (no-commit-inst-p (cdr trace)))))

(defun in-order-trace-p (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace)
      T
      (and (cond ((IFU-stg-p (INST-stg (car trace))) (endp (cdr trace)))
		 ((not (dispatched-p (car trace)))
		  (no-dispatched-inst-p (cdr trace)))
		 ((not (committed-p (car trace)))
		  (no-commit-inst-p (cdr trace)))
		 (t			
		  t))
	   (in-order-trace-p (cdr trace)))))

; Instructions are dispatched and committed in order.
(defun in-order-dispatch-commit-p (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (in-order-trace-p (MT-trace MT)))

(defun in-order-DQ-trace-p (trace idx)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace)
      t
      (if (IFU-stg-p (INST-stg (car trace)))
	  t
	  (if (DQ-stg-p (INST-stg (car trace)))
	      (and (equal (DQ-stg-idx (INST-stg (car trace))) idx)
		   (in-order-DQ-trace-p (cdr trace) (+ 1 idx)))
	      (in-order-DQ-trace-p (cdr trace) idx)))))
			    
; The dispatch queue is a FIFO queue.
(defun in-order-DQ-p (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (in-order-DQ-trace-p (MT-trace MT) 0))

(defun no-INST-at-wbuf0-p (trace)	     
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace) T
      (and (not (wbuf0-stg-p (INST-stg (car trace))))
	   (no-INST-at-wbuf0-p (cdr trace)))))

(defun no-INST-at-wbuf1-p (trace)	     
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace) T
      (and (not (wbuf1-stg-p (INST-stg (car trace))))
	   (no-INST-at-wbuf1-p (cdr trace)))))

(defun no-INST-at-wbuf-p (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace) T
      (and (not (wbuf-stg-p (INST-stg (car trace))))
	   (no-INST-at-wbuf-p (cdr trace)))))
		
; The instructions in the write-buffer should be in the correct order;
; the instruction in wbuf0 should precede the instruction in wbuf1. 
(defun in-order-WB-trace-p (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace) T
      (and (implies (wbuf1-stg-p (INST-stg (car trace)))
		    (no-INST-at-wbuf0-p (cdr trace)))
	   (in-order-WB-trace-p (cdr trace)))))

(defun no-retired-store-p (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace) T
      (and (not (and (retire-stg-p (INST-stg (car trace)))
		     (b1p (INST-store? (car trace)))))
	   (no-retired-store-p (cdr trace)))))

; Store instructions should retire in program order.
(defun in-order-WB-retire-p (trace)
  (declare (xargs :guard (INST-listp trace)))  
  (if (endp trace) T
      (and (implies (wbuf0-stg-p (INST-stg (car trace)))
		    (no-retired-store-p (cdr trace)))
	   (in-order-WB-retire-p (cdr trace)))))
					

(defun LSU-issued-stg-p (stg)
  (declare (xargs :guard (stage-p stg)))
  (or (equal stg '(LSU wbuf0))
      (equal stg '(LSU wbuf1))
      (equal stg '(LSU rbuf))
      (equal stg '(LSU wbuf0 lch))
      (equal stg '(LSU wbuf1 lch))
      (equal stg '(LSU lch))
      (equal stg '(complete wbuf0))
      (equal stg '(complete wbuf1))
      (equal stg '(commit wbuf0))
      (equal stg '(commit wbuf1))))
			
(defun no-issued-LSU-inst-p (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace) T
      (and (not (LSU-issued-stg-p (INST-stg (car trace))))
	   (no-issued-LSU-inst-p (cdr trace)))))

; Instructions in LSU should be issued in the program order.
(defun in-order-LSU-issue-p (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace) T
      (and (implies (or (equal (INST-stg (car trace)) '(LSU RS0))
			(equal (INST-stg (car trace)) '(LSU RS1)))
		    (no-issued-LSU-inst-p (cdr trace)))
	   (in-order-LSU-issue-p (cdr trace)))))

; Instructions in the reservations stations attached to LSU should be in the
; correct order, depending on the flag LSU-rs1-head.
(defun in-order-LSU-RS-p (trace MA)
  (declare (xargs :guard (and (INST-listp trace) (MA-state-p MA))))
  (if (endp trace) T
      (and (cond ((and (b1p (LSU-rs1-head? (MA-LSU MA)))
		       (equal (INST-stg (car trace)) '(LSU RS0)))
		  (no-INST-at-stg-in-trace '(LSU RS1) (cdr trace)))
		 ((and (not (b1p (LSU-rs1-head? (MA-LSU MA))))
		       (equal (INST-stg (car trace)) '(LSU RS1)))
		  (no-INST-at-stg-in-trace '(LSU RS0) (cdr trace)))
		 (t t))
	   (in-order-LSU-RS-p (cdr trace) MA))))

; The following predicate is true, if the instruction in wbuf0 appears
; earlier in trace than the instruction at rbuf.  Similarly, following
; predicates define the order of instructions in the read and write
; buffers.
(defun in-order-wbuf0-rbuf-p (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace) t
      (and (implies  (equal (INST-stg (car trace)) '(LSU rbuf))
		     (no-INST-at-wbuf0-p (cdr trace)))
	   (in-order-wbuf0-rbuf-p (cdr trace)))))

(defun in-order-rbuf-wbuf0-p (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace) t
      (and (implies  (wbuf0-stg-p (INST-stg (car trace)))
		     (no-INST-at-stg-in-trace '(LSU rbuf) (cdr trace)))
	   (in-order-rbuf-wbuf0-p (cdr trace)))))

(defun in-order-wbuf1-rbuf-p (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace) t
      (and (implies  (equal (INST-stg (car trace)) '(LSU rbuf))
		     (no-INST-at-wbuf1-p (cdr trace)))
	   (in-order-wbuf1-rbuf-p (cdr trace)))))

(defun in-order-rbuf-wbuf1-p (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace) t
      (and (implies  (wbuf1-stg-p (INST-stg (car trace)))
		     (no-INST-at-stg-in-trace '(LSU rbuf) (cdr trace)))
	   (in-order-rbuf-wbuf1-p (cdr trace)))))
      

; Rbuf-wbuf0? records whether the instruction stored in wbuf0 precedes the
; instruction stored in rbuf.  According to the flag, the instructions should
; be recorded in MT in the correct order.  Similarly with rbuf-wbuf1?.
(defun in-order-load-store-p (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (and (implies (and (b1p (rbuf-valid? (LSU-rbuf (MA-LSU MA))))
		     (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
		(if (b1p (rbuf-wbuf0? (LSU-rbuf (MA-LSU MA))))
		    (in-order-wbuf0-rbuf-p (MT-trace MT))
		    (in-order-rbuf-wbuf0-p (MT-trace MT))))
       (implies (and (b1p (rbuf-valid? (LSU-rbuf (MA-LSU MA))))
		     (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
		(if (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA))))
		    (in-order-wbuf1-rbuf-p (MT-trace MT))
		    (in-order-rbuf-wbuf1-p (MT-trace MT))))))
		

; This predicate checks instructions are stored in LSU in a certain order. 
; The violation of the constraints causes incorrect memory operations. 
(defun in-order-LSU-inst-p (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (and (in-order-WB-trace-p (MT-trace MT))
       (in-order-LSU-issue-p (MT-trace MT))
       (in-order-LSU-RS-p (MT-trace MT) MA)
       (in-order-WB-retire-p (MT-trace MT))
       (in-order-load-store-p MT MA)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  Various functions for register modifiers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Definition of Last Register Modifiers in the ROB.  The ROB records
; all instructions that are dispatched but not yet committed.  When an
; instruction is dispatched, its destination register does not contain
; the correct register value as a source value of following
; instructions.  Each register records which instruction should
; eventually writes the correct value of register in the future.
; (This information is stored in the register reference table.)  We
; call this instruction as the last register modifier in the ROB.  The
; last register modifier I of register idx in the ROB can be
; characterized by three conditions.
; 1. I is dispatched but not yet committed.
; 2. I writes back its result to the register idx.
; 3. I is the last instruction in program order of all such
; instructions. 
; We define a function that tells whether there is any modifier of
; register idx in the ROB, and a function that returns the last
; register modifier. 
; 
; Instruction i modifies register idx.
(defun reg-modifier-p (idx i)
  (declare (xargs :guard (and (rname-p idx) (INST-p i))))
  (and (b1p (INST-wb? i)) (not (b1p (INST-wb-sreg? i)))
       (equal (INST-dest-reg i) idx)))

; Instruction i modifies special register idx.
(defun sreg-modifier-p (idx i)
  (declare (xargs :guard (and (rname-p idx) (INST-p i))))
  (and (b1p (INST-wb? i))  (b1p (INST-wb-sreg? i))
       (equal (INST-dest-reg i) idx)))
  

; trace-exist-LRM-in-ROB-p is used to define exist-LRM-in-ROB-p.
(defun trace-exist-LRM-in-ROB-p (idx trace)
  (declare (xargs :guard (and (rname-p idx) (INST-listp trace))))
  (if (endp trace)
      nil
      (if (and (dispatched-p (car trace))
	       (not (committed-p (car trace)))
	       (reg-modifier-p idx (car trace)))
	  t
	  (trace-exist-LRM-in-ROB-p idx (cdr trace)))))

; (exist-LRM-in-ROB-p idx MT) is true if there exists a register
; modifier of register idx in the ROB in the state represented by
; MT. (If an instruction is dispatched and not committed, it is
; assigned to an entry in the ROB.)
(defun exist-LRM-in-ROB-p (idx MT)
  (declare (xargs :guard (and (rname-p idx) (MAETT-p MT))))
  (trace-exist-LRM-in-ROB-p idx (MT-trace MT)))

(defun trace-exist-LSRM-in-ROB-p (idx trace)
  (declare (xargs :guard (and (rname-p idx) (INST-listp trace))))
  (if (endp trace)
      nil
      (if (and (dispatched-p (car trace))
	       (not (committed-p (car trace)))
	       (sreg-modifier-p idx (car trace)))
	  t
	  (trace-exist-LSRM-in-ROB-p idx (cdr trace)))))

; (exist-LSRM-in-ROB-p idx MT) is t when there exists an register
; modifier of register idx in ROB in the state represented by MT.
(defun exist-LSRM-in-ROB-p (idx MT)
  (declare (xargs :guard (and (rname-p idx) (MAETT-p MT))))
  (trace-exist-LSRM-in-ROB-p idx (MT-trace MT)))

(defun trace-LRM-in-ROB (idx trace )
  (declare (xargs :guard (and (rname-p idx) (INST-listp trace))))
  (if (endp trace)
      nil
      (if (and (dispatched-p (car trace))
	       (not (committed-p (car trace)))
	       (reg-modifier-p idx (car trace))
	       (not (trace-exist-LRM-in-ROB-p idx (cdr trace))))
	  (car trace)
	  (trace-LRM-in-ROB idx (cdr trace)))))

; The last register modifier of register idx in ROB. 
(defun LRM-in-ROB (idx MT)
  (declare (xargs :guard (and (rname-p idx) (MAETT-p MT))))  
  (trace-LRM-in-ROB idx (MT-trace MT)))

(in-theory (disable LRM-in-ROB))

(defun trace-LSRM-in-ROB (idx trace )
  (declare (xargs :guard (and (rname-p idx) (INST-listp trace))))
  (if (endp trace)
      nil
      (if (and (dispatched-p (car trace))
	       (not (committed-p (car trace)))
	       (sreg-modifier-p idx (car trace))
	       (not (trace-exist-LSRM-in-ROB-p idx (cdr trace))))
	  (car trace)
	  (trace-LSRM-in-ROB idx (cdr trace)))))

; The last register modifier of special register idx in the ROB in
; the state represented by MT. 
(defun LSRM-in-ROB (idx MT)
  (declare (xargs :guard (and (rname-p idx) (MAETT-p MT))))  
  (trace-LSRM-in-ROB idx (MT-trace MT)))

(in-theory (disable LSRM-in-ROB))

(defun trace-exist-LRM-before-p (i idx trace)
  (declare (xargs :guard (and (INST-p i) (rname-p idx)
			      (INST-listp trace))))
  (if (endp trace)
      nil
      (if (equal (car trace) i)
	  nil
	  (if (reg-modifier-p idx (car trace))
	      t
	      (trace-exist-LRM-before-p i idx (cdr trace))))))
	      

(defun trace-exist-LSRM-before-p (i idx trace)
  (declare (xargs :guard (and (INST-p i) (rname-p idx)
			      (INST-listp trace))))
  (if (endp trace)
      nil
      (if (equal (car trace) i)
	  nil
	  (if (sreg-modifier-p idx (car trace))
	      t
	      (trace-exist-LSRM-before-p i idx (cdr trace))))))
	      
; If there is an uncommitted modifier of register idx before instruction i,
; exist-LRM-before-p returns t.
(defun exist-LRM-before-p (i idx MT)
  (declare (xargs :guard (and (INST-p i) (rname-p idx) (MAETT-p MT))))
  (trace-exist-LRM-before-p i idx (MT-trace MT)))

; If there is an uncommitted modifier of special register idx before
; instruction i, exist-LRM-before-p returns t.
(defun exist-LSRM-before-p (i idx MT)
  (declare (xargs :guard (and (INST-p i) (rname-p idx) (MAETT-p MT))))
  (trace-exist-LSRM-before-p i idx (MT-trace MT)))

(in-theory (disable exist-LRM-before-p
		    exist-LSRM-before-p))

(defun trace-exist-uncommitted-LRM-before-p (i idx trace)
  (declare (xargs :guard (and (INST-p i) (rname-p idx)
			      (INST-listp trace))))
  (if (endp trace)
      nil
      (if (equal (car trace) i)
	  nil
	  (if (and (reg-modifier-p idx (car trace))
		   (not (committed-p (car trace))))
	      t
	      (trace-exist-uncommitted-LRM-before-p i idx (cdr trace))))))

(defun trace-exist-uncommitted-LSRM-before-p (i idx trace)
  (declare (xargs :guard (and (INST-p i) (rname-p idx)
			      (INST-listp trace))))
  (if (endp trace)
      nil
      (if (equal (car trace) i)
	  nil
	  (if (and (sreg-modifier-p idx (car trace))
		   (not (committed-p (car trace))))
	      t
	      (trace-exist-uncommitted-LSRM-before-p i idx (cdr trace))))))

; If there is an uncommitted modifier of register idx before instruction i,
; exist-uncommitted-LRM-before-p returns t.
(defun exist-uncommitted-LRM-before-p (i idx MT)
  (declare (xargs :guard (and (INST-p i) (rname-p idx) (MAETT-p MT))))
  (trace-exist-uncommitted-LRM-before-p i idx (MT-trace MT)))

; If there is an uncommitted modifier of special register idx before
; instruction i, exist-uncommitted-LRM-before-p returns t.
(defun exist-uncommitted-LSRM-before-p (i idx MT)
  (declare (xargs :guard (and (INST-p i) (rname-p idx) (MAETT-p MT))))
  (trace-exist-uncommitted-LSRM-before-p i idx (MT-trace MT)))

(in-theory (disable exist-uncommitted-LRM-before-p
		    exist-uncommitted-LSRM-before-p))

(defun trace-LRM-before (i idx trace)
  (declare (xargs :guard (and (INST-p i) (rname-p idx) (INST-listp trace))))
  (if (endp trace)
      nil
      (if (equal (car trace) i)
	  nil
	  (if (and (reg-modifier-p idx (car trace))
		   (not (trace-exist-LRM-before-p i idx (cdr trace))))
	      (car trace)
	      (trace-LRM-before i idx (cdr trace))))))

(defun trace-LSRM-before (i idx trace)
  (declare (xargs :guard (and (INST-p i) (rname-p idx) (INST-listp trace))))
  (if (endp trace)
      nil
      (if (equal (car trace) i)
	  nil
	  (if (and (sreg-modifier-p idx (car trace))
		   (not (trace-exist-LSRM-before-p i idx (cdr trace))))
	      (car trace)
	      (trace-LSRM-before i idx (cdr trace))))))

; If there is a register modifier before instruction i,
; LRM-before returns the last register modifier.
(defun LRM-before (i idx MT)
  (declare (xargs :guard (and (INST-p i) (rname-p idx) (MAETT-p MT))))
  (trace-LRM-before i idx (MT-trace MT)))

; If there is a special register modifier before instruction i,
; LSRM-before returns the last special register modifier.
(defun LSRM-before (i idx MT)
  (declare (xargs :guard (and (INST-p i) (rname-p idx) (MAETT-p MT))))
  (trace-LSRM-before i idx (MT-trace MT)))

(defthm inst-p-trace-LRM-before
    (implies (and (INST-p i)
		  (INST-listp trace)
		  (trace-exist-LRM-before-p i rname trace))
	     (INST-p (trace-LRM-before i rname trace))))

; LRM-before returns INST-p if there exists a register modifier.
(defthm inst-p-LRM-before
    (implies (and (INST-p i) (MAETT-p MT)
		  (exist-LRM-before-p i rname MT))
	     (INST-p (LRM-before i rname MT)))
  :hints (("goal" :in-theory (enable exist-LRM-before-p
				     LRM-before))))

(defthm inst-p-trace-LSRM-before-help
    (implies (and (INST-p i) (INST-listp trace)
		  (trace-exist-LSRM-before-p i rname trace))
	     (INST-p (trace-LSRM-before i rname trace))))

; LSRM-before returns INST-p if there exists a
; special register modifier.
(defthm inst-p-LSRM-before
    (implies (and (INST-p i) (MAETT-p MT)
		  (exist-LSRM-before-p i rname MT))
	     (INST-p (LSRM-before i rname MT)))
  :hints (("goal" :in-theory (enable exist-LSRM-before-p
				     LSRM-before))))

(in-theory (disable LRM-before
		    LSRM-before))

(defthm INST-p-trace-LRM-in-ROB
    (implies (and (rname-p idx) (INST-listp trace)
		  (trace-exist-LRM-in-ROB-p idx trace))
	     (INST-p (trace-LRM-in-ROB idx trace))))

; LRM-in-ROB returns an INST-p if there exist register 
; modifiers in the ROB.
(defthm INST-p-LRM-in-ROB
    (implies (and (rname-p idx) (MAETT-p MT)
		  (exist-LRM-in-ROB-p idx MT))
	     (INST-p (LRM-in-ROB idx MT)))
  :hints (("goal" :in-theory (enable exist-LRM-in-ROB-p
				     LRM-in-ROB))))

(defthm INST-p-trace-LSRM-in-ROB
    (implies (and (srname-p idx) (INST-listp trace)
		  (trace-exist-LSRM-in-ROB-p idx trace))
	     (INST-p (trace-LSRM-in-ROB idx trace))))

; LSRM-in-ROB returns an INST-p if there exist special
; register modifiers in the ROB.
(defthm INST-p-LSRM-in-ROB
    (implies (and (srname-p idx) (MAETT-p MT)
		  (exist-LSRM-in-ROB-p idx MT))
	     (INST-p (LSRM-in-ROB idx MT)))
  :hints (("goal" :in-theory (enable exist-LSRM-in-ROB-p
				     LSRM-in-ROB))))

(defthm trace-exist-LRM-if-trace-exist-uncommitted-LRM
    (implies (trace-exist-uncommitted-LRM-before-p i r trace)
	     (trace-exist-LRM-before-p i r trace))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
     (implies (not (trace-exist-LRM-before-p i r trace))
	      (not (trace-exist-uncommitted-LRM-before-p i r trace))))))

; The existence of uncommitted register modifier implies
; the existence of register modifiers in general. 
(defthm exist-LRM-if-exist-uncommitted-LRM
    (implies (exist-uncommitted-LRM-before-p i r MT)
	     (exist-LRM-before-p i r MT))
  :hints (("goal" :in-theory (enable exist-uncommitted-LRM-before-p
				     exist-LRM-before-p))))

(defthm trace-exist-LSRM-if-exist-uncommitted-LSRM
    (implies (trace-exist-uncommitted-LSRM-before-p i r trace)
	     (trace-exist-LSRM-before-p i r trace))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
     (implies (not (trace-exist-LSRM-before-p i r trace))
	      (not (trace-exist-uncommitted-LSRM-before-p i r trace))))))

; The existence of uncommitted special register modifier implies
; the existence of special register modifiers in general. 
(defthm exist-LSRM-if-exist-uncommitted-LSRM
    (implies (exist-uncommitted-LSRM-before-p i r MT)
	     (exist-LSRM-before-p i r MT))
  :hints (("goal" :in-theory (enable exist-uncommitted-LSRM-before-p
				     exist-LSRM-before-p))))

;;;;;;;;;;;;;;;;;;;Definition of mem-modifier;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Definition of memory modifiers. We define the same concept as
; register modifier with the memory.  We define
; (LMM-before i addr MT) as the last instruction that
; modifies the memory at address addr before the instruction i. 
; 
; We didn't define a concept like LRM-in-ROB.  This
; was useful in obtaining the ideal value for the field of the
; reservation station which designates the producer of the source
; operand value.   Our load store unit does load-bypassing, but this
; is done by comparing access address directly.  Thus we need not to
; generate something like Tomasulo's tag.  Thus, we did not find the
; use of functions similar to LRM-in-ROB.
(defun mem-modifier-p (addr i)
  (declare (xargs :guard (and (addr-p addr) (INST-p i))))
  (and (b1p (INST-store? i)) 
       (equal (INST-store-addr i) addr)))
(in-theory (disable mem-modifier-p))

(defun trace-exist-LMM-before-p (i addr trace)
  (declare (xargs :guard (and (INST-p i) (addr-p addr)
			      (INST-listp trace))))
  (if (endp trace)
      nil
      (if (equal (car trace) i)
	  nil
	  (if (mem-modifier-p addr (car trace))
	      t
	      (trace-exist-LMM-before-p i addr (cdr trace))))))

; If there is a memory modifier before instruction i,
; exist-LMM-before-p returns t.
(defun exist-LMM-before-p (i addr MT)
  (declare (xargs :guard (and (INST-p i) (addr-p addr) (MAETT-p MT))))
  (trace-exist-LMM-before-p i addr (MT-trace MT)))

(in-theory (disable exist-LMM-before-p))

(defun trace-LMM-before (i addr trace)
  (declare (xargs :guard (and (INST-p i) (addr-p addr) (INST-listp trace))))
  (if (endp trace)
      nil
      (if (equal (car trace) i)
	  nil
	  (if (and (mem-modifier-p addr (car trace))
		   (not (trace-exist-LMM-before-p i addr (cdr trace))))
	      (car trace)
	      (trace-LMM-before i addr (cdr trace))))))

; If there is an memory modifier before instruction i,
; LMM-before returns the last memory modifier.
(defun LMM-before (i addr MT)
  (declare (xargs :guard (and (INST-p i) (addr-p addr) (MAETT-p MT))))
  (trace-LMM-before i addr (MT-trace MT)))

                   
(defun trace-exist-non-retired-LMM-before-p (i addr trace)
  (declare (xargs :guard (and (INST-p i) (addr-p addr)
			      (INST-listp trace))))
  (if (endp trace)
      nil
      (if (equal (car trace) i)
	  nil
	  (if (and (mem-modifier-p addr (car trace))
		   (not (retire-stg-p (INST-stg (car trace)))))
	      t
	      (trace-exist-non-retired-LMM-before-p i addr (cdr trace))))))

; If there is a non-retired memory modifier before instruction i,
; exist-non-retired-LMM-before-p returns non nil.
(defun exist-non-retired-LMM-before-p (i addr MT)
  (declare (xargs :guard (and (INST-p i) (addr-p addr) (MAETT-p MT))))
  (trace-exist-non-retired-LMM-before-p i addr (MT-trace MT)))

(in-theory (disable exist-non-retired-LMM-before-p))

(encapsulate nil
(local
 (defthm inst-p-LMM-before-help
     (implies (and (INST-p i)
		   (INST-listp trace)
		   (trace-exist-LMM-before-p i addr trace))
	      (INST-p (trace-LMM-before i addr trace)))))

; LMM-before returns INST-p if there is a memory modifier.
(defthm inst-p-LMM-before
    (implies (and (INST-p i) (MAETT-p MT)
		  (exist-LMM-before-p i addr MT))
	     (INST-p (LMM-before i addr MT)))
  :hints (("goal" :in-theory (enable exist-LMM-before-p
				     LMM-before))))
)
(in-theory (disable LMM-before))

; Consistent-reg-ref-p defines the correct state of register reference
; table at entry idx.  If wait? flag in the register reference table
; is on for register idx, then there is a register modifier in ROB,
; and its tag is stored in the register reference table. 
; If wait? flag is not on, the register modifier does not exist.
; Note that the register reference table may not contain the correct
; value when the processor is executing speculatively or modified
; instruction stream at the dispatching boundary.
(defun consistent-reg-ref-p (idx MT MA)
  (declare (xargs :guard (and (rname-p idx) (MAETT-p MT) (MA-state-p MA))))
  (if (or (b1p (MT-specultv-at-dispatch? MT))
	  (b1p (MT-modified-at-dispatch? MT)))
      t
      (if (b1p (reg-ref-wait? (reg-tbl-nth idx (DQ-reg-tbl (MA-DQ MA)))))
	  (and (exist-LRM-in-ROB-p idx MT)
	       (equal (INST-tag (LRM-in-ROB idx MT))
		      (reg-ref-tag (reg-tbl-nth idx (DQ-reg-tbl (MA-DQ MA))))))
	  (not (exist-LRM-in-ROB-p idx MT)))))
  

; Similar to consistent-reg-ref-p.  It specifies that the register
; reference table for special registers contain the correct values. 
(defun consistent-sreg-ref-p (idx MT MA)
  (declare (xargs :guard (and (srname-p idx) (MAETT-p MT) (MA-state-p MA))
		  :guard-hints (("goal" :in-theory (enable srname-p)))))
  (if (or (b1p (MT-specultv-at-dispatch? MT))
	  (b1p (MT-modified-at-dispatch? MT)))
      T
    (if (b1p (reg-ref-wait? (sreg-tbl-nth idx (DQ-sreg-tbl (MA-DQ MA)))))
	(and (exist-LSRM-in-ROB-p idx MT)
	     (equal (INST-tag (LSRM-in-ROB idx MT))
		    (reg-ref-tag (sreg-tbl-nth idx (DQ-sreg-tbl (MA-DQ MA))))))
	(not (exist-LSRM-in-ROB-p idx MT)))))
  
(defun consistent-reg-tbl-under (idx MT MA)
  (declare (xargs :guard (and (integerp idx) (<= 0 idx) (<= idx *num-regs*)
			      (MAETT-p MT) (MA-state-p MA))
		  :guard-hints
		  (("goal" :in-theory (enable rname-p unsigned-byte-p)))))
  (if (zp idx)
      t
      (and (consistent-reg-ref-p (1- idx) MT MA)
	   (consistent-reg-tbl-under (1- idx) MT MA))))

; All entries in the register reference table contain the right
; values. 
(defun consistent-reg-tbl-p (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (consistent-reg-tbl-under *num-regs* MT MA))

(defun consistent-sreg-tbl-p (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (and (consistent-sreg-ref-p 0 MT MA)
       (consistent-sreg-ref-p 1 MT MA)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Definition of consistent-RS-p
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Consistent-RS-p defines the right values for the reservation
; stations.  These conditions are critical to guarantee that the
; source operand values are obtained for the right source. 
; 
; For example, let us consider consistent-IU-RS0-p.  All other
; predicates are straightforward once we understand consistent-IU-RS0-p.
; Consistent-IU-RS0-p is a conjunct of several clauses.  A hypothesis
; (not (b1p (RS-ready1? RS0))) of the first clause checks whether the
; first operand for instruction i is not ready.
; (b1p (logbit 0 (cntlv-operand cntlv))) indicates the operand
; type for which source operands are general registers RA and RB. 
; In this case, the first clause claims three things.  First, a
; uncommitted modifier of register RA exists before instruction i. 
; Second, the last register modifier of RA is still in execution
; stage. (If it is in the complete stage, the reservation station
; should have already obtained its value.)  Third, the src1 field of
; reservation station R0 contains the tag to the last register
; modifier.  If instruction i is speculatively executed, or in the
; modified stream of instruction, invariants always hold.
(deflabel begin-consistent-RS-p-def)
(defun consistent-IU-RS0-p (i MT MA)
  (declare (xargs :guard (and (INST-p i) (MAETT-p MT) (MA-state-p MA))))
  (let ((RS0 (IU-RS0 (MA-IU MA)))
	(RA (INST-RA i))
	(RB (INST-RB i))
	(RC (INST-RC i))
	(cntlv (INST-cntlv i)))
    (and (implies (and (not (b1p (inst-specultv? i)))
		       (not (b1p (INST-modified? i)))
		       (not (b1p (RS-ready1? RS0)))
		       (b1p (logbit 0 (cntlv-operand cntlv))))
		  (and (exist-uncommitted-LRM-before-p i RA MT)
		       (execute-stg-p
			(INST-stg (LRM-before i RA MT)))
		       (equal (RS-src1 RS0)
			      (INST-tag (LRM-before i RA MT)))))
	 (implies (and (not (b1p (inst-specultv? i)))
		       (not (b1p (INST-modified? i)))
		       (not (b1p (RS-ready2? RS0)))
		       (b1p (logbit 0 (cntlv-operand cntlv))))
		  (and (exist-uncommitted-LRM-before-p i RB MT)
		       (execute-stg-p
			(INST-stg (LRM-before i RB MT)))
		       (equal (RS-src2 RS0)
			      (INST-tag (LRM-before i RB MT)))))
	 (implies (and (not (b1p (inst-specultv? i)))
		       (not (b1p (INST-modified? i)))
		       (not (b1p (RS-ready1? RS0)))
		       (b1p (logbit 2 (cntlv-operand cntlv))))
		  (and (exist-uncommitted-LRM-before-p i RC MT)
		       (execute-stg-p
			(INST-stg (LRM-before i RC MT)))
		       (equal (RS-src1 RS0)
			      (INST-tag (LRM-before i RC MT)))))
	 (implies (and (not (b1p (inst-specultv? i)))
		       (not (b1p (INST-modified? i)))
		       (not (b1p (RS-ready1? RS0)))
		       (b1p (logbit 3 (cntlv-operand cntlv))))
		  (and (exist-uncommitted-LSRM-before-p i RA MT)
		       (execute-stg-p
			(INST-stg (LSRM-before i RA MT)))
		       (equal (RS-src1 RS0)
			      (INST-tag (LSRM-before i RA MT))))))))

(defun consistent-IU-RS1-p (i MT MA)
  (declare (xargs :guard (and (INST-p i) (MAETT-p MT) (MA-state-p MA))))
  (let ((RS1 (IU-RS1 (MA-IU MA)))
	(RA (INST-RA i))
	(RB (INST-RB i))
	(RC (INST-RC i))
	(cntlv (INST-cntlv i)))
    (and (implies (and (not (b1p (inst-specultv? i)))
		       (not (b1p (INST-modified? i)))
		       (not (b1p (RS-ready1? RS1)))
		       (b1p (logbit 0 (cntlv-operand cntlv))))
		  (and (exist-uncommitted-LRM-before-p i RA MT)
		       (execute-stg-p
			(INST-stg (LRM-before i RA MT)))
		       (equal (RS-src1 RS1)
			      (INST-tag (LRM-before i RA MT)))))
	 (implies (and (not (b1p (inst-specultv? i)))
		       (not (b1p (INST-modified? i)))
		       (not (b1p (RS-ready2? RS1)))
		       (b1p (logbit 0 (cntlv-operand cntlv))))
		  (and (exist-uncommitted-LRM-before-p i RB MT)
		       (execute-stg-p
			(INST-stg (LRM-before i RB MT)))
		       (equal (RS-src2 RS1)
			      (INST-tag (LRM-before i RB MT)))))
	 (implies (and (not (b1p (inst-specultv? i)))
		       (not (b1p (INST-modified? i)))
		       (not (b1p (RS-ready1? RS1)))
		       (b1p (logbit 2 (cntlv-operand cntlv))))
		  (and (exist-uncommitted-LRM-before-p i RC MT)
		       (execute-stg-p
			(INST-stg (LRM-before i RC MT)))
		       (equal (RS-src1 RS1)
			      (INST-tag (LRM-before i RC MT)))))
	 (implies (and (not (b1p (inst-specultv? i)))
		       (not (b1p (INST-modified? i)))
		       (not (b1p (RS-ready1? RS1)))
		       (b1p (logbit 3 (cntlv-operand cntlv))))
		  (and (exist-uncommitted-LSRM-before-p i RA MT)
		       (execute-stg-p
			(INST-stg (LSRM-before i RA MT)))
		       (equal (RS-src1 RS1)
			      (INST-tag (LSRM-before i RA MT))))))))

(defun consistent-IU-RS-p (i MT MA)
  (declare (xargs :guard (and (INST-p i) (MAETT-p MT) (MA-state-p MA))))
  (cond ((equal (INST-stg i) '(IU RS0))
	 (consistent-IU-RS0-p i MT MA))
	((equal (INST-stg i) '(IU RS1))
	 (consistent-IU-RS1-p i MT MA))
	(t t)))

(defun consistent-MU-RS0-p (i MT MA)
  (declare (xargs :guard (and (INST-p i) (MAETT-p MT) (MA-state-p MA))))
  (let ((RS0 (MU-RS0 (MA-MU MA)))
	(RA (INST-RA i))
	(RB (INST-RB i)))
    (and (implies (and (not (b1p (inst-specultv? i)))
		       (not (b1p (INST-modified? i)))
		       (not (b1p (RS-ready1? RS0))))
		  (and (exist-uncommitted-LRM-before-p i RA MT)
		       (execute-stg-p
			(INST-stg (LRM-before i RA MT)))
		       (equal (RS-src1 RS0)
			      (INST-tag (LRM-before i RA MT)))))
	 (implies (and (not (b1p (inst-specultv? i)))
		       (not (b1p (INST-modified? i)))
		       (not (b1p (RS-ready2? RS0))))
		  (and (exist-uncommitted-LRM-before-p i RB MT)
		       (execute-stg-p
			(INST-stg (LRM-before i RB MT)))
		       (equal (RS-src2 RS0)
			      (INST-tag (LRM-before i RB MT))))))))

(defun consistent-MU-RS1-p (i MT MA)
  (declare (xargs :guard (and (INST-p i) (MAETT-p MT) (MA-state-p MA))))
  (let ((RS1 (MU-RS1 (MA-MU MA)))
	(RA (INST-RA i))
	(RB (INST-RB i)))
    (and (implies (and (not (b1p (inst-specultv? i)))
		       (not (b1p (INST-modified? i)))
		       (not (b1p (RS-ready1? RS1))))
		  (and (exist-uncommitted-LRM-before-p i RA MT)
		       (execute-stg-p
			(INST-stg (LRM-before i RA MT)))
		       (equal (RS-src1 RS1)
			      (INST-tag (LRM-before i RA MT)))))
	 (implies (and (not (b1p (inst-specultv? i)))
		       (not (b1p (INST-modified? i)))
		       (not (b1p (RS-ready2? RS1))))
		  (and (exist-uncommitted-LRM-before-p i RB MT)
		       (execute-stg-p
			(INST-stg (LRM-before i RB MT)))
		       (equal (RS-src2 RS1)
			      (INST-tag (LRM-before i RB MT))))))))

(defun consistent-MU-RS-p (i MT MA)
  (declare (xargs :guard (and (INST-p i) (MAETT-p MT) (MA-state-p MA))))
  (cond ((equal (INST-stg i) '(MU RS0))
	 (consistent-MU-RS0-p i MT MA))
	((equal (INST-stg i) '(MU RS1))
	 (consistent-MU-RS1-p i MT MA))
	(t t)))

(defun consistent-BU-RS0-p (i MT MA)
  (declare (xargs :guard (and (INST-p i) (MAETT-p MT) (MA-state-p MA))))
  (let ((RS0 (BU-RS0 (MA-BU MA)))
	(RC (INST-RC i)))
    (and (implies (and (not (b1p (inst-specultv? i)))
		       (not (b1p (INST-modified? i)))
		       (not (b1p (BU-RS-ready? RS0))))
		  (and (exist-uncommitted-LRM-before-p i RC MT)
		       (execute-stg-p
			(INST-stg (LRM-before i RC MT)))
		       (equal (BU-RS-src RS0)
			      (INST-tag (LRM-before i RC MT))))))))

(defun consistent-BU-RS1-p (i MT MA)
  (declare (xargs :guard (and (INST-p i) (MAETT-p MT) (MA-state-p MA))))
  (let ((RS1 (BU-RS1 (MA-BU MA)))
	(RC (INST-RC i)))
    (and (implies (and (not (b1p (inst-specultv? i)))
		       (not (b1p (INST-modified? i)))
		       (not (b1p (BU-RS-ready? RS1))))
		  (and (exist-uncommitted-LRM-before-p i RC MT)
		       (execute-stg-p
			(INST-stg (LRM-before i RC MT)))
		       (equal (BU-RS-src RS1)
			      (INST-tag (LRM-before i RC MT))))))))

(defun consistent-BU-RS-p (i MT MA)
  (declare (xargs :guard (and (INST-p i) (MAETT-p MT) (MA-state-p MA))))
  (cond ((equal (INST-stg i) '(BU RS0))
	 (consistent-BU-RS0-p i MT MA))
	((equal (INST-stg i) '(BU RS1))
	 (consistent-BU-RS1-p i MT MA))
	(t t)))

(defun consistent-LSU-RS0-p (i MT MA)
  (declare (xargs :guard (and (INST-p i) (MAETT-p MT) (MA-state-p MA))))
  (let ((RS0 (LSU-RS0 (MA-LSU MA)))
	(RA (INST-RA i))
	(RB (INST-RB i))
	(RC (INST-RC i)))
    (and (implies (and (not (b1p (inst-specultv? i)))
		       (not (b1p (INST-modified? i)))
		       (not (b1p (LSU-RS-rdy1? RS0))))
		  (and (exist-uncommitted-LRM-before-p i RA MT)
		       (execute-stg-p
			(INST-stg (LRM-before i RA MT)))
		       (equal (LSU-RS-src1 RS0)
			      (INST-tag (LRM-before i RA MT)))))
	 (implies (and (not (b1p (inst-specultv? i)))
		       (not (b1p (INST-modified? i)))
		       (not (b1p (LSU-RS-rdy2? RS0))))
		  (and (exist-uncommitted-LRM-before-p i RB MT)
		       (execute-stg-p
			(INST-stg (LRM-before i RB MT)))
		       (equal (LSU-RS-src2 RS0)
			      (INST-tag (LRM-before i RB MT)))))
	 (implies (and (not (b1p (inst-specultv? i)))
		       (not (b1p (INST-modified? i)))
		       (not (b1p (LSU-RS-rdy3? RS0))))
		  (and (exist-uncommitted-LRM-before-p i RC MT)
		       (execute-stg-p
			(INST-stg (LRM-before i RC MT)))
		       (equal (LSU-RS-src3 RS0)
			      (INST-tag (LRM-before i RC MT))))))))

(defun consistent-LSU-RS1-p (i MT MA)
  (declare (xargs :guard (and (INST-p i) (MAETT-p MT) (MA-state-p MA))))
  (let ((RS1 (LSU-RS1 (MA-LSU MA)))
	(RA (INST-RA i))
	(RB (INST-RB i))
	(RC (INST-RC i)))
    (and (implies (and (not (b1p (inst-specultv? i)))
		       (not (b1p (INST-modified? i)))
		       (not (b1p (LSU-RS-rdy1? RS1))))
		  (and (exist-uncommitted-LRM-before-p i RA MT)
		       (execute-stg-p
			(INST-stg (LRM-before i RA MT)))
		       (equal (LSU-RS-src1 RS1)
			      (INST-tag (LRM-before i RA MT)))))
	 (implies (and (not (b1p (inst-specultv? i)))
		       (not (b1p (INST-modified? i)))
		       (not (b1p (LSU-RS-rdy2? RS1))))
		  (and (exist-uncommitted-LRM-before-p i RB MT)
		       (execute-stg-p
			(INST-stg (LRM-before i RB MT)))
		       (equal (LSU-RS-src2 RS1)
			      (INST-tag (LRM-before i RB MT)))))
	 (implies (and (not (b1p (inst-specultv? i)))
		       (not (b1p (INST-modified? i)))
		       (not (b1p (LSU-RS-rdy3? RS1))))
		  (and (exist-uncommitted-LRM-before-p i RC MT)
		       (execute-stg-p
			(INST-stg (LRM-before i RC MT)))
		       (equal (LSU-RS-src3 (LSU-RS1 (MA-LSU MA)))
			      (INST-tag (LRM-before i RC MT))))))))

(defun consistent-LSU-RS-p (i MT MA)
  (declare (xargs :guard (and (INST-p i) (MAETT-p MT) (MA-state-p MA))))
  (cond ((equal (INST-stg i) '(LSU RS0))
	 (consistent-LSU-RS0-p i MT MA))
	((equal (INST-stg i) '(LSU RS1))
	 (consistent-LSU-RS1-p i MT MA))
	(t t)))
	
; Consistent-RS-entry-p is true if the reservation station stores
; correct info about i.  
(defun consistent-RS-entry-p (i MT MA)
  (declare (xargs :guard (and (INST-p i) (MAETT-p MT) (MA-state-p MA))))
  (cond ((IU-stg-p (INST-stg i)) (consistent-IU-RS-p i MT MA))
	((MU-stg-p (INST-stg i)) (consistent-MU-RS-p i MT MA))
	((BU-stg-p (INST-stg i)) (consistent-BU-RS-p i MT MA))
	((LSU-stg-p (INST-stg i)) (consistent-LSU-RS-p i MT MA))
	(t t)))

(defun trace-consistent-RS-p (trace MT MA)
  (declare (xargs :guard (and (INST-listp trace)
			      (MAETT-p MT) (MA-state-p MA))))
  (if (endp trace)
      t
      (and (consistent-RS-entry-p (car trace) MT MA)
	   (trace-consistent-RS-p (cdr trace) MT MA))))

; All reservation stations contain the right values to keep track of
; instructions that supply the operand values. 
(defun consistent-RS-p (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (trace-consistent-RS-p (MT-trace MT) MT MA))
(deflabel end-consistent-RS-p-def)
(deftheory consistent-RS-p-def
    (set-difference-theories (universal-theory 'end-consistent-RS-p-def)
			     (universal-theory 'begin-consistent-RS-p-def)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Definition of in-order-ROB-p
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; ROB is a FIFO buffer.  Instructions are dispatched and committed in
; program order, and the ROB records them in that order.  Since the
; pointer to the head is incremented every time a new entry comes in,
; and wrapped around when the bottom is reached.  Thus, the ROB
; index idx1 to instruction I1 and index idx2 to the next instruction
; I2 are related as idx2 = (rob-index (+ 1 idx1)).  See MA2-def.lisp
; for detail.
(defun in-order-ROB-trace-p (trace idx)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace)
      T
      (if (or (IFU-stg-p (INST-stg (car trace)))
	      (DQ-stg-p (INST-stg (car trace))))
	  T
	  (if (or (complete-stg-p (INST-stg (car trace)))
		  (execute-stg-p (INST-stg (car trace))))
	      (and (equal (INST-tag (car trace)) idx)
		   (in-order-ROB-trace-p (cdr trace) (rob-index (+ 1 idx))))
	      (in-order-ROB-trace-p (cdr trace) idx)))))

(defun in-order-ROB-p (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (in-order-ROB-trace-p (MT-trace MT) (MT-rob-head MT)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Definition of no-stage-conflict 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; No-stage-conflict defines that no structural conflicts occur on
; pipeline latches.
; No two instructions share the same stage.  This is verified by case 
; analysis on each pipeline stage.  For instance, no-IFU-stg-conflict
; guarantees that no instruction share the IFU stage at a time.
; This is represented by uniq-INST-at-stg and no-INST-at-stg.  
; If IFU-valid? is 1, there exists only one instruction at stage
; (IFU).  If 0, no instruction should be at (IFU).
(defun no-IFU-stg-conflict (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (if (b1p (IFU-valid? (MA-IFU MA)))
      (uniq-INST-at-stg '(IFU) MT)
      (no-INST-at-stg '(IFU) MT)))

(defun no-DQ-stg-conflict (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (and (if (b1p (DE-valid? (DQ-DE0 (MA-DQ MA))))
	   (uniq-INST-at-stg '(DQ 0) MT)
	   (no-INST-at-stg '(DQ 0) MT))
       (if (b1p (DE-valid? (DQ-DE1 (MA-DQ MA))))
	   (uniq-INST-at-stg '(DQ 1) MT)
	   (no-INST-at-stg '(DQ 1) MT))
       (if (b1p (DE-valid? (DQ-DE2 (MA-DQ MA))))
	   (uniq-INST-at-stg '(DQ 2) MT)
	   (no-INST-at-stg '(DQ 2) MT))       
       (if (b1p (DE-valid? (DQ-DE3 (MA-DQ MA))))
	   (uniq-INST-at-stg '(DQ 3) MT)
	   (no-INST-at-stg '(DQ 3) MT))))

(defun no-IU-stg-conflict (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (and (if (b1p (RS-valid? (IU-RS0 (MA-IU MA))))
	   (uniq-INST-at-stg '(IU RS0) MT)
	   (no-INST-at-stg '(IU RS0) MT))
       (if (b1p (RS-valid? (IU-RS1 (MA-IU MA))))
	   (uniq-INST-at-stg '(IU RS1) MT)
	   (no-INST-at-stg '(IU RS1) MT))))

(defun no-BU-stg-conflict (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (and (if (b1p (BU-RS-valid? (BU-RS0 (MA-BU MA))))
	   (uniq-INST-at-stg '(BU RS0) MT)
	   (no-INST-at-stg '(BU RS0) MT))
       (if (b1p (BU-RS-valid? (BU-RS1 (MA-BU MA))))
	   (uniq-INST-at-stg '(BU RS1) MT)
	   (no-INST-at-stg '(BU RS1) MT))))

(defun no-MU-stg-conflict (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (and (if (b1p (RS-valid? (MU-RS0 (MA-MU MA))))
	   (uniq-INST-at-stg '(MU RS0) MT)
	   (no-INST-at-stg '(MU RS0) MT))
       (if (b1p (RS-valid? (MU-RS1 (MA-MU MA))))
	   (uniq-INST-at-stg '(MU RS1) MT)
	   (no-INST-at-stg '(MU RS1) MT))
       (if (b1p (MU-latch1-valid? (MU-lch1 (MA-MU MA))))
	   (uniq-INST-at-stg '(MU lch1) MT)
	   (no-INST-at-stg '(MU lch1) MT))
       (if (b1p (MU-latch2-valid? (MU-lch2 (MA-MU MA))))
	   (uniq-INST-at-stg '(MU lch2) MT)
	   (no-INST-at-stg '(MU lch2) MT))))

(defun no-LSU-stg-conflict (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (and (if (b1p (LSU-RS-valid? (LSU-RS0 (MA-LSU MA))))
	   (uniq-INST-at-stg '(LSU RS0) MT)
	   (no-INST-at-stg '(LSU RS0) MT))
       (if (b1p (LSU-RS-valid? (LSU-RS1 (MA-LSU MA))))
	   (uniq-INST-at-stg '(LSU RS1) MT)
	   (no-INST-at-stg '(LSU RS1) MT))
       (if (b1p (rbuf-valid? (LSU-rbuf (MA-LSU MA))))
	   (uniq-INST-at-stg '(LSU rbuf) MT)
	   (no-INST-at-stg '(LSU rbuf) MT))
       (if (b1p (LSU-latch-valid? (LSU-lch (MA-LSU MA))))
	   (uniq-INST-at-stgs '((LSU lch)
				(LSU wbuf0 lch)
				(LSU wbuf1 lch))
			      MT)
	   (no-INST-at-stgs '((LSU lch)
			      (LSU wbuf0 lch)
			      (LSU wbuf1 lch))
			    MT))
       (if (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
	   (uniq-INST-at-stgs '((LSU wbuf0)
				(LSU wbuf0 lch)
				(complete wbuf0)
				(commit wbuf0))
			      MT)
	   (no-INST-at-stgs '((LSU wbuf0)
			      (LSU wbuf0 lch)
			      (complete wbuf0)
			      (commit wbuf0))
			    MT))
       (if (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
	   (uniq-INST-at-stgs '((LSU wbuf1)
				(LSU wbuf1 lch)
				(complete wbuf1)
				(commit wbuf1))
			      MT)
	   (no-INST-at-stgs '((LSU wbuf1)
			      (LSU wbuf1 lch)
			      (complete wbuf1)
			      (commit wbuf1))
			    MT))))

; No structural conflicts occur at any pipeline latch.  See comments above.
(defun no-stage-conflict (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (and (no-IFU-stg-conflict MT MA)
       (no-DQ-stg-conflict MT MA)
       (no-IU-stg-conflict MT MA)
       (no-MU-stg-conflict MT MA)
       (no-LSU-stg-conflict MT MA)
       (no-BU-stg-conflict MT MA)))

; No-tag-conflict defines that no structural conflict occurs in the
; ROB.  In other words, no ROB entry is shared by more than one
; instruction.  It also implies that the tag used in the Tomasulo's
; algorithm is unique, because we use the index to the ROB entry which
; is allocated to an instruction as its tag.
; 
; No-tag-conflict-at defines whether there is no structural hazard at 
; ROB entry indexed by idx.  If valid? flag of that entry is 1, there
; exists a uniq instruction assigned to that entry. If 0, no
; instruction is assigned. 
(defun no-tag-conflict-at (idx MT MA)
  (declare (xargs :guard (and (rob-index-p idx) (MAETT-p MT) (MA-state-p MA))))
  (if (b1p (robe-valid? (nth-robe idx (MA-rob MA))))
      (uniq-inst-of-tag idx MT)
      (no-inst-of-tag idx MT)))

(defun no-tag-conflict-under (idx MT MA)
  (declare (xargs :guard (and (integerp idx) (<= 0 idx) (<= idx *rob-size*)
			      (MAETT-p MT) (MA-state-p MA))
		  :guard-hints
		  (("goal" :in-theory (enable rob-index-p unsigned-byte-p)))))
  (if (zp idx)
      t
      (and (no-tag-conflict-at (1- idx) MT MA)
	   (no-tag-conflict-under (1- idx) MT MA))))

; No structural conflict occurs in the ROB. 
; See the comment above.
(defun no-tag-conflict (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (no-tag-conflict-under *rob-size* MT MA))

;;;; Definition of misc-inv
; correct-entries-in-DQ-p is a part of misc-inv.
; This function checks whether the dispatch queue contains the correct
; number of instructions suggested by MT-DQ-len.  If index is smaller
; than MT-DQ-len, the entry with the index should contain an instruction.
(defun correct-entries-in-DQ-p (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (and (iff (< 0 (MT-DQ-len MT)) (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
       (iff (< 1 (MT-DQ-len MT)) (b1p (DE-valid? (DQ-DE1 (MA-DQ MA)))))
       (iff (< 2 (MT-DQ-len MT)) (b1p (DE-valid? (DQ-DE2 (MA-DQ MA)))))
       (iff (< 3 (MT-DQ-len MT)) (b1p (DE-valid? (DQ-DE3 (MA-DQ MA)))))))

; Misc invariants.
; MT-rob-head and MT-rob-tail records the correct index of head and tail
; entries in ROB.
; MT-DQ-len must record the number of instructions in dispatch queue.
;
(defun misc-inv (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (and (equal (rob-flg (MA-rob MA)) (MT-rob-flg MT))
       (equal (rob-head (MA-rob MA)) (MT-rob-head MT))
       (equal (rob-tail (MA-rob MA)) (MT-rob-tail MT))
       (<= (MT-DQ-len MT) 4)
       (correct-entries-in-DQ-p MT MA)))

; Definition of strong invariants, which is a conjunction of all properties
; defined above.
(defun inv (MT MA)
  (declare (xargs :guard (and (MAETT-p MT) (MA-state-p MA))))
  (and (weak-inv MT)
       (pc-match-p MT MA)
       (SRF-match-p MT MA)
       (RF-match-p MT MA)
       (mem-match-p MT MA)
       (no-specultv-commit-p MT)
       (correct-speculation-p MT)
       (correct-exintr-p MT)
       (MT-INST-inv MT MA)
       (in-order-dispatch-commit-p MT)
       (in-order-DQ-p MT)
       (in-order-LSU-inst-p MT MA)
       (in-order-ROB-p MT)
       (consistent-RS-p MT MA)
       (consistent-reg-tbl-p MT MA)
       (consistent-sreg-tbl-p MT MA)
       (no-stage-conflict MT MA)
       (no-tag-conflict MT MA)
       (consistent-MA-p MA)
       (misc-inv MT MA)))

(deflabel end-invariants-def)

(deftheory invariants-def 
    (set-difference-theories (function-theory 'end-invariants-def)
			     (function-theory 'begin-invariants-def)))

(deftheory invariants-def-non-rec-functions
    (non-rec-functions (theory 'invariants-def) world))

(in-theory (disable invariants-def-non-rec-functions))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Forward-chaining of weak invariants wk-inv
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deflabel begin-invariants-forward-lemmas)

(defthm weak-invariants-forward
    (implies (inv MT MA)
	     (weak-inv MT))
  :hints (("goal" :In-theory (enable inv)))
  :rule-classes :forward-chaining)

(defthm MT-new-ID-distinct-p-forward-2
    (implies (weak-inv MT)
	     (MT-new-ID-distinct-p MT))
  :hints (("Goal" :in-theory (enable weak-inv)))
  :rule-classes :forward-chaining)

(defthm MT-distinct-IDs-p-forward-2
    (implies (weak-inv MT)
	     (MT-distinct-IDs-p MT))
  :hints (("Goal" :in-theory (enable weak-inv)))
  :rule-classes :forward-chaining)

(defthm MT-distinct-chain-p-forward-2
    (implies (weak-inv MT)
	     (MT-distinct-INST-p MT))
  :hints (("Goal" :in-theory (enable weak-inv)))
  :rule-classes :forward-chaining)

(defthm ISA-step-chain-p-forward-2
    (implies (weak-inv MT)
	     (ISA-step-chain-p MT))
  :hints (("Goal" :in-theory (enable weak-inv)))
  :rule-classes :forward-chaining)

(defthm correct-modified-flgs-p-forward-2
    (implies (weak-inv MT)
	     (correct-modified-flgs-p MT))
  :hints (("Goal" :in-theory (enable weak-inv)))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Forward-chaining for strong invariants inv
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm pc-match-p-forward
    (implies (inv MT MA)
	     (pc-match-p MT MA))
  :hints (("goal" :in-theory (enable inv)))
  :rule-classes :forward-chaining)

(defthm SRF-match-p-forward
    (implies (inv MT MA)
	     (SRF-match-p MT MA))
  :hints (("goal" :in-theory (enable inv)))
  :rule-classes :forward-chaining)

(defthm RF-match-p-forward
    (implies (inv MT MA)
	     (RF-match-p MT MA))
  :hints (("goal" :in-theory (enable inv)))
  :rule-classes :forward-chaining)
	     
(defthm mem-match-p-forward
    (implies (inv MT MA)
	     (mem-match-p MT MA))
  :hints (("goal" :in-theory (enable inv)))
  :rule-classes :forward-chaining)

(defthm no-specultv-commit-p-forward
    (implies (inv MT MA)
	     (no-specultv-commit-p MT))
  :hints (("goal" :in-theory (enable inv)))
  :rule-classes :forward-chaining)

(defthm correct-speculation-p-forward
    (implies (inv MT MA)
	     (correct-speculation-p MT))
  :hints (("goal" :in-theory (enable inv)))
  :rule-classes :forward-chaining)

(defthm correct-exintr-p-forward
    (implies (inv MT MA)
	     (correct-exintr-p MT))
  :hints (("goal" :in-theory (enable inv)))
  :rule-classes :forward-chaining)

(defthm MT-inst-inv-forward
    (implies (inv MT MA)
	     (MT-INST-inv MT MA))
  :hints (("goal" :in-theory (enable inv)))
  :rule-classes :forward-chaining)

(defthm in-order-dispatch-commit-p-forward
    (implies (inv MT MA)
	     (in-order-dispatch-commit-p MT))
  :hints (("goal" :in-theory (enable inv)))
  :rule-classes :forward-chaining)

(defthm in-order-DQ-p-forward
    (implies (inv MT MA)
	     (in-order-DQ-p MT))
  :hints (("goal" :in-theory (enable inv)))
  :rule-classes :forward-chaining)

(defthm in-order-ROB-p-forward
    (implies (inv MT MA)
	     (in-order-ROB-p MT))
  :hints (("goal" :in-theory (enable inv)))
  :rule-classes :forward-chaining)

(defthm no-stage-conflict-p-forward
    (implies (inv MT MA)
	     (no-stage-conflict MT MA))
  :hints (("goal" :in-theory (enable inv)))
  :rule-classes :forward-chaining)

(defthm no-tag-conflict-p-forward
    (implies (inv MT MA)
	     (no-tag-conflict MT MA))
  :hints (("goal" :in-theory (enable inv)))
  :rule-classes :forward-chaining)

(defthm consistent-MA-p-forward
    (implies (inv MT MA)
	     (consistent-MA-p MA))
  :hints (("goal" :in-theory (enable inv)))
  :rule-classes :forward-chaining)

(defthm consistent-ROB-p-forward
    (implies (consistent-MA-p MA)
	     (consistent-ROB-p (MA-rob MA)))
  :hints (("goal" :in-theory (enable consistent-MA-p)))
  :rule-classes :forward-chaining)

(defthm consistent-ROB-flg-p-forward
    (implies (consistent-ROB-p ROB) 
	     (consistent-ROB-flg-p ROB))
  :hints (("goal" :in-theory (enable consistent-ROB-p)))
  :rule-classes :forward-chaining)

(in-theory (disable consistent-ROB-p-forward
		    consistent-ROB-flg-p-forward))

(defthm misc-inv-forward
    (implies (inv MT MA)
	     (misc-inv MT MA))
  :hints (("goal" :in-theory (enable inv)))
  :rule-classes :forward-chaining)

(deflabel end-invariants-forward-lemmas)

(deftheory invariants-forward-lemmas
    (set-difference-theories (universal-theory 'end-invariants-forward-lemmas)
		     (universal-theory 'begin-invariants-forward-lemmas)))
