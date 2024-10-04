;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; MI-inv.lisp
; Author  Jun Sawada, University of Texas at Austin
;
;  This book proves basic lemmas about the memory access and its
;  protection.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "ACL2")

(include-book "MA2-lemmas")
(include-book "MAETT-lemmas")

(deflabel begin-memory-inv)
; This book proves basic lemmas about the memory.
;  Index
;    Lemmas about memory protection
;    Lemmas about supervisor/user mode
;    Lemmas about side effects of memory operations

(local
(defthm MT-mem-=-MA-mem
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA))
	     (equal (MT-mem MT) (MA-mem MA)))
  :hints (("goal" :in-theory (enable weak-inv inv
				     mem-match-p)))))

(local
(defthm MT-RF-=-MA-RF
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA))
	     (equal (MT-RF MT) (MA-RF MA)))
  :hints (("goal" :in-theory (enable weak-inv inv
				     RF-match-p)))))

(local
(defthm MT-SRF-=-MA-SRF
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA))
	     (equal (MT-SRF MT) (MA-SRF MA)))
  :hints (("goal" :in-theory (enable weak-inv inv
				     SRF-match-p)))))

(local (in-theory (enable ISA-before-MT-non-nil-trace)))

;; Lemmas about memory protection.

; IFU-fetch-prohibited? and read-error? are equivalent.
(defthm IFU-fetch-prohibited-read-error
    (equal (IFU-fetch-prohibited? addr mem su)
	   (read-error? addr mem su))
  :hints (("goal" :in-theory (enable IFU-fetch-prohibited? read-error?))))

; Read protection does not change after ISA-step.
(defthm readable-addr-ISA-step
    (implies (and (ISA-state-p ISA) (ISA-input-p intr) (addr-p addr))
	     (equal (readable-addr? addr (ISA-mem (ISA-step ISA intr)))
		    (readable-addr? addr (ISA-mem ISA))))
  :hints (("Goal" :in-theory (enable ISA-step-functions
				     ISA-step))))

(encapsulate nil
(local
(defthm readable-addr-MT-final-ISA-help
    (implies (and (ISA-chained-trace-p trace pre)
		  (INST-listp trace)
		  (ISA-state-p pre)
		  (addr-p addr))
	     (equal (readable-addr? addr (ISA-mem (trace-final-ISA trace pre)))
		    (readable-addr? addr (ISA-mem pre))))
  :hints (("goal" :in-theory (disable readable-addr-ISA-step))
	  (when-found
	   (EQUAL (READABLE-ADDR? ADDR (ISA-MEM (INST-POST-ISA (CAR TRACE))))
		  (READABLE-ADDR? ADDR (ISA-MEM (INST-PRE-ISA (CAR TRACE)))))
	   (:use (:instance
		  readable-addr-ISA-step (ISA (INST-PRE-ISA (CAR TRACE)))
		  (intr (ISA-input (INST-EXINTR? (CAR TRACE))))))))))

; Readable-addr-MT-final-ISA shows that the final ISA state has the same
; read protection as the initial ISA state.  Using the previous lemma
; readable-addr-ISA-step, this can be proven by induction.
(defthm readable-addr-MT-final-ISA
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (addr-p addr))
	     (equal (readable-addr? addr (ISA-mem (MT-final-ISA MT)))
		    (readable-addr? addr (ISA-mem (MT-init-ISA MT)))))
  :hints (("Goal" :in-theory (enable MT-final-ISA weak-inv
				     inv ISA-step-chain-p))))
)

(encapsulate nil
(local
(defthm readable-addr-trace-mem
    (implies (and (INST-listp trace)
		  (addr-p addr)
		  (ISA-state-p ISA)
		  (ISA-chained-trace-p trace ISA))
	     (equal (readable-addr? addr
				    (trace-mem trace (ISA-mem ISA)))
		    (readable-addr? addr (ISA-mem ISA))))
  :hints (("Goal" :in-theory (disable READABLE-ADDR-ISA-STEP))
	  (when-found (TRACE-MEM (CDR TRACE)
				 (ISA-MEM (INST-POST-ISA (CAR TRACE))))
		      (:expand (TRACE-MEM TRACE (ISA-MEM ISA))))
	  (when-found
	   (EQUAL (READABLE-ADDR? ADDR (ISA-MEM (INST-POST-ISA (CAR TRACE))))
		  (READABLE-ADDR? ADDR (ISA-MEM (INST-PRE-ISA (CAR TRACE)))))
	   (:use (:instance
		  readable-addr-ISA-step (ISA (INST-PRE-ISA (CAR TRACE)))
		  (intr (ISA-input (INST-EXINTR? (CAR TRACE))))))))))
(local
(defthm readable-addr-MA-mem-help
    (implies (and (MAETT-p MT)
		  (inv MT MA)
		  (MA-state-p MA)
		  (addr-p addr)
		  (equal (MT-mem MT) (MA-mem MA)))
	     (equal (readable-addr? addr (MA-mem MA))
		    (readable-addr? addr (ISA-mem (MT-init-ISA MT)))))
  :hints (("Goal" :in-theory (enable MT-mem
				     weak-inv inv
				     ISA-step-chain-p)))
  :rule-classes nil))

; Readable-addr-MA-mem shows that the memory read protection in the
; current MA state is the same as the initial ISA state.
(defthm readable-addr-MA-mem
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (addr-p addr))
	     (equal (readable-addr? addr (MA-mem MA))
		    (readable-addr? addr (ISA-mem (MT-init-ISA MT)))))
  :hints (("Goal" :in-theory (enable weak-inv inv
				     mem-match-p)
		  :use (:instance readable-addr-MA-mem-help))))
) ; encapsulate

(encapsulate nil
(local
(defthm readable-addr-INST-pre-ISA-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (member-equal i trace) (INST-p i)
		  (INST-listp trace)
		  (addr-p addr)
		  (MAETT-p MT) (MA-state-p MA))
     (equal (readable-addr? addr (ISA-mem (INST-pre-ISA i)))
	    (readable-addr? addr (ISA-mem (INST-pre-ISA (car trace))))))
  :hints ((when-found (INST-PRE-ISA (CAR (CDR TRACE)))
		      (:cases ((consp (cdr trace))))))
  :rule-classes nil))

; Memory read protection does not change during ISA executions.
; Thus, all instructions are executed under the same protection.
(defthm readable-addr-INST-pre-ISA
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (addr-p addr))
	     (equal (readable-addr? addr (ISA-mem (INST-pre-ISA i)))
		    (readable-addr? addr (ISA-mem (MT-init-ISA MT)))))
  :hints (("goal" :in-theory (enable INST-in)
		  :use (:instance readable-addr-INST-pre-ISA-help
				  (trace (MT-trace MT))))
	  ("goal'" :cases ((consp (MT-trace MT))))))
)
	      
; Memory write protection does not change after ISA-step.
(defthm writable-addr-ISA-step
    (implies (and (addr-p addr)
		  (ISA-state-p ISA))
	     (equal (writable-addr? addr (ISA-mem (ISA-step ISA intr)))
		    (writable-addr? addr (ISA-mem ISA))))
  :hints (("goal" :in-theory (enable ISA-step ISA-step-functions))))

(encapsulate nil
(local
(defthm writable-addr-INST-pre-ISA-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (member-equal i trace) (INST-p i)
		  (INST-listp trace)
		  (addr-p addr)
		  (MAETT-p MT) (MA-state-p MA))
     (equal (writable-addr? addr (ISA-mem (INST-pre-ISA i)))
	    (writable-addr? addr (ISA-mem (INST-pre-ISA (car trace))))))
  :hints ((when-found (INST-PRE-ISA (CAR (CDR TRACE)))
		      (:cases ((consp (cdr trace))))))))

; Memory write protection does not change during ISA executions.
; Thus, all instructions are executed under the same protection.
(defthm writable-addr-INST-pre-ISA
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (addr-p addr)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (writable-addr? addr (ISA-mem (INST-pre-ISA i)))
		    (writable-addr? addr (ISA-mem (MT-init-ISA MT)))))
  :hints (("goal" :in-theory (enable INST-in)
		  :use (:instance writable-addr-INST-pre-ISA-help
				  (trace (MT-trace MT))))
	  ("goal'" :cases ((consp (MT-trace MT))))))
)

(encapsulate nil
(local
(defthm writable-addr-MA-mem-help-help
    (implies (and (inv MT MA)
		  (consp trace)
		  (INST-listp trace)
		  (addr-p addr)
		  (subtrace-p trace MT)
		  (MAETT-p MT) (MA-state-p MA))
     (equal (writable-addr? addr
			    (trace-mem trace
				       (ISA-mem (INST-pre-ISA (car trace)))))
	    (writable-addr? addr (ISA-mem (INST-pre-ISA (car trace))))))
  :hints ((when-found (INST-PRE-ISA (CAR (CDR TRACE)))
		      (:cases ((consp (cdr trace))))))
  :rule-classes nil))

(local
(defthm writable-addr-MA-mem-help
    (implies (and (inv MT MA)
		  (addr-p addr)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (writable-addr? addr (MT-mem MT))
		    (writable-addr? addr (ISA-mem (MT-init-ISA MT)))))
; Matt K. mod: Apparently heuristics have somehow changed.  The proof goes
; through by replacing the original hints with corresponding proof-builder
; commands.
#|
  :hints (("goal" :in-theory (e/d (MT-mem)
				  (MT-mem-=-MA-mem))
		  :use (:instance writable-addr-MA-mem-help-help
				  (trace (MT-trace MT)))))
|#
  :instructions ((:in-theory (e/d (mt-mem) (mt-mem-=-ma-mem)))
                 (:use (:instance writable-addr-ma-mem-help-help
                                  (trace (mt-trace mt))))
                 :prove) ; or :bash
  :rule-classes nil))

; writable-addr-MA-mem shows that the memory write protection in the
; current MA state is the same as in the initial ISA state.
(defthm writable-addr-MA-mem
    (implies (and (inv MT MA)
		  (addr-p addr)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (writable-addr? addr (MA-mem MA))
		    (writable-addr? addr (ISA-mem (MT-init-ISA MT)))))
  :hints (("goal" :in-theory (enable MT-mem-=-MA-mem)
		  :use (:instance writable-addr-MA-mem-help))))
)

;;  Lemmas about supervisor/user mode. 
(encapsulate nil
(local
(defthm MT-SRF-=-ISA-before-MT-non-commit-trace-help
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (INST-listp trace)
		  (subtrace-p trace MT)
		  (tail-p (MT-non-commit-trace MT) trace))
	     (equal (trace-SRF trace (ISA-SRF pre))
		    (ISA-SRF (ISA-at-tail (MT-non-commit-trace MT)
					  trace pre))))))

;; The ISA state at the commit boundary and the current
;; MA state have the same special register file
(defthm MT-SRF-=-ISA-before-MT-non-commit-trace
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA))
	     (equal (ISA-SRF (ISA-before (MT-non-commit-trace MT) MT))
		    (MT-SRF MT)))
  :hints (("Goal" :in-theory (e/d (ISA-before MT-SRF)
				  (MT-SRF-=-MA-SRF)))))

)

;; Unless an exception or an context synchronization takes place,
;; supervisor/user mode does not change.
(defthm sreg-su-INST-pre-ISA-of-non-exintr-context-sync
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (INST-p i)
		  (not (b1p (INST-EXCPT? i)))
		  (not (b1p (INST-context-sync? i)))
		  (not (b1p (ISA-input-exint intr))))
	     (equal (SRF-su (ISA-SRF (ISA-step (INST-pre-ISA i) intr)))
		    (SRF-su (ISA-SRF (INST-pre-ISA i)))))
  :hints (("Goal" :in-theory (enable ISA-step-functions ISA-step
				     lift-b-ops
				     INST-function-def
				     decode-illegal-inst?
				     decode logbit* rdb
				     supervisor-mode?
				     MT-def-non-rec-functions
				     equal-b1p-converter
				     write-sreg
				     ))))

(encapsulate nil
(local
(defthm local-help-lemma2
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (INST-p i)
		  (not (commit-stg-p (INST-stg i)))
		  (not (retire-stg-p (INST-stg i)))
		  (not (b1p (INST-start-specultv? i)))
		  (not (b1p (ISA-input-exint intr))))
	     (equal (SRF-su (ISA-SRF
			     (ISA-step (INST-pre-ISA i) intr)))
		    (SRF-su (ISA-SRF (INST-pre-ISA i)))))
  :hints (("goal" :in-theory (enable INST-start-specultv? lift-b-ops)))))

(local
(defthm local-help-lemma1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-listp trace)
		  (consp trace)
		  (subtrace-p trace MT)
		  (no-commit-INST-p trace)
		  (not (b1p (trace-specultv? trace))))
     (equal (SRF-su (ISA-SRF (trace-final-ISA trace
					      (INST-pre-ISA (car trace)))))
	    (SRF-su (ISA-SRF (INST-pre-ISA (car trace))))))
  :hints (("Goal" :in-theory (enable lift-b-ops
				     dispatched-p committed-p
				     not-inst-specultv-INST-in-if-committed
				     INST-exintr-INST-in-if-not-retired))
	  (when-found (INST-PRE-ISA (car (cdr TRACE)))
		      (:cases ((consp (cdr trace))))))
  :rule-classes nil))

; The supervisor/user mode is the same at the final ISA state and the
; pre-ISA state of the first uncommitted instruction.
(defthm SRF-su-INST-pre-ISA-MT-non-commit-trace
    (implies (and (inv MT MA)
		  (consp (MT-non-commit-trace MT))
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (not (b1p (MT-specultv? MT))))
     (equal (SRF-su (ISA-SRF (INST-pre-ISA (car (MT-non-commit-trace MT)))))
	    (SRF-su (ISA-SRF (MT-final-ISA MT)))))
  :hints (("Goal"
	   :use ((:instance local-help-lemma1
			    (trace (MT-non-commit-trace MT)))
		 (:instance trace-final-ISA-subtrace
			    (trace (MT-non-commit-trace MT))
			    (pre (INST-pre-ISA
				  (car (MT-non-commit-trace MT)))))))))
) ;encapsulate

;; Supervisor/user mode in the pre-ISA state of the first uncommitted
;; instruction, and the final ISA state of MT are the same, provided
;; that no instructions currently being executed cause internal
;; exceptions.  MT-specultv? checks if currently executed instructions
;; cause exceptions or misprediction of branches.
(defthm SRF-su-MT-final-ISA-=-MT-non-commit-trace
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (MT-specultv? MT))))
     (equal (SRF-su (ISA-SRF (MT-final-ISA MT)))
	    (SRF-su (ISA-SRF (ISA-before (MT-non-commit-trace MT) MT)))))
  :hints (("Goal" :cases ((consp (MT-non-commit-trace MT))))))

(encapsulate nil
(local
(defthm SRF-su-MT-final-ISA-help
    (implies (and (MA-state-p MA)
		  (inv MT MA)
		  (MAETT-p MT)
		  (not (b1p (MT-specultv? MT))))
	     (equal (SRF-su (ISA-SRF (MT-final-ISA MT)))
		    (SRF-su (MT-SRF MT)))))
)

;; Given that no instructions currently being executed cause
;; exceptions, the supervisor/user mode in the current MA and the
;; final ISA state of MT are the same.
(defthm SRF-su-ISA-SRF-MT-final-ISA
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (not (b1p (MT-specultv? MT))))
	     (equal (SRF-su (ISA-SRF (MT-final-ISA MT)))
		    (SRF-su (MA-SRF MA))))
  :hints (("goal" :in-theory (enable weak-inv inv
				     SRF-match-p))))
)

;; Lemmas about side effects of memory operations.

;; Provided that the processor is not executing instructions
;; speculatively and has not detected any exceptions, an
;; instruction fetch error that occurs in the final ISA state of MT also
;; occurs in the current MA state, when it tries to fetch the next
;; instruction. 
(defthm read-error-MT-final-ISA
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (addr-p addr)
		  (not (b1p (MT-specultv? MT))))
	     (equal (read-error? addr
				 (ISA-mem (MT-final-ISA MT))
				 (SRF-su (MA-SRF MA)))
		    (read-error? addr (MA-mem MA) (SRF-su (MA-SRF MA)))))
  :hints (("goal" :in-theory (enable read-error?))))

;; Only an store instruction, without an exception and an external
;; interrupt, changes the memory.  Otherwise, the memory value remains
;; the same.  
(defthm read-mem-ISA-step-if-not-ISA-store-inst-p
    (implies (and (ISA-state-p ISA)
		  (addr-p addr)
		  (not (and (ISA-store-inst-p ISA)
			    (equal (ISA-store-addr ISA) addr)
			    (not (ISA-excpt-p ISA))
			    (not (b1p (ISA-input-exint intr))))))
	     (equal (read-mem addr (ISA-mem (ISA-step ISA intr)))
		    (read-mem addr (ISA-mem ISA))))
  :hints (("goal" :in-theory (enable ISA-store-addr ISA-store-inst-p
				     ISA-functions
				     store-inst-p
				     ISA-step
				     ISA-step-functions))))

(encapsulate nil
(local
(defthm read-mem-MA-mem-if-MT-no-write-at-induction
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (consp trace)
		  (INST-listp trace)
		  (addr-p addr)
		  (trace-no-write-at addr trace))
	     (equal (read-mem addr
			      (trace-mem trace
					 (ISA-mem (INST-pre-ISA (car trace)))))
		    (read-mem addr (ISA-mem (INST-pre-ISA (car trace))))))
  :hints ((when-found (ISA-MEM (INST-PRE-ISA (car (CDR TRACE))))
		      (:cases ((consp (cdr trace))))))
  :rule-classes nil))

(local
(defthm read-mem-MA-mem-if-MT-no-write-at-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (addr-p addr)
		  (MT-no-write-at addr MT))
	     (equal (read-mem addr (MT-mem MT))
		    (read-mem addr (ISA-mem (MT-init-ISA MT)))))
  :hints (("Goal" :in-theory (e/d (MT-mem MT-no-write-at)
				  (MT-MEM-=-MA-MEM))
		  :use (:instance read-mem-MA-mem-if-MT-no-write-at-induction
				  (trace (MT-trace MT))))
	  ("Goal'" :cases ((consp (MT-trace MT)))))
  :rule-classes nil)
)

;; Provided that no instructions in MT modifies the memory value at address
;; addr,  the memory value remains the same from the initial state.
;; This lemma is useful in proving that the instruction fetched by the MA
;; is the same as in the ISA, provided that no self-modification of the
;; program occurs. 
(defthm read-mem-MA-mem-if-MT-no-write-at
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (addr-p addr)
		  (MT-no-write-at addr MT))
	     (equal (read-mem addr (MA-mem MA))
		    (read-mem addr (ISA-mem (MT-init-ISA MT)))))
  :hints (("goal" :use (:instance read-mem-MA-mem-if-MT-no-write-at-help))))
) ;encapsulate

(encapsulate nil
(local
(defthm read-mem-MT-final-ISA-if-MT-no-write-at-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (consp trace)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (addr-p addr)
		  (MAETT-p MT) (MA-state-p MA)
		  (trace-no-write-at addr trace))
	     (equal (read-mem addr
			      (ISA-mem (trace-final-ISA
					trace
					(INST-pre-ISA (car trace)))))
		    (read-mem addr (ISA-mem (INST-pre-ISA (car trace))))))
  :hints (("Goal" :induct t)
	  (when-found (INST-PRE-ISA (CAR (CDR TRACE)))
		      (:cases ((consp (cdr trace))))))
  :rule-classes nil))

;; Provided that there is no memory write operation on address addr, the
;; memory value at addr at the initial and final ISA states are the same.
(defthm read-mem-MT-final-ISA-if-MT-no-write-at
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (addr-p addr)
		  (MT-no-write-at addr MT))
	     (equal (read-mem addr (ISA-mem (MT-final-ISA MT)))
		    (read-mem addr (ISA-mem (MT-init-ISA MT)))))
; Matt K. mod: Apparently heuristics have somehow changed.  The proof goes
; through by replacing the original hints with corresponding proof-builder
; commands.
#|
  :hints (("Goal" :in-theory (enable MT-final-ISA 
				     MT-no-write-at)
		  :use (:instance read-mem-MT-final-ISA-if-MT-no-write-at-help
				  (trace (MT-trace MT))))))
|#
  :instructions ((:in-theory (enable MT-final-ISA 
				     MT-no-write-at))
                 (:use (:instance read-mem-MT-final-ISA-if-MT-no-write-at-help
				  (trace (MT-trace MT))))
                 :prove) ; or :bash
  )
)
