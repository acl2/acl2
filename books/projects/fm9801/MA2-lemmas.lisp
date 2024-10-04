;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; MA2-lemmas.lisp:
; Author  Jun Sawada, University of Texas at Austin
;
;  This file proves basic lemmas about the microarchitectural design. 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "utils")
(include-book "MA2-def")

(deflabel begin-MA2-lemmas)

(defthm MA-pc-MA-step
    (equal (MA-pc (MA-step MA sigs)) (step-pc MA sigs))
  :hints (("Goal" :in-theory (enable MA-step))))

(defthm MA-RF-MA-step
    (equal (MA-RF (MA-step MA sigs)) (step-RF MA))
  :hints (("Goal" :in-theory (enable MA-step))))

(defthm MA-SRF-MA-step
    (equal (MA-SRF (MA-step MA sigs)) (step-SRF MA sigs))
  :hints (("Goal" :in-theory (enable MA-step))))

(defthm MA-IFU-MA-step
    (equal (MA-IFU (MA-step MA sigs)) (step-IFU MA sigs))
  :hints (("Goal" :in-theory (enable MA-step))))

(defthm MA-BP-MA-step
    (equal (MA-BP (MA-step MA sigs)) (step-BP MA sigs))
  :hints (("Goal" :in-theory (enable MA-step))))

(defthm MA-DQ-MA-step
    (equal (MA-DQ (MA-step MA sigs)) (step-DQ MA sigs))
  :hints (("Goal" :in-theory (enable MA-step))))

(defthm MA-ROB-MA-step
    (equal (MA-ROB (MA-step MA sigs)) (step-ROB MA sigs))
  :hints (("Goal" :in-theory (enable MA-step))))

(defthm MA-IU-MA-step
    (equal (MA-IU (MA-step MA sigs)) (step-IU MA sigs))
  :hints (("Goal" :in-theory (enable MA-step))))

(defthm MA-MU-MA-step
    (equal (MA-MU (MA-step MA sigs)) (step-MU MA sigs))
  :hints (("Goal" :in-theory (enable MA-step))))

(defthm MA-BU-MA-step
    (equal (MA-BU (MA-step MA sigs)) (step-BU MA sigs))
  :hints (("Goal" :in-theory (enable MA-step))))

(defthm MA-LSU-MA-step
    (equal (MA-LSU (MA-step MA sigs)) (step-LSU MA sigs))
  :hints (("Goal" :in-theory (enable MA-step))))

(defthm DQ-DE0-step-DQ
    (equal (DQ-DE0 (step-DQ MA sigs))
	   (step-DE0 (MA-DQ MA) MA sigs))
  :hints (("goal" :in-theory (enable step-DQ))))

(defthm DQ-DE1-step-DQ
    (equal (DQ-DE1 (step-DQ MA sigs))
	   (step-DE1 (MA-DQ MA) MA sigs))
  :hints (("goal" :in-theory (enable step-DQ))))

(defthm DQ-DE2-step-DQ
    (equal (DQ-DE2 (step-DQ MA sigs))
	   (step-DE2 (MA-DQ MA) MA sigs))
  :hints (("goal" :in-theory (enable step-DQ))))

(defthm DQ-DE3-step-DQ
    (equal (DQ-DE3 (step-DQ MA sigs))
	   (step-DE3 (MA-DQ MA) MA sigs))
  :hints (("goal" :in-theory (enable step-DQ))))

(defthm decode-exunit-exclusive
    (and (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 0 (cntlv-exunit (decode op br)))))
		  (not (b1p (logbit 4 (cntlv-exunit (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 1 (cntlv-exunit (decode op br)))))
		  (not (b1p (logbit 4 (cntlv-exunit (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 2 (cntlv-exunit (decode op br)))))
		  (not (b1p (logbit 4 (cntlv-exunit (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 3 (cntlv-exunit (decode op br)))))
		  (not (b1p (logbit 4 (cntlv-exunit (decode op br))))))

	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 0 (cntlv-exunit (decode op br)))))
		  (not (b1p (logbit 3 (cntlv-exunit (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 1 (cntlv-exunit (decode op br)))))
		  (not (b1p (logbit 3 (cntlv-exunit (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 2 (cntlv-exunit (decode op br)))))
		  (not (b1p (logbit 3 (cntlv-exunit (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 4 (cntlv-exunit (decode op br)))))
		  (not (b1p (logbit 3 (cntlv-exunit (decode op br))))))

	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 0 (cntlv-exunit (decode op br)))))
		  (not (b1p (logbit 2 (cntlv-exunit (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 1 (cntlv-exunit (decode op br)))))
		  (not (b1p (logbit 2 (cntlv-exunit (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 3 (cntlv-exunit (decode op br)))))
		  (not (b1p (logbit 2 (cntlv-exunit (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 4 (cntlv-exunit (decode op br)))))
		  (not (b1p (logbit 2 (cntlv-exunit (decode op br))))))

	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 0 (cntlv-exunit (decode op br)))))
		  (not (b1p (logbit 1 (cntlv-exunit (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 2 (cntlv-exunit (decode op br)))))
		  (not (b1p (logbit 1 (cntlv-exunit (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 3 (cntlv-exunit (decode op br)))))
		  (not (b1p (logbit 1 (cntlv-exunit (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 4 (cntlv-exunit (decode op br)))))
		  (not (b1p (logbit 1 (cntlv-exunit (decode op br))))))

	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 1 (cntlv-exunit (decode op br)))))
		  (not (b1p (logbit 0 (cntlv-exunit (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 2 (cntlv-exunit (decode op br)))))
		  (not (b1p (logbit 0 (cntlv-exunit (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 3 (cntlv-exunit (decode op br)))))
		  (not (b1p (logbit 0 (cntlv-exunit (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 4 (cntlv-exunit (decode op br)))))
		  (not (b1p (logbit 0 (cntlv-exunit (decode op br)))))))

  :hints (("goal" :in-theory (enable decode lift-b-ops
				     logbit* rdb))))

(defthm decode-operand-exclusive
    (and (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 0 (cntlv-operand (decode op br)))))
		  (not (b1p (logbit 3 (cntlv-operand (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 1 (cntlv-operand (decode op br)))))
		  (not (b1p (logbit 3 (cntlv-operand (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 2 (cntlv-operand (decode op br)))))
		  (not (b1p (logbit 3 (cntlv-operand (decode op br))))))

	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 0 (cntlv-operand (decode op br)))))
		  (not (b1p (logbit 2 (cntlv-operand (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 1 (cntlv-operand (decode op br)))))
		  (not (b1p (logbit 2 (cntlv-operand (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 3 (cntlv-operand (decode op br)))))
		  (not (b1p (logbit 2 (cntlv-operand (decode op br))))))

	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 0 (cntlv-operand (decode op br)))))
		  (not (b1p (logbit 1 (cntlv-operand (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 2 (cntlv-operand (decode op br)))))
		  (not (b1p (logbit 1 (cntlv-operand (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 3 (cntlv-operand (decode op br)))))
		  (not (b1p (logbit 1 (cntlv-operand (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 1 (cntlv-operand (decode op br)))))
		  (not (b1p (logbit 0 (cntlv-operand (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 2 (cntlv-operand (decode op br)))))
		  (not (b1p (logbit 0 (cntlv-operand (decode op br))))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (logbit 3 (cntlv-operand (decode op br)))))
		  (not (b1p (logbit 0 (cntlv-operand (decode op br)))))))

  :hints (("goal" :in-theory (enable decode lift-b-ops
				     logbit* rdb))))

(defthm decode-cntlv-exclusive
    (and (implies (and (opcd-p op) (bitp br)
		       (b1p (cntlv-sync? (decode op br))))
		  (not (b1p (cntlv-wb? (decode op br)))))
	 (implies (and (opcd-p op) (bitp br)
		       (b1p (cntlv-sync? (decode op br))))
		  (not (b1p (logbit 3 (cntlv-exunit (decode op br)))))))
  :hints (("goal" :in-theory (enable decode lift-b-ops
				     logbit* rdb))))

(defthm dispatch-inst-if-not-DE0-valid
    (implies (not (b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))
	     (equal (dispatch-inst? MA) 0))
  :hints (("goal" :in-theory (enable dispatch-inst? lift-b-ops
				     equal-b1p-converter dispatch-no-unit?
				     dispatch-to-mu? dispatch-to-bu?
				     dq-ready-no-unit? dispatch-to-iu?
				     dq-ready-to-iu? dq-ready-to-mu?
				     dq-ready-to-bu? dq-ready-to-lsu?
				     dispatch-to-lsu?))))

(defthm issue-LSU-RS0-issue-LSU-RS1-exclusive
    (implies (and (MA-state-p MA) (MA-input-p sigs)
		  (b1p (issue-LSU-RS0? (MA-LSU MA) MA sigs)))
	     (equal (issue-LSU-RS1? (MA-LSU MA) MA sigs) 0))
  :hints (("goal" :in-theory (enable issue-LSU-RS0? issue-LSU-RS1?
				     lift-b-ops equal-b1p-converter
				     LSU-RS0-ISSUE-READY?
				     LSU-RS1-ISSUE-READY?))))

(defthm cases-of-CDB-ready
    (implies (b1p (CDB-ready? MA))
	     (or (b1p (CDB-for-IU? MA))
		 (b1p (CDB-for-BU? MA))
		 (b1p (CDB-for-MU? MA))
		 (b1p (CDB-for-LSU? MA))))
  :hints (("goal" :in-theory (enable CDB-ready? lift-b-ops
				     CDB-for-LSU? CDB-for-IU?
				     CDB-for-BU? CDB-for-MU?)))
  :rule-classes nil)

(defthm cases-of-CDB-ready-for
    (implies (b1p (CDB-ready-for? rix MA))
	     (or (b1p (CDB-for-IU? MA))
		 (b1p (CDB-for-BU? MA))
		 (b1p (CDB-for-MU? MA))
		 (b1p (CDB-for-LSU? MA))))
  :hints (("goal" :in-theory (enable CDB-ready-for? CDB-ready?
				     lift-b-ops
				     CDB-for-LSU? CDB-for-IU?
				     CDB-for-BU? CDB-for-MU?)))
  :rule-classes nil)

(defthm CDB-for-exclusive
    (and (implies (b1p (CDB-for-IU? MA)) (not (b1p (CDB-for-BU? MA))))
	 (implies (b1p (CDB-for-IU? MA)) (not (b1p (CDB-for-MU? MA))))
	 (implies (b1p (CDB-for-IU? MA)) (not (b1p (CDB-for-LSU? MA))))
	 (implies (b1p (CDB-for-BU? MA)) (not (b1p (CDB-for-IU? MA))))
	 (implies (b1p (CDB-for-BU? MA)) (not (b1p (CDB-for-MU? MA))))
	 (implies (b1p (CDB-for-BU? MA)) (not (b1p (CDB-for-LSU? MA))))
	 (implies (b1p (CDB-for-MU? MA)) (not (b1p (CDB-for-IU? MA))))
	 (implies (b1p (CDB-for-MU? MA)) (not (b1p (CDB-for-BU? MA))))
	 (implies (b1p (CDB-for-MU? MA)) (not (b1p (CDB-for-LSU? MA))))
	 (implies (b1p (CDB-for-LSU? MA)) (not (b1p (CDB-for-IU? MA))))
	 (implies (b1p (CDB-for-LSU? MA)) (not (b1p (CDB-for-BU? MA))))
	 (implies (b1p (CDB-for-LSU? MA)) (not (b1p (CDB-for-MU? MA)))))
  :hints (("goal" :in-theory (enable lift-b-ops cdb-def))))

(defthm len-MA-ROB-entries
    (implies (MA-state-p MA)
	     (equal (len (ROB-entries (MA-ROB MA))) *ROB-size*))
  :hints (("goal" :in-theory (enable MA-state-p ROB-p ROB-entries-p))))

(encapsulate nil
(local
 (defun induct-nth-robe (entries idx1 idx2)
     (if (endp entries)	 nil
	 (if (zp idx1) (list entries idx1 idx2)
	     (induct-nth-robe (cdr entries) (1- idx1) (1+ idx2))))))
	     

(local
 (defthm nth-robe-step-robe-help
     (implies (and (integerp idx1) (<= 0 idx1)
		   (integerp idx2) (<= 0 idx2)
		   (< (+ idx1 idx2) 8)
		   (< idx1 (len entries)))
	      (equal (nth idx1 (step-robe-list entries idx2 ROB MA sigs))
		     (step-robe (nth idx1 entries) (+ idx1 idx2) ROB MA sigs)))
   :hints (("goal" :induct (induct-nth-robe entries idx1 idx2)
		   :in-theory (enable STEP-ROBE-LIST unsigned-byte-p
				      rob-index-p))
	   (when-found (STEP-ROBE-LIST ENTRIES IDX2 ROB MA SIGS)
		       (:expand (STEP-ROBE-LIST ENTRIES IDX2 ROB MA SIGS))))))

; A lemma to help opening the definition of step-ROB.
(defthm nth-robe-step-rob
    (implies (and (MA-state-p MA) (rob-index-p index))
	     (equal (nth-robe index (step-ROB MA sigs))
		    (step-robe (nth-robe index (MA-rob MA))
			       index (MA-rob MA) MA sigs)))
  :hints (("goal" :in-theory (enable step-rob nth-robe step-rob-entries))))
)

(defthm not-ex-intr-if-not-exintr-flag-nor-input-exintr
    (implies (and (MA-state-p MA) (MA-input-p sigs)
		  (not (b1p (MA-input-exintr sigs)))
		  (not (b1p (exintr-flag? MA))))
	     (equal (ex-intr? MA sigs) 0))
  :hints (("Goal" :in-theory (enable exintr-flag? ex-intr? lift-b-ops
				     b1p-bit-rewriter))))

(defthm not-ex-intr-if-rob-not-empty
    (implies (not (b1p (rob-empty? (MA-rob MA))))
	     (equal (ex-intr? MA sigs) 0))
  :hints (("Goal" :in-theory (enable ex-intr? lift-b-ops
				     b1p-bit-rewriter))))

(defthm commit-inst-if-leave-excpt
    (implies (and (MA-state-p MA) (b1p (leave-excpt? MA)))
	     (equal (commit-inst? MA) 1))
  :hints (("goal" :in-theory (enable lift-b-ops leave-excpt? commit-inst?
				     equal-b1p-converter
				     b1p-bit-rewriter))))

(defthm commit-inst-if-enter-excpt
    (implies (and (MA-state-p MA) (b1p (enter-excpt? MA)))
	     (equal (commit-inst? MA) 1))
  :hints (("goal" :in-theory (enable lift-b-ops enter-excpt? commit-inst?
				     equal-b1p-converter
				     b1p-bit-rewriter))))

(defthm cntlv-exunit-decode
    (implies (and (syntaxp (quoted-constant-p op)) (bitp br))
	     (equal (cntlv-exunit (decode op br))
		    (cntlv-exunit (decode op 0))))
  :hints (("goal" :in-theory (enable decode logbit* rdb lift-b-ops
				     loghead* logtail*))))

(defthm cntlv-operand-decode
    (implies (and (syntaxp (quoted-constant-p op)) (bitp br))
	     (equal (cntlv-operand (decode op br))
		    (cntlv-operand (decode op 0))))
  :hints (("goal" :in-theory (enable decode logbit* rdb lift-b-ops
				     loghead* logtail*))))

(defthm cntlv-br-predict-decode
    (implies (bitp br)
	     (equal (cntlv-br-predict? (decode op br))
		    br))
  :hints (("goal" :in-theory (enable decode logbit* rdb lift-b-ops
				     loghead* logtail*))))

(defthm cntlv-ld-st-decode
    (implies (syntaxp (quoted-constant-p op))
	     (equal (cntlv-ld-st? (decode op br))
		    (cntlv-ld-st? (decode op 0))))
  :hints (("goal" :in-theory (enable decode logbit* rdb lift-b-ops))))

(defthm cntlv-wb-decode
    (implies (syntaxp (quoted-constant-p op))
	     (equal (cntlv-wb? (decode op br))
		    (cntlv-wb? (decode op 0))))
  :hints (("goal" :in-theory (enable decode logbit* rdb lift-b-ops))))

(defthm cntlv-wb-sreg-decode
    (implies (syntaxp (quoted-constant-p op))
	     (equal (cntlv-wb-sreg? (decode op br))
		    (cntlv-wb-sreg? (decode op 0))))
  :hints (("goal" :in-theory (enable decode logbit* rdb lift-b-ops))))

(defthm cntlv-sync-decode
    (implies (syntaxp (quoted-constant-p op))
	     (equal (cntlv-sync? (decode op br))
		    (cntlv-sync? (decode op 0))))
  :hints (("goal" :in-theory (enable decode logbit* rdb lift-b-ops))))

(defthm cntlv-rfeh-decode
    (implies (syntaxp (quoted-constant-p op))
	     (equal (cntlv-rfeh? (decode op br))
		    (cntlv-rfeh? (decode op 0))))
  :hints (("goal" :in-theory (enable decode logbit* rdb lift-b-ops))))

(defthm cntlv-sync-and-branch-of-decode-exclusive
    (implies (and (opcd-p op) (bitp flg)
		  (b1p (cntlv-sync? (decode op flg))))
	     (equal (logbit 3 (cntlv-exunit (decode op flg))) 0))
  :hints (("goal" :in-theory (enable decode lift-b-ops
				     equal-b1p-converter
				     rdb logbit*
				     opcd-p
				     bv-eqv-iff-equal))))

(defthm exintr-flag-ma-step
    (implies (and (MA-state-p MA) (MA-input-p sigs)
		  (not (b1p (exintr-flag? MA)))
		  (not (b1p (MA-input-exintr sigs))))
	     (not (b1p (exintr-flag? (MA-step MA sigs))))) 
  :hints (("goal" :in-theory (enable exintr-flag? MA-step step-rob
				     lift-b-ops))))
     
; When the ROB is full, no instruction is dispatched.
(defthm not-dispatch-inst-if-rob-full
    (implies (and (MA-state-p MA) (b1p (ROB-full? (MA-rob MA))))
	     (equal (dispatch-inst? MA) 0))
  :hints (("goal" :in-theory (enable lift-b-ops MA-def equal-b1p-converter))))
