;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; misc-inv.lisp
; Author  Jun Sawada, University of Texas at Austin
;
;  This book proves miscellaneous invariant properties such as
;  consistent-MA-p, in-order-dispatch-commit-p, correct-speculation-p,
;  no-specultv-commit-p, correct-exintr-p, and misc-inv.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "ACL2")

(include-book "MA2-lemmas")
(include-book "MAETT-lemmas")

(deflabel begin-misc-inv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Consistent-MA-p
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Proof of consistent-MA-p for initial states
(defthm consistent-robe-p-if-MA-flushed-help
    (implies (and (ROB-p ROB) (b1p (ROBE-empty-under? idx2 ROB))
		  (integerp idx2) (rob-index-p idx) (< idx idx2))
	     (equal (robe-valid? (nth-robe idx ROB)) 0))
  :hints (("goal" :induct (natural-induction idx2)
		  :in-theory (enable ROBE-EMPTY-UNDER? lift-b-ops
				     ROBE-EMPTY? equal-b1p-converter))))

(defthm consistent-robe-p-if-MA-flushed
    (implies (and (ROB-p ROB) (b1p (ROB-entries-empty? ROB))
		  (b1p (ROB-empty? ROB))
		  (rob-index-p idx))
	     (consistent-robe-p (nth-robe idx ROB) idx ROB))
  :hints (("goal" :in-theory (enable consistent-robe-p ROB-entries-empty?
				     rob-empty? lift-b-ops)))
  :rule-classes
  ((:rewrite :corollary
	     (implies (and (ROB-p ROB) (b1p (ROB-entries-empty? ROB))
			   (b1p (ROB-empty? ROB))
			   (rob-index-p idx))
		      (consistent-robe-p (nth idx (ROB-entries ROB))
					 idx ROB))
	     :hints (("goal" :in-theory (enable nth-robe))))))

(defthm consistent-rob-entries-p-if-MA-flushed-help
    (implies (and (ROB-p ROB) (b1p (ROB-empty? ROB))
		  (b1p (ROB-entries-empty? ROB))
		  (integerp idx) (<= 0 idx) (<= idx *rob-size*))
	     (consistent-rob-entries-p (nthcdr (- *rob-size* idx)
					       (ROB-entries ROB))
				       (rob-index (- *rob-size* idx)) ROB))
  :hints (("goal" :induct (natural-induction idx)
		  :in-theory (enable rob-index-p)))
  :rule-classes nil)

(defthm consistent-rob-entries-p-if-MA-flushed
    (implies (and (ROB-p ROB) (b1p (ROB-empty? ROB))
		  (b1p (ROB-entries-empty? ROB)))
	     (consistent-rob-entries-p (ROB-entries ROB) 0 ROB))
  :hints (("goal" :use (:instance consistent-rob-entries-p-if-MA-flushed-help
				  (idx *rob-size*)))))

(defthm consistent-DQ-cntlv-p-if-MA-flushed
    (implies (and (MA-state-p MA) (b1p (MA-flushed? MA)))
	     (consistent-DQ-cntlv-p (MA-DQ MA)))
  :hints (("goal" :in-theory (enable consistent-DQ-cntlv-p lift-b-ops
				     MA-flushed? DQ-empty?))))

(defthm consistent-ROB-p-if-MA-flushed
    (implies (and (MA-state-p MA) (b1p (MA-flushed? MA)))
	     (consistent-ROB-p (MA-ROB MA)))
  :hints (("goal" :in-theory (enable consistent-ROB-p MA-FLUSHED?
				     ROB-empty? lift-b-ops
				     consistent-ROB-flg-p))))

(defthm consistent-LSU-p-if-MA-flushed
    (implies (and (MA-state-p MA) (b1p (MA-flushed? MA)))
	     (consistent-LSU-p (MA-LSU MA)))
  :hints (("goal" :in-theory (enable consistent-LSU-p
				     MA-flushed? lift-b-ops
				     LSU-empty?))))

(defthm consistent-MA-p-if-MA-flushed
    (implies (and (MA-state-p MA) (b1p (MA-flushed? MA)))
	     (consistent-MA-p MA))
  :Hints (("goal" :in-theory (enable consistent-MA-p ))))

;;; Invariant proof
(defthm consistent-cntlv-p-decode
    (implies (and (IFU-p IFU) (MA-state-p MA))
	     (consistent-cntlv-p (DE-cntlv (decode-output IFU MA sigs))))
  :hints (("Goal" :in-theory (enable consistent-cntlv-p lift-b-ops
				     decode-output))))
(defthm consistent-DQ-cntlv-p-preserved-0
    (implies (and (MA-state-p MA)
		  (consistent-DQ-cntlv-p (MA-DQ MA))
		  (b1p (DE-valid? (step-DE0 (MA-DQ MA) MA sigs))))
	     (consistent-cntlv-p (DE-cntlv (step-DE0 (MA-DQ MA) MA sigs))))
  :hints (("Goal" :in-theory (enable step-DE0 
				     consistent-DQ-cntlv-p
				     DE1-out DE2-out DE3-out
				     lift-b-ops))))

(defthm consistent-DQ-cntlv-p-preserved-1
    (implies (and (MA-state-p MA)
		  (consistent-DQ-cntlv-p (MA-DQ MA))
		  (b1p (DE-valid? (step-DE1 (MA-DQ MA) MA sigs))))
	     (consistent-cntlv-p (DE-cntlv (step-DE1 (MA-DQ MA) MA sigs))))
  :hints (("Goal" :in-theory (enable step-DE1 
				     consistent-DQ-cntlv-p
				     DE1-out DE2-out DE3-out
				     lift-b-ops))))

(defthm consistent-DQ-cntlv-p-preserved-2
    (implies (and (MA-state-p MA)
		  (consistent-DQ-cntlv-p (MA-DQ MA))
		  (b1p (DE-valid? (step-DE2 (MA-DQ MA) MA sigs))))
	     (consistent-cntlv-p (DE-cntlv (step-DE2 (MA-DQ MA) MA sigs))))
  :hints (("Goal" :in-theory (enable step-DE2 
				     consistent-DQ-cntlv-p
				     DE1-out DE2-out DE3-out
				     lift-b-ops))))

(defthm consistent-DQ-cntlv-p-preserved-3
    (implies (and (MA-state-p MA)
		  (consistent-DQ-cntlv-p (MA-DQ MA))
		  (b1p (DE-valid? (step-DE3 (MA-DQ MA) MA sigs))))
	     (consistent-cntlv-p (DE-cntlv (step-DE3 (MA-DQ MA) MA sigs))))
  :hints (("Goal" :in-theory (enable step-DE3 
				     consistent-DQ-cntlv-p
				     lift-b-ops))))

(defthm consistent-DQ-cntlv-p-preserved
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (consistent-DQ-cntlv-p (step-DQ MA sigs)))
  :hints (("goal" :cases ((consistent-DQ-cntlv-p (MA-DQ MA))))
	  ("subgoal 2" :in-theory (enable inv consistent-MA-p)) 
	  ("subgoal 1" :in-theory (enable consistent-DQ-cntlv-p
					  step-DQ))))

;; (rob-index (+ 1 idx)) is either 0 or (+ 1 idx) depending on whether
;; (+ 1 idx) is wrapped-around.
(local
(defthm rob-index-+-1
    (implies (rob-index-p idx)
	     (equal (rob-index (+ 1 idx))
		    (b-if (logbit *ROB-INDEX-SIZE* (+ 1 idx))
			  0 (+ 1 idx))))
  :hints (("goal" :in-theory (enable lift-b-ops rob-index-p rob-index
				     unsigned-byte-p)
		  :cases ((B1P (LOGBIT 3 (+ 1 IDX)))))
	  ("subgoal 1" :use (:instance logbit-0-if-val-lt-expt-2-width
				     (val (+ 1 idx)) (width 3))))))

; local opening rules.
(local
(defthm rob-flg-step-rob
    (equal (rob-flg (step-rob MA sigs))
	   (B-IF
	    (FLUSH-ALL? MA SIGS)
	    0
	    (B-XOR
	     (ROB-FLG (MA-ROB MA))
	     (B-XOR (B-AND (COMMIT-INST? MA)
			   (LOGBIT *ROB-INDEX-SIZE*
				   (+ 1 (ROB-HEAD (MA-ROB MA)))))
		    (B-AND (DISPATCH-INST? MA)
			   (LOGBIT *ROB-INDEX-SIZE*
				   (+ 1 (ROB-TAIL (MA-ROB MA)))))))))
  :hints (("Goal" :in-theory (enable step-rob)))))

(local
(defthm rob-head-step-rob
    (equal (rob-head (step-rob MA sigs))
	   (B-IF (FLUSH-ALL? MA SIGS)
		 0
		 (B-IF (COMMIT-INST? MA)
		       (ROB-INDEX (+ 1 (ROB-HEAD (MA-ROB MA))))
		       (ROB-HEAD (MA-ROB MA)))))
  :hints (("Goal" :in-theory (enable step-rob)))))

(local
(defthm rob-tail-step-rob
    (equal (rob-tail (step-rob MA sigs))
	   (B-IF (FLUSH-ALL? MA SIGS)
		 0
		 (B-IF (DISPATCH-INST? MA)
		       (ROB-INDEX (+ 1 (ROB-TAIL (MA-ROB MA))))
		       (ROB-TAIL (MA-ROB MA)))))
  :hints (("Goal" :in-theory (enable step-rob)))))  

; Linear lemmas to restrict the range of ROB-tail
(defthm rob-tail-range
    (implies (ROB-p ROB)
	     (and (< (rob-tail ROB) 8)
		  (<=  0 (rob-tail ROB))))
  :rule-classes
  ((:linear :corollary
	    (implies (ROB-p ROB) (< (rob-tail ROB) 8)))
   (:linear :corollary 
	    (implies (ROB-p ROB) (<=  0 (rob-tail ROB))))))

; Linear lemmas to restrict the range of ROB-head
(defthm rob-head-range
    (implies (ROB-p ROB)
	     (and (< (rob-head ROB) 8)
		  (<=  0 (rob-head ROB))))
  :rule-classes
  ((:linear :corollary
	    (implies (ROB-p ROB) (< (rob-head ROB) 8)))
   (:linear :corollary 
	    (implies (ROB-p ROB) (<=  0 (rob-head ROB))))))

; If the reorder-buffer is full, no instruction is dispatched.
; Unfortunately, the version with ROB-empty? does not work in the
; proof for consistent-robe-p-preserved.
(defthm not-dispatch-INST-if-rob-is-full
    (implies (and (MA-state-p MA)
		  (b1p (ROB-flg (MA-rob MA)))
		  (equal (ROB-head (MA-ROB MA)) (ROB-tail (MA-ROB MA))))
	     (equal (dispatch-INST? MA) 0))
  :hints (("goal" :in-theory (enable MA-def bv-eqv-iff-equal lift-b-ops
				     equal-b1p-converter))))

; If the reorder-buffer is empty, no instruction is committed.
; Unfortunately, the version with ROB-full? does not work in the
; proof for consistent-robe-p-preserved.
(defthm not-commit-INST-if-rob-is-empty
    (implies (and (MA-state-p MA)
		  (consistent-rob-p (MA-ROB MA))
		  (not (b1p (ROB-flg (MA-rob MA))))
		  (equal (ROB-head (MA-ROB MA)) (ROB-tail (MA-ROB MA))))
	     (equal (commit-INST? MA) 0))
  :hints (("goal" :in-theory (enable MA-def bv-eqv-iff-equal lift-b-ops
				     equal-b1p-converter))))

(encapsulate nil
(local
(defthm cntlv-sync-branch-of-dispatch-cntlv-exclusive-help-help
    (implies (and (consistent-cntlv-p (DE-cntlv (DQ-DE0 (MA-DQ MA))))
		  (b1p (de-valid? (DQ-DE0 (MA-DQ MA))))
		  (b1p (cntlv-sync? (dispatch-cntlv MA))))
	     (equal (logbit 3 (cntlv-exunit (dispatch-cntlv MA))) 0))
  :hints (("goal" :in-theory (enable dispatch-cntlv inv
				     consistent-MA-p consistent-DQ-cntlv-p
				     CONSISTENT-CNTLV-P lift-b-ops
				     equal-b1p-converter)))))

(local
(defthm cntlv-sync-cntlv-wb-of-dispatch-cntlv-exclusive-help-help
    (implies (and (consistent-cntlv-p (DE-cntlv (DQ-DE0 (MA-DQ MA))))
		  (b1p (de-valid? (DQ-DE0 (MA-DQ MA))))
		  (b1p (cntlv-sync? (dispatch-cntlv MA))))
	     (equal (cntlv-wb? (dispatch-cntlv MA)) 0))
    :hints (("goal" :in-theory (enable dispatch-cntlv inv
				     consistent-MA-p consistent-DQ-cntlv-p
				     CONSISTENT-CNTLV-P lift-b-ops
				     equal-b1p-converter)))))

(local
(defthm cntlv-sync-branch-of-dispatch-cntlv-exclusive-help
    (implies (and (inv MT MA)
		  (b1p (de-valid? (DQ-DE0 (MA-DQ MA))))
		  (b1p (cntlv-sync? (dispatch-cntlv MA))))
	     (equal (logbit 3 (cntlv-exunit (dispatch-cntlv MA))) 0))
  :hints (("goal" :in-theory (enable inv
				     consistent-MA-p consistent-DQ-cntlv-p
				     lift-b-ops)))))

(local
(defthm cntlv-sync-cntlv-wb-of-dispatch-cntlv-exclusive-help
    (implies (and (inv MT MA)
		  (b1p (de-valid? (DQ-DE0 (MA-DQ MA))))
		  (b1p (cntlv-sync? (dispatch-cntlv MA))))
	     (equal (cntlv-wb? (dispatch-cntlv MA)) 0))
    :hints (("goal" :in-theory (enable inv
				     consistent-MA-p consistent-DQ-cntlv-p
				     lift-b-ops)))))

(local
 (defthm DQ-de0-valid-if-dispatch-inst
     (implies (and (MA-state-p MA) (b1p (dispatch-inst? MA)))
	      (equal (de-valid? (DQ-DE0 (MA-DQ MA))) 1))
   :hints (("goal" :in-theory (enable MA-def lift-b-ops
				      equal-b1p-converter)))))

(defthm cntlv-sync-branch-of-dispatch-cntlv-exclusive
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA))
		  (b1p (cntlv-sync? (dispatch-cntlv MA))))
	     (equal (logbit 3 (cntlv-exunit (dispatch-cntlv MA))) 0)))

(defthm cntlv-sync-cntlv-wb-of-dispatch-cntlv-exclusive
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (dispatch-inst? MA))
		  (b1p (cntlv-sync? (dispatch-cntlv MA))))
	     (equal (cntlv-wb? (dispatch-cntlv MA)) 0)))
)

(encapsulate nil
(local
(defthm rob-tail-7-if-carries-out
    (implies (and (ROB-p ROB)
		  (b1p (logbit 3 (+ 1 (rob-tail ROB)))))
	     (equal (rob-tail ROB) 7))
  :Hints (("goal" :use (:instance logbit-0-if-val-lt-expt-2-width
				  (val (+ 1 (rob-tail ROB))) (width 3))
		  :in-theory (enable rob-p rob-index-p unsigned-byte-p)))))

(local
(defthm rob-head-7-if-carries-out
    (implies (and (ROB-p ROB) (b1p (logbit 3 (+ 1 (rob-head ROB)))))
	     (equal (rob-head ROB) 7))
  :Hints (("goal" :use (:instance logbit-0-if-val-lt-expt-2-width
				  (val (+ 1 (rob-head ROB))) (width 3))
		  :in-theory (enable rob-p rob-index-p unsigned-byte-p)))))

(local
(defun consistent-robe-p-1 (robe idx ROB)
   (equal (robe-valid? robe)
	  (if (b1p (ROB-flg ROB))
	      (if (or (<= (ROB-head ROB) idx) (< idx (ROB-tail ROB))) 1 0)
	      (if (and (<= (ROB-head ROB) idx) (< idx (ROB-tail ROB))) 1 0)))))

(local
(defun consistent-robe-p-2 (robe)
    (implies (b1p (robe-valid? robe))
	     (and (not (b1p (b-and (robe-branch? robe) (robe-sync? robe))))
		  (not (b1p (b-and (robe-wb? robe) (robe-sync? robe))))))))

(local
(defthm consistent-robe-p*
    (equal (consistent-robe-p robe idx ROB)
	   (and (consistent-robe-p-1 robe idx ROB)
		(consistent-robe-p-2 robe)))
  :hints (("goal" :in-theory (enable consistent-robe-p)))
  :rule-classes :definition))

(local
(in-theory (disable consistent-robe-p-1 consistent-robe-p-2
		    consistent-robe-p*)))

; consistent-robe-p is preserved.
(local
(defthm consistent-robe-p-1-preserved
    (implies (and (rob-index-p idx)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (consistent-ROB-p (MA-ROB MA))
		  (consistent-robe-p robe idx (MA-ROB MA)))
	     (consistent-robe-p-1 (step-robe robe idx (MA-ROB MA) MA sigs)
				  idx  (step-rob MA sigs)))
  :hints (("goal" :in-theory (enable consistent-robe-p-1
				     consistent-robe-p*
				     step-robe
				     consistent-rob-p
				     rob-index-p
				     unsigned-byte-p
				     consistent-rob-flg-p
				     lift-b-ops
				     bv-eqv-iff-equal
				     ROBE-RECEIVE-INST?
				     )))))

(local
(defthm consistent-robe-p-2-preserved
    (implies (and (inv MT MA)
		  (rob-index-p idx)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (consistent-robe-p robe idx (MA-ROB MA)))
	     (consistent-robe-p-2 (step-robe robe idx (MA-ROB MA) MA sigs)))
  :hints (("goal" :in-theory (enable consistent-robe-p-2
				     CONSISTENT-ROBE-P*
				     ROBE-RECEIVE-INST?
				     lift-b-ops
				     consistent-cntlv-p
				     step-robe)))))

(defthm consistent-robe-p-preserved
    (implies (and (inv MT MA)
		  (rob-index-p idx)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (consistent-ROB-p (MA-ROB MA))
		  (consistent-robe-p robe idx (MA-ROB MA)))
	     (consistent-robe-p (step-robe robe idx (MA-ROB MA) MA sigs)
				idx  (step-rob MA sigs)))
  :hints (("goal" :in-theory (enable consistent-robe-p*))))

(defthm consistent-ROB-entries-p-preserved
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (rob-index-p idx)
		  (consistent-ROB-p (MA-ROB MA))
		  (consistent-ROB-entries-p robe-list idx (MA-ROB MA)))
	     (consistent-ROB-entries-p (step-robe-list robe-list idx
						       (MA-rob MA) MA sigs)
				       idx
				       (step-rob MA sigs)))
  :hints (("Goal" :in-theory (enable STEP-ROBE-LIST))))

; consistent-rob-flg-p is preserved.
(defthm consistent-rob-flg-p-preserved
    (implies (and (MA-state-p MA)
		  (consistent-rob-flg-p (MA-ROB MA))
		  (consistent-rob-p (MA-rob MA)))
	     (consistent-ROB-flg-p (step-ROB MA sigs)))
  :hints (("goal" :in-theory (enable consistent-rob-flg-p lift-b-ops
				     consistent-rob-p))))
)

(local
(defthm rob-entries-step-rob
    (equal (rob-entries (step-rob MA sigs))
	   (step-rob-entries (rob-entries (MA-rob MA)) (MA-rob MA) MA sigs))
  :hints (("Goal" :in-theory (enable step-rob)))))

; consistent-ROB-p is preserved.
(defthm consistent-ROB-p-preserved
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA))
	     (consistent-ROB-p (step-rob MA sigs)))
  :hints (("goal" :cases  ((consistent-ROB-p (MA-ROB MA))))
	  ("subgoal 2" :in-theory (enable inv consistent-MA-p))
	  ("subgoal 1" :in-theory (enable consistent-rob-p step-rob-entries))))

;; Proof of consistent-LSU-p-preserved
(defthm wbuf0-valid-step-wbuf0-if-rbuf-wbuf0
    (implies (and (inv MT MA)
		  (b1p (rbuf-valid? (step-rbuf (MA-LSU MA) MA sigs)))
		  (b1p (rbuf-wbuf0? (step-rbuf (MA-LSU MA) MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)) 
	     (equal (wbuf-valid? (step-wbuf0 (MA-LSU MA) MA sigs)) 1))
  :hints (("Goal" :in-theory (enable step-rbuf step-wbuf0
				     wbuf1-output update-wbuf0
				     RELEASE-WBUF0?
				     issued-write
				     lift-b-ops equal-b1p-converter))))

(defthm wbuf1-valid-step-wbuf1-if-rbuf-wbuf1
    (implies (and (inv MT MA)
		  (b1p (rbuf-valid? (step-rbuf (MA-LSU MA) MA sigs)))
		  (b1p (rbuf-wbuf1? (step-rbuf (MA-LSU MA) MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)) 
	     (equal (wbuf-valid? (step-wbuf1 (MA-LSU MA) MA sigs)) 1))
  :hints (("Goal" :in-theory (enable step-rbuf step-wbuf1 lift-b-ops
				     issued-write update-wbuf1
				     RELEASE-WBUF0?
				     equal-b1p-converter))))

(defthm uniq-inst-at-stg-non-commit-wbuf0
     (implies (and (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (not (b1p (wbuf-commit? (LSU-wbuf0 (MA-LSU MA)))))
		   (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
	      (uniq-inst-at-stgs '((LSU wbuf0)
				   (LSU wbuf0 lch)
				   (complete wbuf0))
				 MT))
  :hints (("Goal" :use ((:instance UNIQ-INST-AT-LSU-WBUF0-IF-VALID)
			(:instance uniq-inst-at-stgs-remove-equal
				   (stgs '((LSU wbuf0)
					   (LSU wbuf0 lch)
					   (complete wbuf0)
					   (commit wbuf0)))
				   (stg '(commit wbuf0)))))))

(defthm not-committed-p-inst-at-non-commit-wbuf0
    (implies (and (inv MT MA)
		  (uniq-inst-at-stgs '((LSU wbuf0)
				       (LSU wbuf0 lch)
				       (complete wbuf0))
				     MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (not (committed-p (inst-at-stgs '((LSU wbuf0)
					       (LSU wbuf0 lch)
					       (complete wbuf0))
					     MT))))
  :hints (("Goal" :use ((:instance uniq-inst-at-stgs*
				   (stgs '((LSU wbuf0)
					   (LSU wbuf0 lch)
					   (complete wbuf0))))
			(:instance uniq-inst-at-stgs*
				   (stgs '((LSU wbuf0 lch)
					   (complete wbuf0))))
			(:instance inst-at-stgs*
				   (stgs '((LSU wbuf0)
					   (LSU wbuf0 lch)
					   (complete wbuf0))))
			(:instance inst-at-stgs*
				   (stgs '((LSU wbuf0 lch)
					   (complete wbuf0))))))))

(defthm wbuf0-commit-if-wbuf1-commit
    (implies (and (inv MT MA)
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (b1p (wbuf-commit? (LSU-wbuf1 (MA-LSU MA))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (wbuf-commit? (LSU-wbuf0 (MA-LSU MA))) 1))
  :hints (("Goal" :use (:instance INST-in-order-p-wbuf0-wbuf1
				  (i (INST-at-stgs '((LSU wbuf0)
						     (LSU wbuf0 lch)
						     (complete wbuf0)) MT))
				  (j (INST-at-stg '(commit wbuf1) MT)))
		  :in-theory (enable lift-b-ops equal-b1p-converter))))

(defthm wbuf0-valid-step-wbuf0
    (implies (and (inv MT MA)
		  (b1p (wbuf-valid? (step-wbuf1 (MA-LSU MA) MA sigs)))
		  (MAETT-p MT) (MA-state-p MA))
	     (b1p (wbuf-valid? (step-wbuf0 (MA-LSU MA) MA sigs))))
  :Hints (("Goal" :in-theory (enable step-wbuf1 step-wbuf0 lift-b-ops
				     wbuf1-output update-wbuf1
				     ISSUED-WRITE
				     update-wbuf0))))

(defthm consistent-LSU-p-preserved
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-LSU-p (step-LSU MA sigs)))
  :hints (("Goal" :in-theory (enable consistent-LSU-p step-LSU lift-b-ops))))

; consistent-MA-p is preserved.
(defthm consistent-MA-p-preserved
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (consistent-MA-p (MA-step MA sigs)))
  :hints (("goal" :in-theory (enable consistent-MA-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Proof about in-order-dispatch-commit-p
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Proof of in-order-dispatch-commit-p for initial states
(defthm in-order-dispatch-commit-p-init-MT
    (in-order-dispatch-commit-p (init-MT MA))
  :hints (("goal" :in-theory (enable init-MT in-order-dispatch-commit-p))))

;;;;; Invariant proof
(defthm step-trace-cdr-if-step-INST-car-is-IFU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (not (b1p (INST-exintr-now? (car trace) MA sigs)))
		  (IFU-stg-p (INST-stg (step-INST (car trace) MT MA sigs))))
	     (equal (step-trace (cdr trace) MT MA sigs ISA spc smc)
		    nil))
  :hints (("goal" :use (:instance INST-is-at-one-of-the-stages
				  (i (car trace)))
		  :in-theory (disable INST-is-at-one-of-the-stages)
		  :do-not-induct t)
	  ("subgoal 2" :cases ((consp (cdr trace))))))

(encapsulate nil
(local
(defthm INST-in-order-car-car-tail-p-help
    (implies (and (consp sub)
		  (tail-p trace sup)
		  (tail-p sub trace)
		  (not (equal sub trace)))
	     (member-in-order (car trace) (car sub) sup))
  :hints (("goal" :In-theory (enable member-in-order* tail-p)))))

(defthm INST-in-order-car-car-tail-p
    (implies (and (consp sub)
		  (subtrace-p trace MT)
		  (tail-p sub trace)
		  (not (equal sub trace)))
	     (INST-in-order-p (car trace) (car sub) MT))
  :hints (("goal" :In-theory (enable INST-in-order-p subtrace-p))))
)

	   

(encapsulate nil
(local
(defthm not-member-in-order-if-i-is-IFU
    (implies (and (in-order-trace-p trace)
		  (IFU-stg-p (INST-stg i)))
	     (not (member-in-order I J trace)))
  :hints (("goal" :in-theory (enable member-in-order*)))))

(defthm not-INST-in-order-if-i-is-IFU
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (IFU-stg-p (INST-stg i)))
	     (not (INST-in-order-p I J MT)))
  :Hints (("goal" :in-theory (enable INST-in-order-p inv
				     in-order-dispatch-commit-p))))
)

(defthm DQ-stg-idx-non-negative
    (implies (and (INST-p i) (DQ-stg-p (INST-stg i)))
	     (<= 0 (DQ-stg-idx (INST-stg i))))
  :hints (("goal" :in-theory (enable INST-p stage-p DQ-stg-p)))
  :rule-classes :linear)

(defthm DQ-stg-p-decremented
    (implies (and (INST-p i)
		  (DQ-stg-p (INST-stg i))
		  (< 0 (DQ-stg-IDX (INST-stg i))))
	     (DQ-stg-p (list 'DQ (+ -1 (DQ-stg-IDX (INST-stg i))))))
  :Hints (("goal" :in-theory (enable DQ-stg-p INST-p stage-p))))

(encapsulate nil
(local
 (defthm DQ-stg-idx-monotone-help-help
     (implies (and (consp trace)
		   (INST-listp trace)
		   (INST-p j)
		   (DQ-stg-p (INST-stg (car trace)))
		   (DQ-stg-p (INST-stg j))
		   (in-order-trace-p trace)
		   (member-equal j (cdr trace))
		   (in-order-DQ-trace-p (cdr trace)
				(+ 1 (DQ-stg-idx (INST-stg (car trace))))))
	      (< (DQ-stg-idx (INST-stg (car trace)))
		 (DQ-stg-idx (INST-stg j))))
   :hints (("goal" :in-theory (enable dispatched-p)))))

(local
(defthm DQ-stg-idx-monotone-help
    (implies (and (in-order-trace-p trace)
		  (in-order-DQ-trace-p trace idx)
		  (INST-p i)
		  (INST-listp trace)
		  (member-in-order i j trace)
		  (DQ-stg-p (INST-stg i))
		  (DQ-stg-p (INST-stg j)))
	     (< (DQ-stg-idx (INST-stg i)) (DQ-stg-idx (INST-stg j))))
  :Hints (("Goal" :in-theory (enable member-in-order*)))))
  
(defthm DQ-stg-idx-monotone
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in-order-p i j MT)
		  (INST-p i) (INST-p j)
		  (DQ-stg-p (INST-stg i))
		  (DQ-stg-p (INST-stg j)))
	     (< (DQ-stg-idx (INST-stg i)) (DQ-stg-idx (INST-stg j))))
  :hints (("goal" :in-theory (enable inv in-order-DQ-p
				     in-order-dispatch-commit-p
				     INST-in-order-p)))
  :rule-classes nil)
)

(encapsulate nil
(local
 (defthm not-conflict-inst-exintr-now 
     (implies (and (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (INST-p j)
		   (B1P (INST-EXINTR-NOW? i MA SIGS))
		   (not (b1p (INST-exintr-now? j MA sigs))))
	      (not (DQ-stg-p (INST-stg (step-inst j MT MA sigs)))))
   :hints (("goal" :cases ((b1p (ex-intr? MA sigs))))
	   ("subgoal 1" :use (:instance INST-is-at-one-of-the-stages (i j))
			:in-theory (disable INST-is-at-one-of-the-stages)))))

(local
 (defthm ex-intr-inst-exintr-now-DQ-stg-conflict
     (implies (and (INST-p i)
		   (b1p (ex-intr? MA sigs))
		   (not (b1p (INST-exintr-now? i MA sigs))))
	      (not (DQ-stg-p (INST-stg (step-INST i MT MA sigs)))))
   :hints (("goal"  :use (:instance INST-is-at-one-of-the-stages)
		    :in-theory (disable INST-is-at-one-of-the-stages)))))
 
		  

(defthm DQ-stg-p-second-if-first-inst-is-DQ
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-p j)
		  (INST-in-order-p i j MT)
		  (DQ-stg-p (INST-stg i))
		  (DQ-stg-p (INST-stg j)))
	     (DQ-stg-p (INST-stg (step-INST j MT MA sigs))))
  :hints (("goal" :use (:instance DQ-stg-idx-monotone)
		  :in-theory (enable step-INST-opener step-INST-dq))))
	     
(local
(defthm IFU-or-DQ-stg-step-INST-if-INST-in-order
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (DQ-stg-p (INST-stg (step-INST i MT MA sigs)))
		  (INST-p i) (INST-p j)
		  (INST-in i MT) (INST-in j MT)
		  (INST-in-order-p i j MT)
		  (not  (IFU-stg-p (INST-stg (step-INST j MT MA sigs)))))
	     (DQ-stg-p (INST-stg (step-INST j MT MA sigs))))
  :hints (("goal" :use ((:instance INST-is-at-one-of-the-stages)
			(:instance INST-is-at-one-of-the-stages (i j)))
		  :in-theory (disable INST-is-at-one-of-the-stages)))))

(local
(defthm no-dispatch-inst-step-trace-cdr-if-step-INST-car-is-DQ-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (subtrace-p trace MT)
		  (not (equal sub trace))
		  (tail-p sub trace)
		  (INST-listp sub)
		  (INST-listp trace)
		  (not (b1p (inst-exintr-now? (car trace) MA sigs)))
		  (DQ-stg-p (INST-stg (step-INST (car trace) MT MA sigs))))
	     (no-dispatched-inst-p
	      (step-trace sub MT MA sigs ISA spc smc)))
  :hints (("goal" :induct (step-trace sub MT MA sigs ISA spc smc)
		  :restrict ((IFU-or-DQ-stg-step-INST-if-INST-in-order
			      ((i (car trace)))))
		  :in-theory (enable dispatched-p*))
	  (when-found (DQ-STG-P (INST-STG (STEP-INST (CAR SUB) MT MA SIGS)))
		      (:cases ((consp trace))))
	  (when-found (IFU-STG-P (INST-STG (STEP-INST (CAR SUB) MT MA SIGS)))
		      (:cases ((consp trace)))))))

; The instructions are not dispatched in this cycle, if a preceding
; instruction is in the DQ stage in the next cycle.
(defthm no-dispatch-inst-step-trace-cdr-if-step-INST-car-is-DQ
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (not (b1p (inst-exintr-now? (car trace) MA sigs)))
		  (DQ-stg-p (INST-stg (step-INST (car trace) MT MA sigs))))
	     (no-dispatched-inst-p
	      (step-trace (cdr trace) MT MA sigs ISA spc smc))))
)

(local
(encapsulate nil
; If instruction i is in the execute stage next cycle, a subsequent
; instruction j is not committed in the next cycle.
(local
(defthm not-commit-if-earlier-inst-in-execute-stg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in-order-p i j MT)
		  (INST-p i) (INST-in i MT)
		  (INST-p j) (INST-in j MT)
		  (execute-stg-p (INST-stg (step-INST i MT MA sigs))))
	     (not (commit-stg-p (INST-stg (step-INST j MT MA sigs)))))
  :hints (("goal" :use ((:instance INST-is-at-one-of-the-stages)
			(:instance INST-is-at-one-of-the-stages (i j)))
		  :in-theory (disable INST-is-at-one-of-the-stages)))))

(local
(defthm not-retire-if-earlier-inst-in-execute-stg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in-order-p i j MT)
		  (INST-p i) (INST-in i MT)
		  (INST-p j) (INST-in j MT)
		  (execute-stg-p (INST-stg (step-INST i MT MA sigs))))
	     (not (retire-stg-p (INST-stg (step-INST j MT MA sigs)))))
  :hints (("goal" :use ((:instance INST-is-at-one-of-the-stages)
			(:instance INST-is-at-one-of-the-stages (i j)))
		  :in-theory (disable INST-is-at-one-of-the-stages)))))

; Local lemmas
; If external exception occurs this cycle, no instruction will be
; in the execute stage in the next cycle.
(local
(defthm  not-execute-stg-p-step-INST-if-ex-intr
     (implies (and (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (B1P (ex-intr? MA sigs))
		   (INST-p i) (INST-in i MT)
		   (not (B1P (INST-EXINTR-NOW? i MA SIGS))))
	      (not (execute-stg-p (INST-stg (step-INST i MT MA sigs)))))
   :hints (("goal" :use (:instance INST-is-at-one-of-the-stages)
		   :in-theory (disable INST-is-at-one-of-the-stages)))))

(local
(defthm  not-execute-stg-p-step-INST-if-INST-exintr-now?
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (not (B1P (INST-EXINTR-NOW? i MA SIGS)))
		  (B1P (INST-EXINTR-NOW? j MA SIGS)))
	     (not (execute-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :use (:instance INST-is-at-one-of-the-stages)
		  :in-theory (disable INST-is-at-one-of-the-stages))
	  (when-found (DQ-STG-P (INST-STG I))
		      (:cases ((b1p (ex-intr? MA sigs))))))))

(local
(defthm no-complete-inst-step-trace-cdr-if-step-INST-car-execute-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (not (equal sub trace))
		  (tail-p sub trace)
		  (INST-listp sub)
		  (INST-listp trace)
		  (execute-stg-p (INST-stg (step-INST (car trace) MT MA sigs)))
		  (not (b1p (INST-exintr-now? (car trace) MA sigs))))
	     (no-commit-inst-p
	      (step-trace sub MT MA sigs ISA spc smc)))
  :hints (("goal" :induct (step-trace sub MT MA sigs ISA spc smc)
		  :restrict ((not-commit-if-earlier-inst-in-execute-stg
			      ((i (car trace))))
			     (not-retire-if-earlier-inst-in-execute-stg
			      ((i (car trace)))))
		  :expand (INST-listp trace)))))

; A local lemma to help the proof of in-order-trace-p-step-trace.
; If instruction (car trace) is in the execute stage in the next cycle,
; no instruction in (cdr trace) will be committed.  This is
; practically the proof of in-order commit.
(defthm no-complete-inst-step-trace-cdr-if-step-INST-car-execute
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (not (b1p (INST-exintr-now? (car trace) MA sigs)))
		  (execute-stg-p (INST-stg (step-INST (car trace)
						      MT MA sigs))))
	     (no-commit-inst-p
	      (step-trace (cdr trace) MT MA sigs ISA spc smc))))
))

; A local lemma to help the proof of in-order-trace-p-step-trace.
; If instruction (car trace) is in the complete stage in the next cycle,
; no instruction in (cdr trace) will be committed.  This is
; practically the proof of in-order commit.
(encapsulate nil
; If instruction i is in the complete stage next cycle, a subsequent
; instruction j is not committed in the next cycle.
(local
(defthm not-commit-if-earlier-inst-in-complete-stg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in-order-p i j MT)
		  (INST-p i) (INST-in i MT)
		  (INST-p j) (INST-in j MT)
		  (complete-stg-p (INST-stg (step-INST i MT MA sigs))))
	     (not (commit-stg-p (INST-stg (step-INST j MT MA sigs)))))
  :hints (("goal" :use ((:instance INST-is-at-one-of-the-stages)
			(:instance INST-is-at-one-of-the-stages (i j)))
		  :in-theory (disable INST-is-at-one-of-the-stages)))))

(local
(defthm not-retire-if-earlier-inst-in-complete-stg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in-order-p i j MT)
		  (INST-p i) (INST-in i MT)
		  (INST-p j) (INST-in j MT)
		  (complete-stg-p (INST-stg (step-INST i MT MA sigs))))
	     (not (retire-stg-p (INST-stg (step-INST j MT MA sigs)))))
  :hints (("goal" :use ((:instance INST-is-at-one-of-the-stages)
			(:instance INST-is-at-one-of-the-stages (i j)))
		  :in-theory (disable INST-is-at-one-of-the-stages)))))

(local
(defthm  not-complete-stg-p-step-INST-if-ex-intr
     (implies (and (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (B1P (ex-intr? MA sigs))
		   (INST-p i) (INST-in i MT)
		   (not (B1P (INST-EXINTR-NOW? i MA SIGS))))
	      (not (complete-stg-p (INST-stg (step-INST i MT MA sigs)))))
   :hints (("goal" :use (:instance INST-is-at-one-of-the-stages)
		   :in-theory (disable INST-is-at-one-of-the-stages)))))

(local
(defthm  not-complete-stg-p-step-INST-if-INST-exintr-now?
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (not (B1P (INST-EXINTR-NOW? i MA SIGS)))
		  (B1P (INST-EXINTR-NOW? j MA SIGS)))
	     (not (complete-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :use (:instance INST-is-at-one-of-the-stages)
		  :in-theory (disable INST-is-at-one-of-the-stages))
	  (when-found (DQ-STG-P (INST-STG I))
		      (:cases ((b1p (ex-intr? MA sigs))))))))

(local
(defthm no-complete-inst-step-trace-cdr-if-step-INST-car-complete-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (not (equal sub trace))
		  (tail-p sub trace)
		  (INST-listp sub) (INST-listp trace)
		  (complete-stg-p
		   (INST-stg (step-INST (car trace) MT MA sigs)))
		  (not (b1p (INST-exintr-now? (car trace) MA sigs))))
	     (no-commit-inst-p
	      (step-trace sub MT MA sigs ISA spc smc)))
  :hints (("goal" :induct (step-trace sub MT MA sigs ISA spc smc)
		  :restrict ((NOT-COMMIT-IF-EARLIER-INST-IN-COMPLETE-STG
			      ((i (car trace))))
			     (NOT-RETIRE-IF-EARLIER-INST-IN-COMPLETE-STG
			      ((i (car trace)))))
		  :expand (INST-listp trace)))))

(defthm no-complete-inst-step-trace-cdr-if-step-INST-car-complete
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (complete-stg-p
		   (INST-stg (step-INST (car trace) MT MA sigs)))
		  (not (b1p (INST-exintr-now? (car trace) MA sigs))))
	     (no-commit-inst-p
	      (step-trace (cdr trace) MT MA sigs ISA spc smc))))
)

(defthm in-order-trace-p-step-trace
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT) (MA-input-p sigs)
		  (INST-listp trace)
		  (subtrace-p trace MT))
	     (in-order-trace-p (step-trace trace MT MA sigs ISA smc spc)))
  :hints (("goal" :in-theory (enable dispatched-p* committed-p*))))

(defthm in-order-dispatch-commit-p-preserved
    (implies (and (inv MT MA) (MA-state-p MA) (MAETT-p MT) (MA-input-p sigs))
	     (in-order-dispatch-commit-p (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable MT-step in-order-dispatch-commit-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof of correct-speculation-p-preserved
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; correct-speculation-p is true for init-MAETT.
(defthm correct-speculation-p-init-MAETT
    (implies (MA-state-p MA)
	     (correct-speculation-p (init-MT MA)))
  :hints (("Goal" :in-theory (enable init-MT correct-speculation-p))))

(defthm inst-wrong-branch-step-INST-if-not-retire-after-step
     (implies (and (INST-p i) (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		   (complete-stg-p (INST-stg i))
		   (not (retire-stg-p (INST-stg (step-INST i MT MA sigs)))))
	      (equal (inst-wrong-branch? (step-INST i MT MA sigs))
		     (inst-wrong-branch? i)))
  :hints (("goal" :in-theory (enable inst-wrong-branch? lift-b-ops))))

; The machine may speculatively execute instructions following a
; certain type of instructions.  These instructions initiating
; speculative execution can be characterized with
; INST-start-specultv?. (INST-start-specultv? i) does not change its
; value unless i retires or advances from IFU stage.
(defthm inst-start-specultv-step-complete-INST
     (implies (and (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (MA-input-p sigs)
		   (INST-p i)
		   (INST-in i MT)
		   (complete-stg-p (INST-stg i))
		   (not (b1p (INST-specultv? i)))
		   (not (b1p (INST-modified? i)))
		   (not (b1p (INST-cause-jmp? i MT MA sigs))))
	      (equal (inst-start-specultv? (step-INST i MT MA sigs))
		     (inst-start-specultv? i)))
  :hints (("goal" :in-theory (e/d (INST-start-specultv? lift-b-ops
				     equal-b1p-converter)
				  (inst-is-at-one-of-the-stages))
		  :use (:instance INST-is-at-one-of-the-stages))
	  (when-found (INST-WRONG-BRANCH? (STEP-INST I MT MA SIGS))
	      (:cases
	       ((complete-stg-p (INST-stg (step-INST i MT MA sigs))))))))

; If instruction i is a correctly predicted branch instruction in the IFU,
; and if fetch-inst? is asserted, i is still correctly predicted
; branch in DQ.  In the IFU stage, we all assume that a branch is not
; taken, and when it is decoded, a branch prediction mechanism
; predicts branch outcome.  If branch i is predicted to be taken, then a
; new instruction won't be fetched during this cycle, i.e. fetch-inst?
; is not asserted.  If the prediction mechanism guesses that i is not
; taken, we continue fetch instruction and fetch-inst? is asserted.
(defthm inst-wrong-branch-step-IFU-inst-if-fetch-inst
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (INST-p I)
		  (INST-in i MT)
		  (b1p (fetch-inst? MA sigs))
		  (IFU-stg-p (INST-stg i)))
	     (equal (INST-wrong-branch? (step-INST i MT MA sigs))
		    (INST-wrong-branch? i)))
  :hints (("Goal" :in-theory (enable INST-wrong-branch? lift-b-ops
				     fetch-inst?
				     equal-b1p-converter
				     equal-to-b1p-b-eqv))))

(defthm not-inst-start-specultv-step-inst-if-fetch-inst
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT)
		  (MA-input-p sigs) (INST-p i)
		  (INST-in i MT)
		  (IFU-stg-p (INST-stg i))
		  (b1p (fetch-inst? MA sigs)))
	     (equal (INST-start-specultv? (step-INST i MT MA sigs))
		    (INST-start-specultv? i)))
  :hints (("Goal" :in-theory (enable inst-start-specultv?
				     lift-b-ops
				     equal-b1p-converter))))

(encapsulate nil
(local
 (defthm not-commit-stg-p-step-inst-if-earlier-is-committed-p
     (implies (and (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (inst-in-order-p i j MT)
		   (INST-p i) (INST-in i MT)
		   (INST-p j) (INST-in j MT)
		   (not (committed-p i)))
	      (not (commit-stg-p (INST-stg (step-INST j MT MA sigs)))))
   :hints (("goal" :use ((:instance INST-is-at-one-of-the-stages)
			 (:instance INST-is-at-one-of-the-stages (i j)))
		   :in-theory (disable INST-is-at-one-of-the-stages)))))

(local
 (defthm not-retire-stg-p-step-inst-if-earlier-is-committed-p
     (implies (and (inv MT MA)
		   (MAETT-p MT) (MA-state-p MA)
		   (inst-in-order-p i j MT)
		   (INST-p i) (INST-in i MT)
		   (INST-p j) (INST-in j MT)
		   (not (committed-p i)))
	      (not (retire-stg-p (INST-stg (step-INST j MT MA sigs)))))
   :hints (("goal" :use ((:instance INST-is-at-one-of-the-stages)
			 (:instance INST-is-at-one-of-the-stages (i j)))
		   :in-theory (disable INST-is-at-one-of-the-stages)))))

(local
 (defthm no-commit-inst-p-step-trace-if-car-is-not-retire-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (tail-p sub trace)
		  (INST-listp trace) (MA-input-p sigs)
		  (INST-listp sub)
		  (not (equal sub trace))
		  (not (b1p (ex-intr? MA sigs)))
		  (not (committed-p (car trace))))
	     (no-commit-inst-p
	      (step-trace sub MT MA sigs isa spc smc)))
   :hints (("goal" :induct (step-trace sub MT MA sigs isa spc smc)
		   :restrict
		   ((not-commit-stg-p-step-inst-if-earlier-is-committed-p
		     ((i (car trace))))
		    (not-retire-stg-p-step-inst-if-earlier-is-committed-p
		     ((i (car trace))))))
	   (when-found (inst-listp trace)
		       (:cases ((consp trace)))))))

(defthm no-commit-inst-p-step-trace-if-car-is-not-retire
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (consp trace)
		  (INST-listp trace) (MA-input-p sigs)
		  (not (b1p (ex-intr? MA sigs)))
		  (not (committed-p (car trace))))
	     (no-commit-inst-p
	      (step-trace (cdr trace) MT MA sigs isa spc smc))))
)

(defthm trace-all-specultv-p-step-trace
    (implies (and (inv MT MA)
		  (trace-all-specultv-p trace)
		  (MA-state-p MA) (MAETT-p MT)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (not (b1p (ex-intr? MA sigs)))
		  (b1p spc))
	     (trace-all-specultv-p
	      (step-trace trace MT MA sigs ISA spc smc)))
  :hints (("goal" :in-theory (enable lift-b-ops))))

; Matt K. mod: Proof no longer succeeds.  To fix it may require some reasonably
; deep understanding of this proof effort.
(skip-proofs
(defthm trace-correct-speculation-p-step-trace
    (implies (and (inv MT MA)
		  (trace-correct-speculation-p trace)
		  (MA-state-p MA) (MAETT-p MT)
		  (MA-input-p sigs)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (not (b1p spc))
		  (not (trace-CMI-p
			(step-trace trace MT MA sigs ISA spc smc))))
	     (trace-correct-speculation-p (step-trace trace MT MA sigs ISA
						      spc smc)))
  :hints (("goal" :in-theory (e/d (lift-b-ops committed-p)
				  (INST-STG-STEP-IFU-INST-IF-DQ-FULL
				   INST-is-at-one-of-the-stages
				   dispatch-commit-inst-stages)))
	  (when-found-multiple ((IFU-STG-P (INST-STG (CAR TRACE)))
				(cdr trace))
			       (:cases ((consp (cdr trace)))))
	  (when-found (B1P (INST-EXINTR-NOW? (CAR TRACE) MA SIGS))
		      (:cases ((b1p (ex-intr? MA sigs)))))
	  (when-found (TRACE-CMI-P
		       (STEP-TRACE (CDR TRACE)
				   MT MA SIGS (INST-POST-ISA (CAR TRACE))
				   (B-IOR (INST-SPECULTV? (CAR TRACE))
					  (INST-START-SPECULTV? (CAR TRACE)))
				   (INST-MODIFIED? (CAR TRACE))))
		      (:use (:instance INST-is-at-one-of-the-stages
				       (i (car trace)))))
	  (when-found (TRACE-CORRECT-SPECULATION-P
		       (STEP-TRACE (CDR TRACE)
				   MT MA SIGS (INST-POST-ISA (CAR TRACE))
				   (B-IOR (INST-SPECULTV? (CAR TRACE))
					  (INST-START-SPECULTV? (CAR TRACE)))
				   (INST-MODIFIED? (CAR TRACE))))
		      (:use (:instance INST-is-at-one-of-the-stages
				       (i (car trace)))))
	  (when-found (B1P (B-IOR (INST-SPECULTV? (CAR TRACE))
				  (INST-START-SPECULTV? (CAR TRACE))))
		      (:use (:instance INST-is-at-one-of-the-stages
				       (i (car trace)))))
	  (when-found (TRACE-CORRECT-SPECULATION-P (CDR TRACE))
		      (:use (:instance INST-is-at-one-of-the-stages
				       (i (car trace)))))))
)

(defthm correct-speculation-p-preserved
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT) (MA-input-p sigs)
		  (not (MT-CMI-p (MT-step MT MA sigs))))
	     (correct-speculation-p (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable correct-speculation-p
				     MT-CMI-p
				     inv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Proof of no-specultv-commit-p-preserved
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Proof of no-specultv-commit-p for initial states
(defthm no-specultv-commit-p-init-MT
    (implies (and (MA-state-p MA) (b1p (MA-flushed? MA)))
	     (no-specultv-commit-p (init-MT MA)))
  :hints (("goal" :in-theory (enable no-specultv-commit-p init-MT))))

;;;; Step case
(encapsulate nil
(local
(defthm no-specultv-commit-p-preserved-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MA-state-p MA) (MAETT-p MT) (MA-input-p sigs)
		  (not (MT-CMI-p (MT-step MT MA sigs))))
	     (trace-no-specultv-commit-p (step-trace trace MT MA sigs
						     ISA spc smc)))
  :hints (("Goal" :in-theory (enable lift-b-ops
				     committed-p
				     NOT-INST-SPECULTV-INST-IN-IF-COMMITTED))
	  (when-found (COMMIT-STG-P (INST-STG (STEP-INST (CAR TRACE)
							 MT MA SIGS)))
		      (:cases ((committed-p (car trace)))))
	  (when-found (RETIRE-STG-P (INST-STG (STEP-INST (CAR TRACE)
							 MT MA SIGS)))
		      (:cases ((committed-p (car trace))))))))

(defthm no-specultv-commit-p-preserved
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT) (MA-input-p sigs)
		  (not (MT-CMI-p (MT-step MT MA sigs))))
	     (no-specultv-commit-p (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable MT-step
				     no-specultv-commit-p))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Proof of correct-exintr-p-preserved     
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof of correct-exintr-p for initial states
(defthm correct-exintr-p-init-MT
    (correct-exintr-p (init-MT MA))
  :hints (("goal" :in-theory (enable init-MT correct-exintr-p))))

;; Invariant proof
(encapsulate nil
(local
(defthm INST-exintr-if-not-retire-help
    (implies (and (member-equal i trace)
		  (trace-correct-exintr-p trace)
		  (INST-p i)
		  (not (retire-stg-p (INST-stg i))))
	     (equal (INST-exintr? i) 0))
  :hints (("Goal" :in-theory (enable lift-b-ops equal-b1p-converter)))))
  
(defthm INST-exintr-if-not-retire
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA) 
		  (not (retire-stg-p (INST-stg i))))
	     (equal (INST-exintr? i) 0))
  :hints (("Goal" :in-theory (enable inv CORRECT-EXINTR-P INST-in))))
)

(encapsulate nil
(local
(defthm correct-exintr-p-preserved-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (MAETT-p MT) (MA-state-p MA))
	     (trace-correct-exintr-p (step-trace trace MT MA sigs
						 ISA spc smc)))
  :hints ((when-found (RETIRE-STG-P (INST-STG (STEP-INST (CAR TRACE)
							 MT MA SIGS)))
		      (:cases ((retire-stg-p (INST-stg (car trace)))))))))

(defthm correct-exintr-p-preserved
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (correct-exintr-p (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable correct-exintr-p))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; misc-inv
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; proof of misc-inv for initial states
(defthm misc-inv-init-MT
    (implies (and (MA-state-p MA) (b1p (MA-flushed? MA)))
	     (misc-inv (init-MT MA) MA))
  :hints (("goal" :in-theory (enable init-MT misc-inv lift-b-ops
				     ROB-empty? MA-flushed?
				     CORRECT-ENTRIES-IN-DQ-P
				     DQ-empty?
				     equal-b1p-converter))))

;; Invariant Proof
(defthm rob-head-MA-rob-MA-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (ROB-head (MA-ROB (MA-step MA sigs)))
		    (MT-ROB-head (MT-step MT MA sigs))))
  :hints (("Goal" :in-theory (enable MT-step step-mt-rob-head))))

(defthm rob-tail-MA-rob-MA-step
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (ROB-tail (MA-ROB (MA-step MA sigs)))
		    (MT-ROB-tail (MT-step MT MA sigs))))
  :hints (("Goal" :in-theory (enable MT-step step-mt-rob-tail))))

; this should follow mt-dq-len-lt-4
(defthm MT-dq-len-le-4
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA))
	     (<= (MT-dq-len MT) 4))
  :hints (("Goal" :in-theory (enable inv misc-inv)))
  :rule-classes :linear)
     
(defthm MT-DQ-len-le-4-MT-step
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA))
	     (<= (MT-DQ-len (MT-step MT MA sigs)) 4))
  :hints (("Goal" :in-theory (enable MT-step STEP-MT-DQ-LEN
				     lift-b-ops DQ-FULL?)))
  :rule-classes :linear)

(defthm not-dispatch-inst-if-MT-dq-len-0
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA) 
		  (equal (MT-DQ-len MT) 0))
	     (equal (dispatch-inst? MA) 0))
  :hints (("goal" :in-theory (enable dispatch-inst? lift-b-ops
				     dispatch-no-unit?
				     dispatch-to-IU? dispatch-to-MU?
				     dispatch-to-BU? dispatch-to-LSU?
				     DQ-ready-no-unit? DQ-ready-to-IU?
				     DQ-ready-to-MU? DQ-ready-to-BU?
				     DQ-ready-to-LSU? equal-b1p-converter))))

(defthm correct-entries-in-DQ-p-preserved
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA))
	     (correct-entries-in-DQ-p (MT-step MT MA sigs) (MA-step MA sigs)))
  :hints (("Goal" :in-theory (e/d (correct-entries-in-DQ-p MT-step
				     step-de0 step-de1 step-de2 step-de3
				     STEP-MT-DQ-LEN
				     decode-output DQ-FULL?
				     de1-out de2-out de3-out 
				     lift-b-ops)
			  ()))))

(defthm rob-flg-MA-step-=-MA-rob-flg-MT-step
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA))
	     (equal (ROB-flg (MA-rob (MA-step MA sigs)))
		    (MT-rob-flg (MT-step MT MA sigs))))
  :hints (("Goal" :in-theory (enable step-rob MT-step step-MT-rob-flg))))

(defthm misc-inv-preserved
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA))
	     (misc-inv (MT-step MT MA sigs) (MA-step MA sigs)))
  :hints (("Goal" :in-theory (e/d (misc-inv)
				  (MA-ROB-MA-STEP)))))

(deflabel end-misc-inv)
