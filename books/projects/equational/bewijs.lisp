;; Utrecht Texas Equational Prover
;; Written by Grant Olney Passmore {grant@math.utexas.edu}
;;
;; Proof manipulation routines.
;;  (... `bewijs' is `proof' in Dutch! :) )

(in-package "ACL2")

;; RAW-CLAUSES-TO-AXIOM-MOVES (input-clauses)
;; Given a list of input clauses, return the result of structuring them
;; into valid LOVEY proof-moves.
;; G. Passmore :: 12/23/05
;;
;; Updated on 11/14/06 to differentiate between SOS and USABLE at the
;; name level by prefixing S or U to the (now) id conses.

(defun raw-clauses-to-axiom-moves* (input-clauses cur-clause-id prefix)
  (if (endp input-clauses) nil
    (cons (list (list prefix cur-clause-id)
		(list 'move ':AXIOM)
		(car input-clauses))
	  (raw-clauses-to-axiom-moves* (cdr input-clauses) (1+ cur-clause-id) prefix))))

;;
;; For backwards compatability, raw-clauses-to-axiom-moves defaults to
;; 0 and SOS.

(defun raw-clauses-to-axiom-moves (input-clauses)
  (raw-clauses-to-axiom-moves* input-clauses 0 'S))

;; CROP-PROOF-END-AT-LINE-ID (linear-move-proof-tree end-line-id)
;; Given an end-line-id for a linear-move-proof-tree, return the result of
;; cropping it at the end-line-id.  This is to make proof output prettier,
;; so that multiple NIL derivations aren't listed (we just show the first).
;; G. Passmore :: 12/23/05

(defun crop-proof-end-at-line-id (linear-move-proof-tree end-line-id)
  (if (endp linear-move-proof-tree) nil
   (if (equal (caar linear-move-proof-tree) end-line-id)
       (list (car linear-move-proof-tree))
      (cons (car linear-move-proof-tree)
            (crop-proof-end-at-line-id (cdr linear-move-proof-tree) end-line-id)))))

;; PRUNE-PROOF-TREE* (raw-linear-mpt)
;; Given a raw linear move-proof-tree already cropped to its sought refutation,
;; return the linear proof tree only containing the clauses used in the
;; derivation.
;; Note: Naming parent function PRUNE-PROOF-TREE* as ACL2 has a :program mode
;; function with the name PRUNE-PROOF-TREE.
;; G. Passmore :: 12/24/05

(defun prune-proof-tree** (revd-remaining-clauses cur-tree flagged-clauses)
  (if (endp revd-remaining-clauses) cur-tree
    (let ((cur-move (car revd-remaining-clauses)))
      (let ((cur-move-id (car cur-move))
	    (cur-move-defence (cadr cur-move)))
	(if (or (member-equal cur-move-id flagged-clauses)
		(endp flagged-clauses))
	    (let ((new-flagged-clauses
		   (cond ((equal (cadr cur-move-defence) ':AXIOM) flagged-clauses)
			 ((or (equal (cadr cur-move-defence) ':BINARY-RESOLUTION)
			      (equal (cadr cur-move-defence) ':BINARY-RESOLUTION-AND-MERGING))
			  (append (list (caaddr cur-move-defence) (caaddr (cdr cur-move-defence)))
				  flagged-clauses))
			 ((equal (cadr cur-move-defence) ':BINARY-FACTORING)
			  (append (list (caaddr cur-move-defence)) flagged-clauses))
			 ((equal (cadr cur-move-defence) ':MERGE-CLAUSE)
			  (append (list (caaddr cur-move-defence)) flagged-clauses))
			 ((equal (cadr cur-move-defence) ':PARAMODULATION)
			  (append (list (caaddr cur-move-defence) (caaddr (cdr cur-move-defence))) flagged-clauses)))))
	      (prune-proof-tree** (cdr revd-remaining-clauses) (cons cur-move cur-tree) new-flagged-clauses))
	  (prune-proof-tree** (cdr revd-remaining-clauses) cur-tree flagged-clauses))))))

(defun prune-proof-tree* (raw-linear-mpt)
  (prune-proof-tree** (reverse raw-linear-mpt) nil nil))
