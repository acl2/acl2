;; Parsimony tree scoring
;; Separate (more efficient) algorithm for the case where all transitions
;; cost 1.  Written in most part by Sol Swords.

(in-package "ACL2")
(include-book "costs")

(local (in-theory (e/d (mv-nth)
                       (mv-nth-cons-meta))))

;; Subproblem: Given a subtree, for each character in the sequences find the
;; minimum contribution of that subtree, and for each assignment of a state to
;; the root node decide whether that assignment can achieve the minimum
;; contribution.

(defmacro mv2-cons (call1 call2)
  `(mv-let
    (car1 car2) ,call1
    (mv-let
     (cdr1 cdr2) ,call2
     (mv (cons car1 cdr1) (cons car2 cdr2)))))


(defun fitch-combine-scores1 (first-score first-states rest-states)
  (declare (xargs :guard (and (rational-or-nil-listp first-states)
                              (rational-or-nil-listp rest-states)
                              (or (rationalp first-score) (not first-score))
                              (equal (len first-states) (len rest-states)))
                  :verify-guards nil))
  (if (atom first-states)
      (mv nil nil)
    (mv-let
     (cdr-score cdr-states)
     (fitch-combine-scores1 first-score (cdr first-states) (cdr rest-states))
     (let ((car-score (plus-nil-inf (min-nil-inf (car first-states)
                                                 (plus-nil-inf 1 first-score))
                                    (car rest-states))))
       (mv (min-nil-inf car-score cdr-score)
           (cons car-score cdr-states))))))

(defthm fitch-combine-scores1-car
  (implies (and (rational-or-nil-listp first-states)
                (rational-or-nil-listp rest-states)
                (or (rationalp first-score) (not first-score))
                (equal (len first-states) (len rest-states))
                (car (fitch-combine-scores1 first-score first-states
                                            rest-states)))
           (rationalp (car (fitch-combine-scores1 first-score first-states
                                                  rest-states)))))

(defthm fitch-combine-scores1-len
  (equal (len (mv-nth 1 (fitch-combine-scores1 first-score first-states
                                               rest-states)))
         (len first-states)))

(defthm fitch-combine-scores1-rational-or-nil-listp
  (implies (and (rational-or-nil-listp first-states)
                (rational-or-nil-listp rest-states)
                (or (rationalp first-score) (not first-score))
                (equal (len first-states) (len rest-states)))
           (rational-or-nil-listp
            (mv-nth 1 (fitch-combine-scores1 first-score first-states rest-states)))))

(local
 (defthm consp-not-len-0
   (implies (consp x)
            (not (equal (len x) 0)))))

(verify-guards fitch-combine-scores1)


(defun fitch-combine-scores (first-scores first-states rest-states alpha-len)
  (declare (xargs :guard (and (rational-or-nil-listp first-scores)
                              (acl2-numberp alpha-len)
                              (sequence-scorelistp first-states alpha-len)
                              (sequence-scorelistp rest-states alpha-len)
                              (equal (len first-scores) (len first-states))
                              (equal (len first-scores) (len rest-states)))))
  (if (atom first-scores)
      (mv nil nil)
    (mv2-cons (fitch-combine-scores1 (car first-scores) (car first-states)
                                     (car rest-states))
              (fitch-combine-scores (cdr first-scores) (cdr first-states)
                                    (cdr rest-states) alpha-len))))


(defthm fitch-combine-scores-len
  (and (equal (len (car (fitch-combine-scores first-scores first-states
                                              rest-states alpha-len)))
              (len first-scores))
       (equal (len (mv-nth 1 (fitch-combine-scores first-scores first-states
                                              rest-states alpha-len)))
              (len first-scores))))

(defthm fitch-combine-scores-char-scorelistp
  (implies (and (rational-or-nil-listp first-scores)
                (acl2-numberp alpha-len)
                (sequence-scorelistp first-states alpha-len)
                (sequence-scorelistp rest-states alpha-len)
                (equal (len first-scores) (len first-states))
                (equal (len first-scores) (len rest-states)))
           (sequence-scorelistp (mv-nth 1 (fitch-combine-scores first-scores first-states
                                                                rest-states alpha-len))
                            alpha-len)))

(defthm fitch-combine-scores-rational-or-nil-listp
  (implies (and (rational-or-nil-listp first-scores)
                (acl2-numberp alpha-len)
                (sequence-scorelistp first-states alpha-len)
                (sequence-scorelistp rest-states alpha-len)
                (equal (len first-scores) (len first-states))
                (equal (len first-scores) (len rest-states)))
           (rational-or-nil-listp (car (fitch-combine-scores first-scores first-states
                                                             rest-states alpha-len)))))

;given current score min-score, can you add one to any element of scores and
;get something less?  keep the smallest in new scorelist which we are building
(defun fitch-initial-scorelist1 (min-score scores)
  (declare (xargs :guard (and (or (rationalp min-score) (not min-score))
                              (rational-or-nil-listp scores))))
  (if (atom scores)
      nil
    (cons (min-nil-inf (plus-nil-inf 1 min-score) (car scores))
          (fitch-initial-scorelist1 min-score (cdr scores)))))

(defthm fitch-initial-scorelist1-len
  (equal (len (fitch-initial-scorelist1 min-score scores))
         (len scores)))

(defthm fitch-initial-scorelist1-rational-or-nil-listp
  (implies (and (or (rationalp min-score) (not min-score))
                (rational-or-nil-listp scores))
           (rational-or-nil-listp (fitch-initial-scorelist1 min-score scores))))

;;as above, for entire sequence-scorelist instead of a single character
(defun fitch-initial-scorelist (min-scores scores alpha-len)
  (declare (xargs :guard (and (rational-or-nil-listp min-scores)
                              (acl2-numberp alpha-len)
                              (sequence-scorelistp scores alpha-len)
                              (equal (len min-scores) (len scores)))))
  (if (atom min-scores)
      nil
    (cons (fitch-initial-scorelist1 (car min-scores) (car scores))
          (fitch-initial-scorelist (cdr min-scores) (cdr scores) alpha-len))))


(defthm fitch-initial-scorelist-len
  (equal (len (fitch-initial-scorelist min-scores scores alpha-len))
         (len min-scores)))


(defthm fitch-initial-scorelist-sequence-scorelistp
  (implies (and (rational-or-nil-listp min-scores)
                (acl2-numberp alpha-len)
                (sequence-scorelistp scores alpha-len)
                (equal (len min-scores) (len scores)))
           (sequence-scorelistp (fitch-initial-scorelist min-scores scores
                                                     alpha-len)
                            alpha-len)))

;; Solves the subproblem described above as follows.
;; Returns an mv where the first value is a list consisting of the minimum
;; contribution of the subtree for each character in the sequences, and the
;; second value is a list consisting of, for each character in the sequences,
;; the list of the minimum score for each assignment of state to the root.
(defun fitch-score-subtree (flg tree sequences cssl-map alpha-len)
  (declare (xargs :guard (and (or flg (consp tree))
                              (valid-sequences-same-length sequences)
                              (tree-matches-sequences flg tree sequences)
                              (natp alpha-len)
                              (charstate-scorelist-map-p cssl-map alpha-len))
                  :verify-guards nil
                  :measure (tree-measure tree flg)))
  (if flg
      ;; score subtree.
      (if (atom tree)
          (let ((seq (cdr (het tree sequences))))
            (mv (zero-scores seq) ;; minimum score should always be zero,
                ;; though we will run into trouble if the sequences aren't
                ;; well-formed with respect to the cssl-map
                (make-leaf-score-list seq cssl-map alpha-len)))
        ;;otherwise put together scores from each subtree
        (fitch-score-subtree nil tree sequences cssl-map alpha-len))

    ;; combine scores of a list of subtrees.
    (if (mbt (consp tree))
        (if (atom (cdr tree))
            (mv-let (scores state-scores) ; (len scores) equals (len sequences)
                    (fitch-score-subtree t (car tree) sequences cssl-map
                                         alpha-len)
                    (mv scores (fitch-initial-scorelist scores state-scores alpha-len)))
          (mv-let
           (rest-scores rest-states)
           (fitch-score-subtree nil (cdr tree) sequences cssl-map
                                alpha-len)
           (declare (ignore rest-scores))
           (mv-let
            (first-scores first-states)
            (fitch-score-subtree t (car tree) sequences cssl-map alpha-len)
            ;; Combine the scores from the first subtree with those from the rest
            ;; of the subtrees.
            (fitch-combine-scores first-scores first-states rest-states
                                  alpha-len))))
      (mv nil nil))))

(defthm fitch-score-subtree-len
  (implies (and (or flg (consp tree))
                (valid-sequences-same-length sequences)
                (tree-matches-sequences flg tree sequences)
                (natp alpha-len)
                (charstate-scorelist-map-p cssl-map alpha-len))
           (and (equal (len (car (fitch-score-subtree flg tree sequences cssl-map
                                                      alpha-len)))
                       (len (cdar sequences)))
                (equal (len (mv-nth 1 (fitch-score-subtree flg tree sequences cssl-map
                                                      alpha-len)))
                       (len (cdar sequences))))))

(defthm fitch-score-subtree-char-scorelistp
  (implies (and (or flg (consp tree))
                (valid-sequences-same-length sequences)
                (tree-matches-sequences flg tree sequences)
                (natp alpha-len)
                (charstate-scorelist-map-p cssl-map alpha-len))
           (and (rational-or-nil-listp
                 (car (fitch-score-subtree flg tree sequences cssl-map alpha-len)))
                (sequence-scorelistp (mv-nth 1 (fitch-score-subtree flg tree sequences
                                                                cssl-map alpha-len))
                            alpha-len))))

(verify-guards fitch-score-subtree)

(defun fitch-score-tree (tree sequences cssl-map alpha-len)
  (declare (xargs :guard (and (valid-sequences-same-length sequences)
                              (tree-matches-sequences t tree sequences)
                              (natp alpha-len)
                              (charstate-scorelist-map-p cssl-map alpha-len))))
  (mv-let (mins scores)
          (fitch-score-subtree t tree sequences cssl-map alpha-len)
          (declare (ignore scores))
          (sum-list mins)))

(defun fitch-score-trees (trees sequences cssl-map alpha-len)
  (declare (xargs :guard (and (valid-sequences-same-length sequences)
                              (tree-matches-sequences nil trees sequences)
                              (natp alpha-len)
                              (charstate-scorelist-map-p cssl-map alpha-len))))
  (if (atom trees)
      nil
    (cons (fitch-score-tree (car trees) sequences cssl-map alpha-len)
          (fitch-score-trees (cdr trees) sequences cssl-map alpha-len))))


#|
EXAMPLES: see testing.lisp
|#

