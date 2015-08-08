
;; Parsimony tree scoring.

;; The two top-level functions are
;; (pscore-tree tree sequences cssl-map matrix) and
;; (pscore-trees trees sequences cssl-map matrix).

;; Arguments:

;; matrix - A cost matrix containing distances between (unambiguous)
;; nucleotides (or whatever states are used). This is an alist such that
;; (assoc-equal a matrix) equals the cost of a transition from a (the parent)
;; to each of n children where the nth child has a transition cost of (nth (cdr
;; (assoc-equal a matrix))).  Entries in the matrix need to be made in a
;; consistent order; i.e. all inner lists have the same order as the outer
;; alist.  We've defined the constant *dna-matrix* at the end of this file for
;; use with typical DNA sequences.

;; cssl-map - For dealing with ambiguous states.  A fast alist
;; which maps every character state, including ambiguous ones, to a list containing one
;; element (either 0 or nil for infinity) for each unambiguous state.  This
;; lets us answer the question "What is the cost of this subtree given that its
;; root is in state x" where x is some unambiguous state and the subtree is a
;; leaf.  If the state at the leaf is y (which may be ambiguous), we look up y
;; in the mapping.  This gives a list of 0s and nils, one for each unambiguous
;; state.  If x is the nth entry in matrix, the nth entry in this list gives
;; the cost of the subtree.  So if we are looking at DNA sequences (with
;; unambiguous states A C T G), and R is the symbol for the ambiguous state
;; which could be A or G, then the entry for R should be (0 nil nil 0).  The
;; unambiguous states should be present as well; for example, T should map to
;; (nil nil 0 nil).  *dna-scorelists* at the end of this file is an example
;; for typical DNA sequences.

;; sequences - a fast alist mapping taxon names to sequences, each sequence
;; being a list of characters

;; tree - a tree in the typical TASPI form whose leaves are keys in sequences.

;; trees - a list of such trees.

;; (pscore-tree tree sequences cssl-map matrix) gives the parsimony score of
;; the given tree.

;; (pscore-trees trees sequences cssl-map matrix) gives a list containing the
;; parsimony scores of all the trees in the list.

(in-package "ACL2")
(include-book "costs")

;; The idea is that given a char-scorelist for each child node, we can
;; calculate the scorelist for the parent node: We need, for each character c and
;; state x, the cost contribution of c of the subtree rooted at the
;; parent given that c(parent) = x.  This value is
;; the sum over children a of
;;        the minimum over the states y of
;;                  the cost of the subtree rooted at a given c(a) = y
;;                      plus the cost of the transition from x to y.
;; We can get the char-scorelist for a leaf node by simply looking up each
;; state in the sequence in the scorelist-map (see make-leaf-score-list), and
;; we can get the final score for the tree from the char-scorelist for the root
;; node by summing the list of minima of its elements.

;; find-smallest-addition adds in the score contribution of one of the children
;; to the parent scorelist.  Doing this for all children results in the final
;; parent scorelist.

;; Finds the minimum of the subtree cost + transition cost given the list of
;; subtree costs and the list of transition costs.

;; add two scorelists returning smallest possible score
;; CurList is the scorelist at some child, and the translist is from
;; assuming we're transitioning to some particular character state at the
;; parent.  We are finding how much that transition would
;; cost for this subtree, essentially picking how to set the child charstate to
;; minimize the cost of the subtree given the parent assignment.
(defun find-smallest-addition (curList translist)
  (declare (xargs :guard (and (rational-or-nil-listp curList)
                              (equal (len curList) (len translist))
                              (rational-or-nil-listp translist))
                  :verify-guards nil))
  (if (atom curList)
      nil ;; infinity
    (min-nil-inf (plus-nil-inf (car curList) (car translist))
                 (find-smallest-addition (cdr curList) (cdr translist)))))

(defthm rationalp-find-smallest-addition
  (implies (and (rational-or-nil-listp child)
                (rational-or-nil-listp translist)
                (equal (len child) (len translist))
                (find-smallest-addition child translist))
           (rationalp (find-smallest-addition child translist))))

(verify-guards find-smallest-addition)

;; Adds the minimum cost contribution of the child for each assignment of state
;; to the parent. (this is for one position in a sequence)
(defun add-min-cost-to-parent-scorelist (parent child matrix)
  (declare (xargs :guard (and (cost-matrixp-nstates matrix (len child))
                              (equal (len parent) (len matrix))
                              (rational-or-nil-listp child)
                              (rational-or-nil-listp parent))))
  (if (atom parent)
      nil
    (cons (plus-nil-inf
           (car parent) (find-smallest-addition child (cdar matrix)))
          (add-min-cost-to-parent-scorelist (cdr parent) child (cdr matrix)))))

(defthm len-add-min-cost-to-parent-scorelist
  (equal (len (add-min-cost-to-parent-scorelist parent child matrix))
         (len parent)))

(defthm rational-or-nil-listp-add-min-cost-to-parent-scorelist
  (implies (and (cost-matrixp-nstates matrix (len child))
                (equal (len parent) (len matrix))
                (rational-or-nil-listp child)
                (rational-or-nil-listp parent))
           (rational-or-nil-listp (add-min-cost-to-parent-scorelist
                                   parent
                                   child matrix)))
  :hints (("Subgoal *1/5''" :in-theory (disable
                                        rationalp-find-smallest-addition)
           :use (:instance rationalp-find-smallest-addition
                           (translist (cdar matrix))))))
(local
 (defthm consp-not-len-0
   (implies (consp x)
            (not (equal (len x) 0)))))

;; Adds in a child's entire sequence contribution to the scorelist of the parent.
(defun combine-scorelists-for-sequence (parent child matrix)
  (declare (xargs :guard (and (sequence-scorelistp parent (len matrix))
                              (sequence-scorelistp child (len matrix))
                              (equal (len parent) (len child))
                              (cost-matrixp-nstates matrix (len matrix)))))
  (if (atom parent)
      nil
    (cons (add-min-cost-to-parent-scorelist (car parent) (car child) matrix)
          (combine-scorelists-for-sequence (cdr parent) (cdr child) matrix))))

(defthm len-combine-scorelists
  (equal (len (combine-scorelists-for-sequence parent child matrix))
         (len parent)))

(defthm combine-scorelists-char-scorelistp
  (implies (and (sequence-scorelistp parent (len matrix))
                (sequence-scorelistp child (len matrix))
                (equal (len parent) (len child))
                (cost-matrixp-nstates matrix (len matrix)))
           (sequence-scorelistp (combine-scorelists-for-sequence parent child matrix)
                                (len matrix))))

;; Instead of making an all-zero parent scorelist to start with, we can take
;; the scores from the first child as the initial values and skip a step.

;; This makes the initial scorelist for one character
(defun init-scores-char (child matrix)
  (declare (xargs :guard (and (cost-matrixp-nstates matrix (len child))
                              (rational-or-nil-listp child))))
  (if (atom matrix)
      nil
    (cons (find-smallest-addition child (cdar matrix))
          (init-scores-char child (cdr matrix)))))

(defthm len-init-scores-char
  (equal (len (init-scores-char child matrix))
         (len matrix)))

(defthm rational-or-nil-listp-init-scores-char
  (implies (and (cost-matrixp-nstates matrix (len child))
                (rational-or-nil-listp child))
           (rational-or-nil-listp (init-scores-char child matrix))))

;; Makes a (whole-sequence) initial scorelist for a parent based on the
;; scorelist of the first child.
(defun init-scorelist (child matrix)
  (declare (xargs :guard (and (sequence-scorelistp child (len matrix))
                              (cost-matrixp-nstates matrix (len matrix)))))
  (if (atom child)
      nil
    (cons (init-scores-char (car child) matrix)
          (init-scorelist (cdr child) matrix))))

(defthm len-init-scorelist
  (equal (len (init-scorelist child matrix))
         (len child)))

(defthm init-scorelists-char-scorelistp
  (implies (and (sequence-scorelistp child (len matrix))
                (cost-matrixp-nstates matrix (len matrix)))
           (sequence-scorelistp (init-scorelist child matrix) (len matrix))))

;; Identifies a list of scorelists, all of the same length len and for alpha-len
;; possible states.
(defun scorelist-listp (x len alpha-len)
  (declare (xargs :guard (and (integerp len)
                              (integerp alpha-len))))
  (if (atom x)
      t
    (and (sequence-scorelistp (car x) alpha-len)
         (equal (len (car x)) len)
         (scorelist-listp (cdr x) len alpha-len))))

;; Given the list of scorelists for all children, makes the scorelist of the
;; parent.  This can be called initially with init-scorelist like this:
;; (make-internal-score-list (cdr scorelists)
;;                           matrix
;;                           (init-scorelist (car scorelists) matrix))
(defun make-internal-score-list (scorelists matrix parentSoFar)
  (declare (xargs :guard (and (sequence-scorelistp parentSoFar (len matrix))
                              (scorelist-listp scorelists (len parentSoFar) (len matrix))
                              (cost-matrixp-nstates matrix (len matrix)))))
  (if (atom scorelists)
      parentSoFar
    (make-internal-score-list
     (cdr scorelists) matrix
     (combine-scorelists-for-sequence parentSoFar (car scorelists) matrix))))

(defthm sequence-scorelistp-make-internal-score-list
  (implies (and (sequence-scorelistp parentSoFar (len matrix))
                (scorelist-listp scorelists (len parentSoFar) (len matrix))
                (cost-matrixp-nstates matrix (len matrix)))
           (sequence-scorelistp (make-internal-score-list scorelists
                                                          matrix
                                                          parentSofar)
                                (len matrix))))

(defthm len-make-internal-score-list
  (equal (len (make-internal-score-list scorelists matrix parentSoFar))
         (len parentSoFar)))

;; #|
;; two children, two characters, three states
;; cost matrix:
;; '((a . (0 1 1))
;;   (b . (1 0 1))
;;   (c . (1 1 0)))

;; first child:
;; '((0 nil nil) (nil 0 nil))

;; second child:
;; '((nil nil 0) (nil 0 nil))

;; parent should be
;; '((1 2 1) (2 0 2))

;;  (let* ((matrix '((a . (0 1 1))
;;                   (b . (1 0 1))
;;                   (c . (1 1 0))))
;;         (scorelists '(((0 nil nil) (nil 0 nil))
;;                       ((nil nil 0) (nil 0 nil)))))
;;    (make-internal-score-list (cdr scorelists) matrix
;;                              (init-scorelist (car scorelists) matrix)))

;; |#


;; if flg:
;;     Return the sequence scorelist for tree
;; if (not flg):
;;     List the scorelists for all children in the list of subtrees tree.
(defun score-tree-and-sequences (flg tree sequences cssl-map matrix alpha-len)
  (declare (xargs :guard (and (valid-sequences-same-length sequences)
                              (tree-matches-sequences flg tree sequences)
                              (integerp alpha-len)
                              (equal (len matrix) alpha-len)
                              (charstate-scorelist-map-p cssl-map alpha-len)
                              (cost-matrixp-nstates matrix alpha-len))
                  :verify-guards nil
                  :measure (tree-measure tree flg)))
  (if flg
      ;; One tree
      (if (atom tree)
          ;; Scorelist based immediately on a sequence
          (make-leaf-score-list (cdr (het tree sequences)) cssl-map alpha-len)

        ;; Sum contributions of all children:
        (score-tree-and-sequences nil tree sequences cssl-map matrix alpha-len))

    ;; List of trees
    (if (atom tree)
        nil
      (if (atom (cdr tree))
          (init-scorelist (score-tree-and-sequences t (car tree) sequences
                                                    cssl-map matrix alpha-len)
                          matrix)
        (combine-scorelists-for-sequence ;parent child matrix
         (score-tree-and-sequences nil (cdr tree) sequences cssl-map matrix alpha-len)
         (score-tree-and-sequences t (car tree) sequences cssl-map matrix
                                   alpha-len)
         matrix)))))

;; Lemmas for guards of score-tree-and-sequences
(defun length-n-list (l n)
  (declare (xargs :guard (acl2-count n)))
  (if (atom l)
      t
    (and (equal (len (car l)) n)
         (length-n-list (cdr l) n))))

(defthm len-score-tree-and-sequences
  (implies (and (or flg (consp tree))
                (valid-sequences-same-length sequences)
                (tree-matches-sequences flg tree sequences))
           (equal (len (score-tree-and-sequences flg tree sequences
                                                 cssl-map matrix alpha-len))
                  (len (cdar sequences)))))

(defthm scorelistp-score-tree-and-sequences
  (implies (and (or flg (consp tree))
                (tree-matches-sequences flg tree sequences)
                (valid-sequences-same-length sequences)
                (equal (len matrix) alpha-len)
                (charstate-scorelist-map-p cssl-map alpha-len)
                (cost-matrixp-nstates matrix alpha-len))
           (sequence-scorelistp (score-tree-and-sequences flg tree sequences
                                                      cssl-map matrix
                                                      alpha-len)
                            (len matrix))))

(verify-guards score-tree-and-sequences)


;; To get the score of a tree given the scorelist of the root, sum (for all
;; characters) the minimum (over state assignments to the root) contribution of
;; that character to the score.

;; Top-level function for scoring a single tree:  takes the tree, the sequence
;; alist, the scorelist map, and the cost matrix; returns the score of the tree.
(defun pscore-tree (tree sequences cssl-map matrix)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Scores a tree under parsimony~/
;  ~/
;  Arguments:
;    (1) tree - a single phylogenetic tree
;    (2) sequences - a mapping of taxa to sequences
;    (3) cssl-map -  An alist mapping every character state,
;                    including ambiguous ones, to a list containing
;                    one element (either 0 or nil for infinity) for
;                    each unambiguous state.
;    (4) matrix - A mapping of unambiguous character states to
;                 transition costs.
;
;  Details: Does not handle branch lengths."
  (declare (xargs :guard (and (valid-sequences-same-length sequences)
                              (tree-matches-sequences t tree sequences)
                              (charstate-scorelist-map-p cssl-map (len matrix))
                              (cost-matrixp-nstates matrix (len matrix)))
                  :guard-hints
                  (("Goal'"
                    :use (:instance
                          char-scorelistp-rational-or-nil-list-listp
                          (x (score-tree-and-sequences t tree sequences cssl-map
                                                       matrix (len matrix)))
                          (n (len matrix)))
                    :in-theory (disable char-scorelistp-rational-or-nil-list-listp)))))
  (let ((scorelist (score-tree-and-sequences t tree sequences cssl-map
                                             matrix (len matrix))))
    (sum-minima scorelist)))

;; Scores a list of trees all with the same sequences and matrix.
(defun pscore-trees (trees sequences cssl-map matrix)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Scores a list of trees under parsimony~/
;  ~/
;  Arguments:
;     (1) trees - a list of  phylogenetic trees
;     (2) sequences - a mapping of taxa to sequences
;     (3) cssl-map -  An alist mapping every character state to a
;                     list containing one element (either 0 or nil
;                     for infinity) for each unambiguous state
;     (4) matrix - A mapping of unambiguous character states to
;                  transition costs.

;  Details: Does not handle branch lengths."
  (declare (xargs :guard (and (valid-sequences-same-length sequences)
                              (tree-matches-sequences nil trees sequences)
                              (charstate-scorelist-map-p cssl-map (len matrix))
                              (cost-matrixp-nstates matrix (len matrix)))))
  (if (atom trees)
      nil
    (cons (pscore-tree (car trees) sequences cssl-map matrix)
          (pscore-trees (cdr trees) sequences cssl-map matrix))))


;;Default cost matrix for DNA;
;; just 0 for no transition and 1 for any transition.
(defconst *dna-matrix*
   (make-default-cost-matrix '(a c t g))

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;  A dna transition cost matrix with all transitions having cost 1.~/
;  ~/
;  "
)

(defconst *dna-cssl*
  (build-fast-alist-from-alist
   '((a    0   nil nil nil)
     (c    nil 0   nil nil)
     (t    nil nil 0   nil)
     (g    nil nil nil 0  )
     (r    0   nil nil 0  )
     (y    nil 0   0   nil)
     (m    0   0   nil nil)
     (k    nil nil 0   0  )
     (s    nil 0   nil 0  )
     (w    0   nil 0   nil)
     (h    0   0   0   nil)
     (b    nil 0   0   0  )
     (v    0   0   nil 0  )
     (d    0   nil 0   0  )
     (n    0   0   0   0  )
     (-    0   0   0   0  )
     (?    0   0   0   0  ))
  'dna-cssl)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  The usual mapping for dna character states to their dna score-list.~/
;  ~/
;  "
  )

#||

EXAMPLES!  see also testing.lisp


(let ((seqs (build-fast-alist-from-alist
             '((1 a c t g a)  ; Taxon . Sequence
               (2 g g g g g)
               (3 a c t g g)
               (4 g g g a a)
               (5 c c t a t))))
      (trees '(((1 2) (3 (4 5)))
               (((1 2) 4) (3 5))
               (1 ((2 4) (3 5)))
               (1 ((2 (3 4)) 5)))))
  (pscore-trees trees seqs  *dna-cssl* *dna-matrix*))

(let ((seqs (build-fast-alist-from-alist
             '((1 a c t g - a)  ; Taxon . Sequence
               (2 g g - g g g)
               (3 a - c t g g)
               (4 g g g - a a)
               (5 c c t - a t))))
      (trees '(((1 2) (3 (4 5)))
               (((1 2) 4) (3 5))
               (1 ((2 4) (3 5)))
               (1 ((2 (3 4)) 5)))))
  (pscore-trees trees seqs  *dna-cssl* *dna-matrix*))

(let ((seqs (build-fast-alist-from-alist
             '((1 a c t g - a)  ; Taxon . Sequence
               (2 g g - g g g)
               (3 t - c t g g)
               (4 g g g - a a)
               (5 c c t - a t))))
      (trees '(((1 2) (3 (4 5)))
               (((1 2) 4) (3 5))
               (1 ((2 4) (3 5)))
               (1 ((2 (3 4)) 5)))))
  (pscore-trees trees seqs  *dna-cssl* *dna-matrix*))

||#

