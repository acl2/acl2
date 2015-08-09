;This file is going to implement branch and bound for maximum parsimony
;Input : a set of sequences
;Output : binary tree leaf labelled as sequences, achieving best score
;start with basic, then make it better

(in-package "ACL2")
(include-book "../tree-gen-helper/basics")
(include-book "../../code/tree-manip/top")

(defun get-good-possibilities (list score acc seq cssl-map matrix)
  (declare
   (xargs
    :guard (and (valid-sequences-same-length seq)
                (tree-matches-sequences nil list seq)
                (charstate-scorelist-map-p cssl-map (len matrix))
                (rationalp score)
                (cost-matrixp-nstates matrix (len matrix)))))
  (if (consp list)
      (let ((curScore (pscore-tree (car list) seq cssl-map matrix)))
        (if (rationalp curScore) ; should be with appropriate guards
            (if (<= curScore score)
                (get-good-possibilities (cdr list) score (hons (car list) acc)
                                        seq cssl-map matrix)
              (get-good-possibilities (cdr list) score acc
                                      seq cssl-map matrix))
          "Error: Need rational score for trees in list in get-good-possibilities"))
    acc))


(defun get-new-poss-list (curList taxon score acc seq cssl-map matrix tia)
  (declare (xargs :guard
                  (and (valid-sequences-same-length seq)
                       (charstate-scorelist-map-p cssl-map (len matrix))
                       (rationalp score)
                       (cost-matrixp-nstates matrix (len matrix))
                       (good-taxon-index-halist tia))))
  (if (consp curList)
      (if (equal (len (car curlist)) 3)
          (let ((newPieces (mv-root-list
                            (orderly-addTaxa-unrooted taxon (car curList)
                                                      tia) tia nil)))
            (if (tree-matches-sequences nil newPieces seq)
                (get-new-poss-list
                 (cdr curList) taxon score
                 (get-good-possibilities
                  newPieces score acc seq cssl-map matrix)
                 seq cssl-map matrix tia)
              "Error: Need trees built up to have appropriate taxa in
get-new-poss-list"))
        "Error: Need unrooted trees in get-new-poss-list")
    acc))

(defun bandb-work (remTaxa curList score seq cssl-map matrix tia)
  (declare (xargs :guard
                  (and (valid-sequences-same-length seq)
                       (charstate-scorelist-map-p cssl-map (len matrix))
                       (rationalp score)
                       (cost-matrixp-nstates matrix (len matrix))
                       (good-taxon-index-halist tia))))
  (if (consp remTaxa)
      (prog2$ (cw "adding taxa ~p0~%" (car remTaxa))
      (bandb-work (cdr remTaxa)
                  (get-new-poss-list curList (car remTaxa) score nil
                                     seq cssl-map matrix tia)
                  score seq cssl-map matrix tia))
    curList))

;tia could/should be generated!!! here and in depth first
(defun bandb (seq cssl-map matrix tia)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Performs a breadth first branch and bound search for a maximum parsimony
;  tree for sequences~/
;  ~/
;  Arguments:
;    (1) seq - a set of sequences
;    (2) cssl-map -  An alist mapping every character state to a
;                    list containing one element (either 0 or nil
;                    for infinity) for each unambiguous state
;    (3) matrix - A mapping of unambiguous character states to
;                 transition costs.
;    (4) tia - a mapping of taxa names to integers

;  Details: The taxa names in the tia should match those given as keys in seq."
  (declare (xargs :guard
                  (and (valid-sequences-same-length seq)
                       (charstate-scorelist-map-p cssl-map (len matrix))
                       (cost-matrixp-nstates matrix (len matrix))
                       (good-taxon-index-halist tia))))
  (let ((taxa-List (get-taxa-from-sequences seq)))
    (if (<= 3 (len taxa-list))
        (let ((tree1 (build-arbitraryTree taxa-List))
              (tree2 (build-arbitraryTree1 taxa-List))
              (tree3 (build-unrooted-binary-tree taxa-List)))
          (if (and (tree-matches-sequences t tree1 seq)
                   (tree-matches-sequences t tree2 seq)
                   (tree-matches-sequences t tree3 seq))
              (let ((score1 (pscore-tree tree1
                                         seq cssl-map matrix))
                    (score2 (pscore-tree tree2
                                         seq cssl-map matrix))
                    (score3 (pscore-tree tree3
                                         seq cssl-map matrix)))
                (if (and (rationalp score1)
                         (rationalp score2)
                         (rationalp score3))
                    (let ((curScore (min-list (list score1 score2 score3))))
                      (get-best-trees (bandb-work (cdddr taxa-List)
                                                  (hist (hist (car taxa-List)
                                                              (cadr taxa-List)
                                                              (caddr taxa-list)))
                                                  curScore
                                                  seq cssl-map matrix tia)
                                      curScore
                                      nil
                                      seq cssl-map matrix))
                  (mv 'Error
                      "Error: arbitrary trees must have
                              rational scores in bandb")))
            (mv 'Error "Error: arbitrary trees must match sequences in bandb")))
      (if (tree-matches-sequences t taxa-list seq)
          (mv (pscore-tree taxa-list seq cssl-map matrix)
              taxa-list)
        (mv 'Error "Error: this should never happen in bandb")))))

;call with flg = 'search to start
(defun depth-work (flg remTaxa subs curSub score acc seq cssl-map matrix tia)
  (declare (xargs :guard
                  (and (valid-sequences-same-length seq)
                       (charstate-scorelist-map-p cssl-map (len matrix))
                       (rationalp score)
                       (cost-matrixp-nstates matrix (len matrix))
                       (good-taxon-index-halist tia))
                  :measure
                  (cons
                   (cons 1 (1+ (acl2-count remTaxa)))
                   (acl2-count subs)
                   )))
  (if (equal flg 'prune)
      (if (consp subs)
          (if (tree-matches-sequences t (car subs) seq)
              (let ((subscore (pscore-tree (car subs) seq cssl-map matrix)))
                (if (rationalp subscore)
                    (if (<= subscore score)
                        (mv-let (latestScore latestTrees)
                                (depth-work 'search remTaxa (car subs) (car subs)
                                            score acc seq cssl-map matrix tia)
                                (if (rationalp latestScore)
                                    (depth-work 'prune remTaxa (cdr subs) (car subs)
                                                latestScore latestTrees seq cssl-map
                                                matrix tia)
                                  (mv 'Error "Depth work needs to return a
                                              rational in depth-work")))
                      (depth-work 'prune remTaxa (cdr subs) (car subs)
                                  score acc seq cssl-map matrix tia))
                  (mv 'Error "Error: pscore-tree result must be
                                 rational in depth-work")))
            (mv 'Error "Error: need subtrees to match seqs in depth-work"))
        (mv score acc))
    ;(equal flg 'search)
    (if (consp remTaxa)
        (if (equal 3 (len curSub))
            (let ((newSubs (mv-root-list
                            (orderly-addTaxa-unrooted (car remTaxa) curSub tia)
                            tia nil)))
              (mv-let (newScore newtrees)
                      (depth-work 'prune (cdr remTaxa) newSubs (car newSubs)
                                  score acc seq cssl-map matrix tia)
                      (mv newScore newtrees)))
          (mv 'Error "Error: tree pieces must be unrooted in depth-work"))
      (if (tree-matches-sequences t curSub seq)
          (let ((finalscore (pscore-tree curSub seq cssl-map matrix)))
            (if (rationalp finalscore)
                (if (< finalScore score)
                    (mv finalScore (list curSub))
                  (if (equal score finalScore)
                      (mv score (cons curSub acc))
                    (mv score acc)))
              (mv 'Error "Error: pscore-tree result must be rational
                             in second branch of depth-work")))
        (mv 'Error "Error: need curSub to match seq in second branch
                           of depth-work")))))

(defun depth-bandb (seq cssl-map matrix tia)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Performs a depth first branch and bound search for a maximum parsimony
;  tree for sequences~/
;  ~/
;  Arguments:
;    (1) seq - a set of sequences
;    (2) cssl-map -  An alist mapping every character state to a
;                    list containing one element (either 0 or nil
;                    for infinity) for each unambiguous state
;    (3) matrix - A mapping of unambiguous character states to
;                 transition costs.
;    (4) tia - a mapping of taxa names to integers

;  Details: The taxa names in the tia should match those given as keys in seq."
  (declare (xargs :guard
                  (and (valid-sequences-same-length seq)
                       (charstate-scorelist-map-p cssl-map (len matrix))
                       (cost-matrixp-nstates matrix (len matrix))
                       (good-taxon-index-halist tia))))
  (let ((taxa-List (get-taxa-from-sequences seq)))
    (if (<= 3 (len taxa-list))
        (let ((tree1 (build-arbitraryTree taxa-List))
              (tree2 (build-arbitraryTree1 taxa-List))
              (tree3 (build-unrooted-binary-tree taxa-List)))
          (if (and (tree-matches-sequences t tree1 seq)
                   (tree-matches-sequences t tree2 seq)
                   (tree-matches-sequences t tree3 seq))
              (let ((score1 (pscore-tree tree1
                                         seq cssl-map matrix))
                    (score2 (pscore-tree tree2
                                         seq cssl-map matrix))
                    (score3 (pscore-tree tree3
                                         seq cssl-map matrix)))
                (if (and (rationalp score1)
                         (rationalp score2)
                         (rationalp score3))
                    (let ((curScore (min-list (list score1 score2 score3))))
                      (depth-work 'search (cdddr taxa-List) nil
                                  (hist (car taxa-List)
                                        (cadr taxa-List)
                                        (caddr taxa-list))
                                  curScore nil
                                  seq cssl-map matrix tia))
                  (mv 'Error
                      "Error: arbitrary trees must have
                              rational scores in depth-bandb")))
            (mv 'Error "Error: arbitrary trees must match sequences in depth-bandb")))
      (if (tree-matches-sequences t taxa-list seq)
          (mv (pscore-tree taxa-list seq cssl-map matrix)
              taxa-list)
        (mv 'Error "Error: this should never happen in depth-bandb")))))

#|| EXAMPLES:

See also tests/testing.lisp

(defconst *seq3* (build-fast-alist-from-alist '((a . (a c c t g))
                                                (b . (a t g a g))
                                                (c . (t c c t a))
                                                (d . (c a t t a))
                                                (e . (g c t g c)))))

(get-good-possibilities '((a (b c)) ((a b) c)) 10 nil *seq3*
                        *dna-cssl* *dna-matrix*)

(get-good-possibilities '((a (b c)) ((a b) c)) 4 nil *seq3*
                        *dna-cssl* *dna-matrix*)

(get-new-poss-list '((a (b c)) ((a b) c)) 'd 8 nil
                *seq3* *dna-cssl* *dna-matrix*)

(bandb-work '(d e) '((a (b c)) ((a c) b)) 11 *seq3* *dna-cssl* *dna-matrix*)
(bandb-work '(c b a) '((e d)) 11 *seq3* *dna-cssl* *dna-matrix*)

(time$ (bandb *seq3* *dna-cssl* *dna-matrix* (make-tia '(a b c d e))))

(let ((taxaList (get-taxa-from-charlist *seq3*)))
  (bandB-work (cddr taxaList)
              (list (list (car
                           taxaList) (cadr taxaList))) 12 *seq3*))

(depth-work 'search '(d e) nil '(a b c) 10000 nil *seq3* *dna-cssl*
            *dna-matrix*)

(time$ (depth-bandb *seq3* *dna-cssl* *dna-matrix* (make-tia (strip-cars-gen *seq3*))))
||#
