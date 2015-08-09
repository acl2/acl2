(in-package "ACL2")

(include-book "tbr")

(defun add-no-dups (list hash)
  (declare (xargs :guard t))
  (if (consp list)
      (if (het (car list) hash)
          (add-no-dups (cdr list) hash)
        (add-no-dups
         (cdr list) (hut (car list) t hash)))
    hash))

(defthm alistp-add-no-dups
  (implies (alistp-gen hash)
           (alistp-gen (add-no-dups list hash))))

(defun get-unique-spr-neighbors (curTrees hash tia)
  (declare (xargs :guard (and (good-taxon-index-halist tia)
                              (alistp-gen hash))
                  :guard-hints (("Goal" :in-theory
                                 (disable orderly-spr)))))
  (if (consp curTrees)
      (get-unique-spr-neighbors (cdr curTrees)
                                (add-no-dups
                                 (orderly-spr (car curTrees) tia)
                                 hash)
                                tia)
    (strip-cars-gen hash)))

(defun get-all-spr-neighbors (curTrees ans tia)
  (declare (xargs :guard (good-taxon-index-halist tia)))
  (if (consp curTrees)
      (get-all-spr-neighbors (cdr curTrees)
                             (app-gen (orderly-spr (car curTrees)
                                                   tia)
                                      ans)
                             tia)
    ans))

(defun do-spr-search-iteration (seqs curTrees curScore cssl-map matrix)
  (declare (xargs :guard (and (rationalp curScore)
                              (valid-sequences-same-length seqs)
                              (charstate-scorelist-map-p cssl-map (len matrix))
                              (cost-matrixp-nstates matrix (len matrix)))))
  (let ((tia (make-tia (strip-cars-gen seqs))))
    (if (good-taxon-index-halist tia)
        (let ((allNeighbors (get-unique-spr-neighbors curTrees nil
                                                   tia)))
          (get-best-trees allNeighbors curScore nil seqs
                          cssl-map matrix))
      (mv 'Error "Error: Need good tia in do-spr-search-iteration"))))

(defun do-search-with-spr (seqs num-rearrangements curTrees curScore
                                cssl-map matrix)
  (declare (xargs :guard (and (natp num-rearrangements)
                              (rationalp curScore)
                              (valid-sequences-same-length seqs)
                              (charstate-scorelist-map-p cssl-map (len matrix))
                              (cost-matrixp-nstates matrix (len matrix)))
                  :guard-hints (("Goal" :in-theory
                                 (disable perm-implies-subset
                                          MEMBER-GEN-ALISTP-GEN-GIVES-CONSP)))))
  (if (zp num-rearrangements)
      (mv curScore curTrees num-rearrangements)
    (mv-let (newScore newTrees)
            (do-spr-search-iteration seqs
                                     curTrees
                                     curScore
                                     cssl-map
                                     matrix)
            (if (perm newTrees curTrees)
                (mv curScore curTrees num-rearrangements)
              (if (rationalp newScore)
                  (do-search-with-spr seqs
                                      (1- num-rearrangements)
                                      newTrees
                                      newScore
                                      cssl-map
                                      matrix)
                (mv 'Error
                    "Error: Need rational newScore in
                           do-search-with-spr"
                    'Error))))))

(defun spr-search (seqs num-rearrangements cssl-map matrix)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Searches for the maximum parsimony trees using spr rearrangements.~/
;  ~/
;  Arguments:
;    (1) seqs - a set of sequences
;    (2) num-rearrangements - a limit to the number of rearrangements to try
;    (3) cssl-map -  An alist mapping every character state to a
;                    list containing one element (either 0 or nil
;                    for infinity) for each unambiguous state
;    (4) matrix - A mapping of unambiguous character states to
;                 transition costs.

;  Details: Builds a few starting trees, starts from best of these and keeps
;           best trees found at each iteration to search from next."
  (declare (xargs :guard (and (natp num-rearrangements)
                              (valid-sequences-same-length seqs)
                              (charstate-scorelist-map-p cssl-map (len matrix))
                              (cost-matrixp-nstates matrix (len matrix)))))
  (let ((taxa-List (get-taxa-from-sequences seqs)))
    (if (<= 3 (len taxa-list))
        (let ((tree (build-unrooted-binary-tree taxa-List)))
          (if (tree-matches-sequences t tree seqs)
              (let ((score (pscore-tree tree
                                        seqs cssl-map matrix)))
                (if (rationalp score)
                    (do-search-with-spr seqs num-rearrangements
                                        (list tree)
                                        score
                                        cssl-map matrix)
                  (mv 'Error
                    "Error: Need rational score in
                            spr-search"
                    'Error)))
            (mv 'Error
                "Error: Need tree to match seqs in spr-search"
                'Error)))
      (if (tree-matches-sequences t taxa-list seqs)
          (mv (pscore-tree taxa-list seqs cssl-map matrix)
              taxa-list
              num-rearrangements)
        (mv 'Error
            "Error: Need tree to match seqs in spr-search"
            'Error)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun get-unique-tbr-neighbors (curTrees hash tia)
  (declare (xargs :guard (and (good-taxon-index-halist tia)
                              (alistp-gen hash))
                  :guard-hints (("Goal" :in-theory
                                 (disable phylo-tbr)))))
  (if (consp curTrees)
      (get-unique-tbr-neighbors (cdr curTrees)
                                (add-no-dups
                                 (phylo-tbr (car curTrees) tia)
                                 hash)
                                tia)
    (strip-cars-gen hash)))

(defun do-tbr-search-iteration (seqs curTrees curScore cssl-map matrix)
  (declare (xargs :guard (and (rationalp curScore)
                              (valid-sequences-same-length seqs)
                              (charstate-scorelist-map-p cssl-map (len matrix))
                              (cost-matrixp-nstates matrix (len matrix)))))
  (let ((tia (make-tia (strip-cars-gen seqs))))
    (if (good-taxon-index-halist tia)
        (let ((allNeighbors (get-unique-tbr-neighbors curTrees nil
                                                   tia)))
          (get-best-trees allNeighbors curScore nil seqs
                          cssl-map matrix))
      (mv 'Error "Error: Need good tia in do-spr-search-iteration"))))

(defun do-search-with-tbr (seqs num-rearrangements curTrees curScore
                                cssl-map matrix)
  (declare (xargs :guard (and (natp num-rearrangements)
                              (rationalp curScore)
                              (valid-sequences-same-length seqs)
                              (charstate-scorelist-map-p cssl-map (len matrix))
                              (cost-matrixp-nstates matrix (len matrix)))
                 :guard-hints (("Goal" :in-theory
                                 (disable perm-implies-subset
                                          member-gen-alistp-gen-gives-consp
                                          make-spr-pieces-to-do-tbr
                                          get-tbr-pieces)))))
  (if (zp num-rearrangements)
      (mv curScore curTrees num-rearrangements)
    (mv-let (newScore newTrees)
            (do-tbr-search-iteration seqs
                                     curTrees
                                     curScore
                                     cssl-map
                                     matrix)
            (if (perm newTrees curTrees)
                (mv curScore curTrees num-rearrangements)
              (if (rationalp newScore)
                  (do-search-with-tbr seqs
                                      (1- num-rearrangements)
                                      newTrees
                                      newScore
                                      cssl-map
                                      matrix)
                (mv 'Error
                    "Error: Need rational newScore in
                           do-search-with-spr"
                    'Error))))))

(defun tbr-search (seqs num-rearrangements cssl-map matrix)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Searches for the maximum parsimony trees using tbr rearrangements.~/
;  ~/
;  Arguments:
;    (1) seqs - a set of sequences
;    (2) num-rearrangements - a limit to the number of rearrangements to try
;    (3) cssl-map -  An alist mapping every character state to a
;                    list containing one element (either 0 or nil
;                    for infinity) for each unambiguous state
;    (4) matrix - A mapping of unambiguous character states to
;                 transition costs.

;  Details: Builds a few starting trees, starts from best of these and keeps
;           best trees found at each iteration to search from next."
  (declare (xargs :guard (and (natp num-rearrangements)
                              (valid-sequences-same-length seqs)
                              (charstate-scorelist-map-p cssl-map (len matrix))
                              (cost-matrixp-nstates matrix (len matrix)))))
  (let ((taxa-List (get-taxa-from-sequences seqs)))
    (if (<= 3 (len taxa-list))
        (let ((tree (build-unrooted-binary-tree taxa-List)))
          (if (tree-matches-sequences t tree seqs)
              (let ((score (pscore-tree tree
                                        seqs cssl-map matrix)))
                (if (rationalp score)
                    (do-search-with-tbr seqs num-rearrangements
                                        (list tree)
                                        score
                                        cssl-map matrix)
                  (mv 'Error
                    "Error: Need rational score in
                            tbr-search"
                    'Error)))
            (mv 'Error
                "Error: Need tree to match seqs in tbr-search"
                'Error)))
      (if (tree-matches-sequences t taxa-list seqs)
          (mv (pscore-tree taxa-list seqs cssl-map matrix)
              taxa-list
              num-rearrangements)
        (mv 'Error
            "Error: Need tree to match seqs in tbr-search"
            'Error)))))

#||
See ../branch-and-bound/tests/testing.lisp for sequences

(memoize 'pscore-tree)
(mv-let (score trees how-far)
        (time$ (spr-search *angio5* 4 *dna-cssl* *dna-matrix*))
        (mv score (len trees) (no-dups-gen trees) how-far))

(mv-let (score trees how-far)
        (time$ (spr-search *angio4* 6 *dna-cssl* *dna-matrix*))
        (mv score (len trees) (no-dups-gen trees) how-far))

(mv-let (score trees how-far)
        (time$ (tbr-search *angio5* 4 *dna-cssl* *dna-matrix*))
        (mv score (len trees) (no-dups-gen trees) how-far))

(mv-let (score trees how-far)
        (time$ (tbr-search *angio4* 4 *dna-cssl* *dna-matrix*))
        (mv score (len trees) (no-dups-gen trees) how-far))


||#
