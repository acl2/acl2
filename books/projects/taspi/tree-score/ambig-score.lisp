(in-package "ACL2")

(include-book "min-length")

(defun reassign-ambig-help (actual-seq pars-seq-scorelist cssl-map)
  (declare (xargs :guard (and (equal (len actual-seq)
                                     (len pars-seq-scorelist))
                              (alistp-gen cssl-map)
                              (consp cssl-map))))
  (if (consp actual-seq)
      (if (equal (car actual-seq) 'N)
          (cons (if (not (equal (car pars-seq-scorelist)
                                (cdr (assoc-hqual '-
                                                  cssl-map))))
                    (car pars-seq-scorelist) ; not a gap, return parsimony ans
                  (cdar cssl-map)) ; otherwise return A
                (reassign-ambig-help (cdr actual-seq)
                                     (cdr pars-seq-scorelist)
                                     cssl-map))
        (cons (cdr (assoc-hqual (car actual-seq) cssl-map))
              (reassign-ambig-help (cdr actual-seq)
                                   (cdr pars-seq-scorelist)
                                   cssl-map)))
    nil))

;; return trees mapped to sequences with ambig characters removed
(defun get-key-matching-val (val mapping)
  (declare (xargs :guard (alistp-gen mapping)))
  (if (consp mapping)
      (if (equal (cdar mapping) val)
          (caar mapping)
        (get-key-matching-val val (cdr mapping)))
    nil))

(defun reassign-ambig2 (pars-seqs-scorelist actual-seq cssl-map anc-mappings)
  (declare (xargs :guard (and (alistp-gen pars-seqs-scorelist)
                              (alistp-gen actual-seq)
                              (alistp-gen anc-mappings)
                              (alistp-gen cssl-map)
                              (consp cssl-map))))
  (if (consp pars-seqs-scorelist)
      (let* ((poss-internal-name (get-key-matching-val
                                  (caar pars-seqs-scorelist)
                                  anc-mappings))
             (internal-name (if poss-internal-name
                                poss-internal-name
                              (caar pars-seqs-scorelist)))
             (one-actual-seq (cdr (assoc-hqual internal-name actual-seq))))
        (if (equal (len (cdar pars-seqs-scorelist))
                   (len one-actual-seq))
            (cons (cons (caar pars-seqs-scorelist)
                        (reassign-ambig-help one-actual-seq
                                             (cdar pars-seqs-scorelist)
                                             cssl-map))
                  (reassign-ambig2 (cdr pars-seqs-scorelist) actual-seq
                                   cssl-map anc-mappings))
          "Error in reassign-ambig2"))
    nil))



(defun make-sequence-pairings-for-tree-from-scorelists-and-actual
  (tree sequence-score-lists sequences matrix-lists cssl-map anc-mapping)
  (declare (xargs :guard
                  (and
                   (map-to-small-integer-list-listp sequence-score-lists)
                   (small-integer-list-listp matrix-lists)
                   (good-len-lists-mapping sequence-score-lists
                                           matrix-lists)
                   (alistp-gen sequences)
                   (alistp-gen anc-mapping)
                   (alistp-gen cssl-map)
                   (consp cssl-map))))
  (mv-let (total pairings)
          (score-tree-and-sequences-keep-internal tree sequence-score-lists
                                                  matrix-lists nil)
          (if (alistp-gen pairings)
              (let ((reassigned-pairings
                     (reassign-ambig2 (cons
                                      (cons tree total)
                                      pairings)
                                     sequences cssl-map anc-mapping)))
                (if (alistp-gen reassigned-pairings)
                    (make-sequence-pairings reassigned-pairings)
                  "Error: Need good pairings from reassign-ambig"))
            "Error: Bad pairings from score-tree-and-keep-internal")))

(defun score-tree-with-affine-score-lists-ambig
  (tree score-lists sequences gap-char gap-cost gap-extend-cost
        transition-matrix anc-mappings cssl-map)
  (declare (xargs :guard (and (small-integer-transition-matrixp
                               transition-matrix)
                              (map-to-small-integer-list-listp score-lists)
                              (small-integer-list-listp (get-matrix-lists-from-trans
                                                         transition-matrix))
                              (good-len-lists-mapping score-lists
                                                      (get-matrix-lists-from-trans
                                                       transition-matrix))
                              (rationalp gap-cost)
                              (rationalp gap-extend-cost)

                              (alistp-gen anc-mappings)
                              (alistp-gen sequences)
                              (alistp-gen cssl-map)
                              (consp cssl-map))))
  (if (consp anc-mappings)
      (let ((pairings
              (make-sequence-pairings-for-tree-from-scorelists-and-actual
               tree score-lists
               sequences
               (get-matrix-lists-from-trans
                transition-matrix) cssl-map anc-mappings)))
        (if (consp pairings)
            (score-pairings 'affine pairings
                            (list gap-char
                                  gap-cost
                                  gap-extend-cost
                                  (numberfy transition-matrix 0))
                            0) ;;acc
          pairings)) ;; effectively passes on errors
    (score-tree-with-affine-score-lists
     tree score-lists gap-char gap-cost gap-extend-cost transition-matrix
     anc-mappings)))