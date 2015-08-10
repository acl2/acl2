(in-package "ACL2")
(include-book "efficient-pscores")
(include-book "../code/gen-helper/sets")

(defthm alistp-gen-make-sequence-score-lists
  (implies (and (alistp-gen x)
                (alistp-gen name))
           (alistp-gen (make-sequence-score-lists x map name))))

(defun small-integer-transition-rowp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (small-integerp (cdar x))
           (small-integer-transition-rowp (cdr x)))
    t))

(defun small-integer-transition-matrixp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (small-integer-transition-rowp (cdar x))
           (small-integer-transition-matrixp (cdr x)))
    t))

(defun get-transition-cost (char1 char2 transition-matrix)
  (declare (xargs :guard (small-integer-transition-matrixp transition-matrix)))
  (let ((row (assoc-hqual char1 transition-matrix)))
    (if (consp row)
        (let ((val (assoc-hqual char2 row)))
          (if (consp val)
              (cdr val)
            (prog2$ (cw "Error: char2 not in transition-matrix~%")
                    "Error: char2 not in transition-matrix")))
      (prog2$ (cw "Error: char1 not in transition-matrix~%")
              "Error: char1 not in transition-matrix"))))

(defun affine-dist (seq1 seq2 gap-char gap-open-flag ; make flag 1 2 or nil
                         gap-open-cost gap-extend transition-matrix acc)
  (declare (xargs :guard (and (rationalp gap-open-cost)
                              (rationalp gap-extend)
                              (small-integer-transition-matrixp
                               transition-matrix)
                              (equal (len seq1) (len seq2)))))
  (if (not (rationalp acc))
      acc ;;forward the error
    (if (consp seq1)
        (let ((char1 (car seq1))
              (char2 (car seq2)))
          (if (and (equal char1 gap-char)
                   (equal char2 gap-char))
              ;; skip this position
              (affine-dist (cdr seq1) (cdr seq2) gap-char gap-open-flag
                           gap-open-cost gap-extend transition-matrix acc)
            (if (equal char1 gap-char)
                (if (equal gap-open-flag 1)
                    (affine-dist (cdr seq1) (cdr seq2)
                                 gap-char gap-open-flag
                                 gap-open-cost gap-extend
                                 transition-matrix (+ gap-extend acc))
                  (affine-dist (cdr seq1) (cdr seq2)
                               gap-char 1
                               gap-open-cost gap-extend
                               transition-matrix (+ gap-open-cost
                                                    gap-extend
                                                    acc)))
              (if (equal char2 gap-char)
                  (if (equal gap-open-flag 2)
                      (affine-dist (cdr seq1) (cdr seq2)
                                   gap-char gap-open-flag
                                   gap-open-cost gap-extend
                                   transition-matrix
                                   (+ gap-extend acc))
                    (affine-dist (cdr seq1) (cdr seq2)
                                 gap-char 2
                                 gap-open-cost gap-extend
                                 transition-matrix
                                 (+ gap-open-cost
                                    gap-extend acc)))
            ;; two non-gaps, so close if open flag, add cost
                (let ((transcost (get-transition-cost char1 char2
                         transition-matrix)))
                  (if (rationalp transcost)
                      (affine-dist (cdr seq1) (cdr seq2)
                                   gap-char nil gap-open-cost
                                   gap-extend transition-matrix
                                   (+ transcost acc))
                    transcost))))))
    acc)))

(defun make-default-translist (currstate alphabet cost)
  (declare (xargs :guard t))
  (if (atom alphabet)
      nil
    (cons (if (equal (car alphabet) currstate)
              (cons (car alphabet) 0)
            (cons (car alphabet) cost))
          (make-default-translist currstate (cdr alphabet) cost))))

(defun make-default-transmat (alphabet whole cost)
  (declare (xargs :guard t))
  (if (atom alphabet)
      nil
    (cons (cons (car alphabet)
                (make-default-translist (car alphabet) whole cost))
          (make-default-transmat (cdr alphabet) whole cost))))

;;made up of conses cause its not that big and we rip down it.
(defun make-default-transition-matrix (alphabet cost)
  (declare (xargs :guard t))
  (make-default-transmat alphabet alphabet cost))

(defconst *dna-trans-matrix*
  (make-default-transition-matrix '(a c g t) 1))

#||
(affine-dist '(-) '(-) '- nil 3 2 *dna-trans-matrix* 0)

(affine-dist '(- - - G - T T)
             '(- C T - - - T) '- nil 3 2 *dna-trans-matrix* 0)
||#

(mutual-recursion
(defun score-tree-and-sequences-keep-internal
  (tree          ; to be scored
   sequence-score-lists ; map from taxon names to sequence scorelists
   matrix-lists  ; (STRIP-CDRS *dna-matrix*)
   acc           ; mapping from nodes to score-list
   )
  (declare (xargs :measure (make-ord 1 (1+ (acl2-count tree)) 1)
                  :guard (and (small-integer-list-listp matrix-lists)
                              (map-to-small-integer-list-listp
                               sequence-score-lists)
                              (good-len-lists-mapping sequence-score-lists
                                                      matrix-lists))))
  ;; one tree
  (if (atom tree)
      ;; Scorelist based immediately on a sequence
      (let ((leaf (het tree sequence-score-lists)))
        (if (consp leaf)
            (mv (cdr (het tree sequence-score-lists))
                acc) ;; added in recursion
          (prog2$ (cw "Error: Taxon not in sequences~%")
                  (mv "Error: Taxon not in sequences" "Error"))))
    ;; Sum contributions of all children:
    (mv-let (curScores newAcc)
            (score-tree-and-sequences-keep-internal
             (car tree) sequence-score-lists matrix-lists acc)
            (if (and (small-integer-list-listp curScores)
                     (good-len-lists curScores matrix-lists))
                (let ((first-tree-score-list
                       (raise-scorelist-to-parent
                        curScores
                        matrix-lists)))
                  (score-tree-and-sequences-keep-internal-list
                   (cdr tree) sequence-score-lists matrix-lists
                   first-tree-score-list (cons (cons (car tree) curScores)
                                               newAcc)))
              (prog2$ (cw "Error passed on~%")
                      (mv "Error passed on" "Error"))))))

(defun score-tree-and-sequences-keep-internal-list
  (tree sequence-score-lists matrix-lists parentSoFar acc)
  (declare (xargs :measure (make-ord 1 (1+ (acl2-count tree)) 0)
                  :guard (and (small-integer-list-listp matrix-lists)
                              (good-len-lists-mapping sequence-score-lists
                                                      matrix-lists)
                              (map-to-small-integer-list-listp
  sequence-score-lists)
                              (small-integer-list-listp parentSoFar))))
  ;; List of trees
  (if (atom tree)
      (mv parentSoFar acc)
    (mv-let (curScores1 acc1)
            (score-tree-and-sequences-keep-internal (car tree)
                                                    sequence-score-lists
                                                    matrix-lists acc)
            (mv-let (curScores2 acc2)
                    (score-tree-and-sequences-keep-internal-list
                     (cdr tree) sequence-score-lists
                     matrix-lists parentSoFar (cons (cons (car tree)
                                                          curScores1)
                                                    acc1))
                    (if (and (small-integer-list-listp curScores1)
                             (small-integer-list-listp curScores2)
                             (good-len-lists curScores1 matrix-lists))
                        (let ((raised (raise-scorelist-to-parent curScores1 matrix-lists)))
                          (if (matching-lens raised curScores2)
                              (mv (scorelist-sum-list
                                   raised
                                   curScores2) acc2)
                            (prog2$ (cw "Error: lengths don't match~%")
                                    (mv "Error: lengths don't match"
                                        "Error"))))
                      (prog2$ (cw "Error passed on in list branch~%")
                              (mv "Error passed on in list branch" "Error")))))))
)

#||
(let* ((seqs (build-fast-alist-from-alist
             '((1 a c t g a)  ; Taxon . Sequence
               (2 g g g g g)
               (3 a c t g g)
               (4 g g g a a)
               (5 c c t a t)
               (6 g a t a g)) 'seqs))
       (sequence-score-lists (make-sequence-score-lists seqs
                                                        *dna-cssl*
                                                        'seq-score-list)))
  (good-len-lists-mapping sequence-score-lists (strip-cdrs-gen *dna-matrix*)))


(let* ((seqs (build-fast-alist-from-alist
             '((1 a c t g a)  ; Taxon . Sequence
               (2 g g g g g)
               (3 a c t g g)
               (4 g g g a a)
               (5 c c t a t)
               (6 g a t a g)) 'seqs))
       (sequence-score-lists (make-sequence-score-lists seqs
                                                        *dna-cssl*
                                                        'seq-score-list)))
  (mv-let (total pairings)
          (score-tree-and-sequences-keep-internal '((1 2) 3 (4 (5 6))) sequence-score-lists
                                                  (strip-cdrs-gen *dna-matrix*)
                                                  nil)
          (cons (cons '((1 2) 3 (4 (5 6))) total) pairings)))

||#

;; Finds valid position if exists, otherwise returns last position
(defun find-min-pos (x pos curMin curMinPos)
  (declare (xargs :guard (and (rationalp curMin)
                              (integerp pos)
                              (integer-listp curMinPos)
                              (rational-listp x))))
  (if (consp x)
      (if (or (and (not (equal (car x) -1))
                   (not (equal curMin -1))
                   (< (car x) curMin))
              (equal curMin -1))
          (find-min-pos (cdr x) (1+ pos) (car x) (list pos))
        (if (equal (car x) curMin)
            (find-min-pos (cdr x) (1+ pos) (car x) (cons pos curMinPos))
          (find-min-pos (cdr x) (1+ pos) curMin curMinPos)))
    curMinPos))

(defthm integer-listp-find-min-pos
  (implies (and (integer-listp curMinPos)
                (integerp pos))
           (integer-listp (find-min-pos x pos curMin curMinPos))))

(defun sequence-from-parent-scorelist (x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (consp (car x))
          (if (rational-listp (car x))
              ;; We just pick the first character that achieves a minimal score
              ;; Since list is reversed, will usually choose last
              (cons (car (find-min-pos (car x) 0 -1 (list -1)))
                    (sequence-from-parent-scorelist (cdr x)))
            (prog2$ (cw "Error: Need rational-listp in sequence-from-parent-scorelist~%")
                    "Error: Need rational-listp in sequence-from-parent-scorelist"))
        (prog2$ (cw "Error:  Need good parent sequence score-list~%")
                "Error:  Need good parent sequence score-list"))
    nil))

(defun get-child-char (child-scorelist parent-char)
  (declare (xargs :guard (rational-listp child-scorelist)))
  (let ((possible-child-chars (find-min-pos child-scorelist 0 -1
                                            (list -1))))
    (if (intersect possible-child-chars (list parent-char))
        parent-char
      (car possible-child-chars))))

(defun rational-list-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (rational-listp (car x))
           (rational-list-listp (cdr x)))
    t))

(defun get-child-sequence (child-scorelists parent-seq)
  (declare (xargs :guard (and (rational-list-listp child-scorelists)
                              (equal (len child-scorelists)
                                     (len parent-seq)))))
  (if (consp child-scorelists)
      (cons (get-child-char (car child-scorelists) (car parent-seq))
            (get-child-sequence (cdr child-scorelists) (cdr parent-seq)))
    nil))

(defun make-sequence-pairings-each (child parent-seq scorelist-pairings acc)
  (declare (xargs :guard t))
  (if (consp child)
      (let ((child-scorelists (cdr (assoc-hqual (car child) scorelist-pairings))))
        (if (and (rational-list-listp child-scorelists)
                 (equal (len child-scorelists)
                        (len parent-seq)))
            (let ((childSeq (get-child-sequence child-scorelists
                                                parent-seq)))
              (make-sequence-pairings-each (car child) childSeq scorelist-pairings
                                           (make-sequence-pairings-each
                                            (cdr child)
                                            parent-seq scorelist-pairings
                                            (cons
                                             (cons
                                              parent-seq childSeq)
                                             acc))))
          (prog2$ (cw "Error: Need good scorelists in scorelist-pairings~%")
                  "Error: Need good scorelists in scorelist-pairings")))
    acc))


(defun make-sequence-pairings (scorelist-pairings)
  (declare (xargs :guard (alistp-gen scorelist-pairings)))
  (if (consp scorelist-pairings)
      ;; first entry must be tree consed to its scorelist
      (let ((parent-seq (sequence-from-parent-scorelist (cdar
                                                         scorelist-pairings))))
        (if (not (equal parent-seq "Error"))
            (make-sequence-pairings-each (caar scorelist-pairings)
                                         parent-seq
                                         (cdr scorelist-pairings)
                                         nil)
          (prog2$ (cw "Error passed on in make-sequence-pairings~%")
                  "Error passed on in make-sequence-pairings")))
    nil))

#||
(let* ((seqs (build-fast-alist-from-alist
             '((1 a c t)  ; Taxon . Sequence
               (2 g g g)
               (3 a c t)
               (4 g g g)
               (5 c c t)
               (6 g a t)) 'seqs))
       (sequence-score-lists (make-sequence-score-lists seqs
                                                        *dna-cssl*
                                                        'seq-score-list)))
  (mv-let (total pairings)
          (score-tree-and-sequences-keep-internal '(1 3 (5 6)) sequence-score-lists
                                                  (strip-cdrs-gen *dna-matrix*)
                                                  nil)
          (make-sequence-pairings
           (cons (cons '(1 3 (5 6)) total)
                 pairings))))

(let* ((seqs (build-fast-alist-from-alist
             '((1 a c t g a)  ; Taxon . Sequence
               (2 g g g g g)
               (3 a c t g g)
               (4 g g g a a)
               (5 c c t a t)
               (6 g a t a g)) 'seqs))
       (sequence-score-lists (make-sequence-score-lists seqs
                                                        *dna-cssl*
                                                        'seq-score-list)))
  (mv-let (total pairings)
          (score-tree-and-sequences-keep-internal '((1 2) 3 (4 (5 6))) sequence-score-lists
                                                  (strip-cdrs-gen *dna-matrix*)
                                                  nil)
          (make-sequence-pairings
           (cons (cons '((1 2) 3 (4 (5 6))) total)
                 pairings))))
||#

(defun make-sequence-pairings-for-tree (tree sequences cssl-map matrix-lists)
  (declare (xargs :guard (and (alistp-gen sequences)
                              (small-integer-list-listp matrix-lists))))
  (let ((sequence-score-lists (make-sequence-score-lists sequences cssl-map
                                                         'seq-score-list)))
    (if (and (map-to-small-integer-list-listp sequence-score-lists)
             (good-len-lists-mapping sequence-score-lists matrix-lists))
        (mv-let (total pairings)
                (score-tree-and-sequences-keep-internal tree sequence-score-lists
                                                        matrix-lists nil)
                (if (alistp-gen pairings)
                    (make-sequence-pairings (cons (cons tree total)
                                                  pairings))
                  (prog2$ (cw "Error: Bad pairings from score-tree-and-keep-internal~%")
                          "Error: Bad pairings from score-tree-and-keep-internal")))
      (prog2$ (cw "Error: Bad scorelists from make-sequence-score-lists~%")
              "Error: Bad scorelists from make-sequence-score-lists"))))

(defun make-sequence-pairings-for-tree-from-scorelists
  (tree sequence-score-lists matrix-lists)
  (declare (xargs :guard
                  (and
                   (map-to-small-integer-list-listp sequence-score-lists)
                   (small-integer-list-listp matrix-lists)
                   (good-len-lists-mapping sequence-score-lists
                                           matrix-lists))))
  (mv-let (total pairings)
          (score-tree-and-sequences-keep-internal tree sequence-score-lists
                                                  matrix-lists nil)
          (if (alistp-gen pairings)
              (make-sequence-pairings (cons (cons tree total)
                                            pairings))
            "Error: Bad pairings from score-tree-and-keep-internal")))



(defconst *dna-matrix-gap*
  (make-default-cost-matrix '(a c g t -) 1))

(defconst *dna-cssl-gap*
  (build-fast-alist-from-alist
   '((a     0 -1 -1 -1 -1)
     (c    -1  0 -1 -1 -1)
     (g    -1 -1  0 -1 -1)
     (t    -1 -1 -1  0 -1)
     (-    -1 -1 -1 -1  0)
     (r     0 -1  0 -1 -1)
     (y    -1  0 -1  0 -1)
     (m     0  0 -1 -1 -1)
     (k    -1 -1  0  0 -1)
     (s    -1  0  0 -1 -1)
     (w     0 -1 -1  0 -1)
     (h     0  0 -1  0 -1)
     (b    -1  0  0  0 -1)
     (v     0  0  0 -1 -1)
     (d     0 -1  0  0 -1)
     (n     0  0  0  0 -1)
     (?     0  0  0  0 -1))
   'dna-cssl-gap))

#||
(make-sequence-pairings-for-tree '(1 2 3) (build-fast-alist-from-alist
             '((1 a - c - t g - a)  ; Taxon . Sequence
               (2 g - g - g - g g)
               (3 a - c t g - g -)
               (4 g g g a a)
               (5 c c t a t)
               (6 g a t a g)) 'seqs) *dna-cssl-gap*
               (strip-cdrs-gen *dna-matrix-gap*))
||#

(defun score-pairings (type pairings args acc)
  (declare (xargs :guard (rationalp acc)))
  (cond ((equal type 'affine)
         (if (consp pairings)
             (if (and (consp (car pairings))
                      (equal (len (caar pairings))
                             (len (cdar pairings))))
                 (if (equal (len args) 4)
                     (let ((gap-char (car args))
                           (gap-cost (cadr args))
                           (gap-extend-cost (caddr args))
                           (transition-matrix (car (cdddr args))))
                       (if (and (rationalp gap-cost)
                                (rationalp gap-extend-cost)
                                (small-integer-transition-matrixp
                                 transition-matrix))
                           (let ((pair-score (affine-dist (caar pairings)
                                                          (cdar pairings)
                                                          gap-char nil gap-cost
                                                          gap-extend-cost
                                                          transition-matrix
                                                          0)))
                             (if (rationalp pair-score)
                                 (score-pairings
                                  type (cdr pairings) args
                                  (+ pair-score
                                     acc))
                               pair-score)) ;; pass error up
                         "Error: Bad arguments in call to affine"))
                   "Error: Wrong arguments in call to affine")
               "Error: Need same length pairings")
           acc))
        (t "Error: Invalid score type")))

;; (defthm small-integer-transition-rowp-gives-alistp-cdr
;;   (implies (and (consp x)
;;                 (small-integer-transition-rowp x))
;;            (alistp-gen (cdr x))))

;; (defthm small-integer-transition-matrixp-gives-alistp-cdar
;;   (implies (and (consp x)
;;                 (small-integer-transition-matrixp x))
;;            (alistp-gen (cdar x))))

(defun get-matrix-lists-from-trans (x)
  (declare (xargs :guard (small-integer-transition-matrixp x)))
  (if (consp x)
      (cons (strip-cdrs-gen (cdar x))
            (get-matrix-lists-from-trans (cdr x)))
    nil))

(defthm transition-matrixp-gives-alistp-gen
   (implies (small-integer-transition-rowp x)
            (small-integer-listp (strip-cdrs-gen x))))

(defthm sm-int-trans-matrix-gives-sm-int-list-listp-get-matrx-lists
  (implies (small-integer-transition-matrixp trans)
           (small-integer-list-listp
            (get-matrix-lists-from-trans trans))))

(defun numberfy-helper (x n)
  (declare (xargs :guard (and (alistp-gen x)
                              (integerp n))))
  (if (consp x)
      (cons (cons n (cdar x))
            (numberfy-helper (cdr x) (1+ n)))
    nil))

(defun numberfy (x n)
  (declare (xargs :guard (and (integerp n)
                              (small-integer-transition-matrixp x))))
  (if (consp x)
      (cons (cons n (numberfy-helper (cdar x) 0))
            (numberfy (cdr x) (1+ n)))
    nil))


(defun update-sequence-keys (sequences anc-tree-mapping tree)
  (declare (xargs :guard (and (alistp-gen anc-tree-mapping)
                              (alistp-gen sequences))))
  (if (consp anc-tree-mapping)
      (update-sequence-keys
       (if (equal (cdar anc-tree-mapping)
                  tree)
           sequences
         (hut (cdar anc-tree-mapping)
              (cdr (het (caar anc-tree-mapping)
                        sequences))
              sequences))
       (cdr anc-tree-mapping)
       (if (equal (cdar anc-tree-mapping) tree)
           (cons tree (cdr (het (caar anc-tree-mapping) sequences)))
         tree))
    (if (consp tree)
        (hut (car tree) (cdr tree) sequences)
      sequences)))

#||
(update-sequence-keys (build-fast-alist-from-alist
                         '((1 a - c t g a - -)  ; Taxon . Sequence
                           (2 g - g - g - g g)
                           (3 a - c t g - g -)
                           (4 g g - - g a - a)
                           (p c - c t - a - t)
                           (q g a - - - a g -)) 'seqs)
                      '((p . 5) (q . (1 (2 3) 4)))
                      '(1 (2 3) 4))
||#

(defthm alistp-gen-through-hons-revappend
  (implies (and (alistp-gen y)
                (alistp-gen x))
           (alistp-gen (hons-revappend x y))))

(defthm alistp-gen-through-revappend
  (implies (and (alistp-gen y)
                (alistp-gen x))
           (alistp-gen (revappend x y))))

(defthm alistp-gen-through-hons-reverse
  (implies (alistp-gen x)
           (alistp-gen (hons-reverse x))))

(defthm alistp-gen-update-sequence-keys
  (implies (and (alistp-gen x)
                (alistp-gen y))
           (alistp-gen (update-sequence-keys x y tree))))

(defun score-tree-with-affine (tree sequences gap-char gap-cost gap-extend-cost
                                    cssl-map transition-matrix anc-mappings)
  (declare (xargs :guard (and (alistp-gen sequences)
                              (rationalp gap-cost)
                              (rationalp gap-extend-cost)
                              (small-integer-transition-matrixp
                               transition-matrix)
                              (alistp-gen anc-mappings))))
  (if (not (consp anc-mappings))
      (let ((pairings (make-sequence-pairings-for-tree tree sequences
                                                       cssl-map
                                                       (get-matrix-lists-from-trans
                                                        transition-matrix))))
        (if (consp pairings)
            (score-pairings 'affine pairings
                            (list gap-char
                                  gap-cost
                                  gap-extend-cost
                                  (numberfy transition-matrix 0))
                            0) ;;acc
          pairings)) ;; effectively passes on errors
    ;;compute from given mappings
    (let* ((new-seqs (hons-reverse (update-sequence-keys sequences anc-mappings tree)))
          (pairings (make-sequence-pairings (make-sequence-score-lists
                                             new-seqs cssl-map
                                             'seq-score-list))))
      (if (consp pairings)
            (score-pairings 'affine pairings
                            (list gap-char
                                  gap-cost
                                  gap-extend-cost
                                  (numberfy transition-matrix 0))
                            0) ;;acc
          pairings))))

(defthm map-to-small-integer-list-listp-gives-alistp-gen
  (implies (map-to-small-integer-list-listp x)
           (alistp-gen x)))

(defun score-tree-with-affine-score-lists (tree score-lists gap-char gap-cost gap-extend-cost
                                                transition-matrix anc-mappings)
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

                              (alistp-gen anc-mappings))))
  (if (not (consp anc-mappings))
      (let ((pairings (make-sequence-pairings-for-tree-from-scorelists
                       tree score-lists
                       (get-matrix-lists-from-trans
                        transition-matrix))))
        (if (consp pairings)
            (score-pairings 'affine pairings
                            (list gap-char
                                  gap-cost
                                  gap-extend-cost
                                  (numberfy transition-matrix 0))
                            0) ;;acc
          pairings)) ;; effectively passes on errors
    ;;compute from given mappings
    (let* ((new-seq-score-lists (update-sequence-keys score-lists anc-mappings tree))
          (pairings (make-sequence-pairings new-seq-score-lists)))
      (if (consp pairings)
            (score-pairings 'affine pairings
                            (list gap-char
                                  gap-cost
                                  gap-extend-cost
                                  (numberfy transition-matrix 0))
                            0) ;;acc
          pairings))))

(defun score-trees-with-affine (trees-and-anc-mapping sequences gap-char
                                                      gap-cost gap-extend-cost
                                                      cssl-map
                                                      transition-matrix)
  (declare (xargs :guard (and (alistp-gen sequences)
                              (rationalp gap-cost)
                              (rationalp gap-extend-cost)
                              (small-integer-transition-matrixp
                               transition-matrix))))
  (if (consp trees-and-anc-mapping)
      (if (and (consp (car trees-and-anc-mapping))
               (alistp-gen (cdar trees-and-anc-mapping)))
          (cons (hons (score-tree-with-affine
                       (caar trees-and-anc-mapping)
                       sequences gap-char gap-cost gap-extend-cost
                       cssl-map transition-matrix
                       (cdar trees-and-anc-mapping))
                      (caar trees-and-anc-mapping))
                (score-trees-with-affine
                 (cdr trees-and-anc-mapping)
                 sequences gap-char gap-cost gap-extend-cost
                 cssl-map transition-matrix))
        "Error: Bad trees-and-anc-mapping in score-trees-with-affine")
    nil))

(defun score-trees-with-affine-score-lists (trees-and-anc-mapping score-lists gap-char
                                                      gap-cost gap-extend-cost
                                                      transition-matrix)
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
                              )))
  (if (consp trees-and-anc-mapping)
      (if (and (consp (car trees-and-anc-mapping))
               (alistp-gen (cdar trees-and-anc-mapping)))
          (cons (hons (score-tree-with-affine-score-lists
                       (caar trees-and-anc-mapping)
                       score-lists gap-char gap-cost gap-extend-cost
                       transition-matrix (cdar trees-and-anc-mapping))
                      (caar trees-and-anc-mapping))
                (score-trees-with-affine-score-lists
                 (cdr trees-and-anc-mapping)
                 score-lists gap-char gap-cost gap-extend-cost
                 transition-matrix))
        "Error: Bad trees-and-anc-mapping in score-trees-with-affine")
    nil))

(defconst *dna-trans-matrix-gap*
  (make-default-transition-matrix '(a c t g -) 1))

(defun get-range (x low high tree-achieving-low)
  (declare (xargs :guard (and (rationalp low)
                              (rationalp high)
                              (alistp-gen x))))
  (if (consp x)
      (if (rationalp (caar x))
          (if (< (caar x) low)
              (get-range (cdr x) (caar x) high (cdar x))
            (if (> (caar x) high)
                (get-range (cdr x) low (caar x) tree-achieving-low)
              (get-range (cdr x) low high tree-achieving-low)))
        (get-range (cdr x) low high tree-achieving-low))
    (mv low high tree-achieving-low)))


#||
(score-tree-with-affine '((1 2) 3 (4 (5 6)))
                        (build-fast-alist-from-alist
                         '((1 a - c t g a - -)  ; Taxon . Sequence
                           (2 g - g - g - g g)
                           (3 a - c t g - g -)
                           (4 g g - - g a - a)
                           (5 c - c t - a - t)
                           (6 g a - t - a g -)) 'seqs)
                        4 ;; 4th position in trans-matrix
                        3 1
                        *dna-cssl-gap*
                        *dna-trans-matrix-gap* nil)

(score-tree-with-affine '((1 2) 3 (4 (5 6)))
                        (build-fast-alist-from-alist
                         '((1 a - c t g a - -)  ; Taxon . Sequence
                           (2 g - g - g - g g)
                           (3 a - c t g - g -)
                           (4 g g - - g a - a)
                           (5 c - c t - a - t)
                           (6 g a - - - a g -)) 'seqs)
                        4 1 1
                        *dna-cssl-gap*
                        *dna-trans-matrix-gap* nil)

(score-tree-with-affine '(1 2)
                        (build-fast-alist-from-alist
                         '((1 a - c t g a - -)  ; Taxon . Sequence
                           (2 g - g - g - g g)
                           (3 a - c t g - g -)
                           (4 g g - - g a - a)
                           (5 c - c t - a - t)
                           (6 g a - - - a g -)) 'seqs)
                         4 1 1
                        *dna-cssl-gap*
                        *dna-trans-matrix-gap* nil)

||#

