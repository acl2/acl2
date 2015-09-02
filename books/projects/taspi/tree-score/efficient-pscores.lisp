(in-package "ACL2")
(include-book "../code/gen-helper/extra")
(include-book "efficient-pscores-help")

(defun min-list (list curMin)
  (declare (xargs :guard (and (small-integer-listp list)
                              (small-integerp curMin))))
  (if (atom list)
      curMin
    (min-list (cdr list)
              (min-nil-inf (car list) curMin))))

(defun sum-list (l1 l2)
  (declare (xargs :guard (and (small-integer-listp l1)
                              (small-integer-listp l2)
                              (equal (len l1) (len l2)))))
  (if (atom l1)
      nil
    (hons (plus-nil-inf (car l1) (car l2))
          (sum-list (cdr l1) (cdr l2)))))

;; So we can memoize only top level calls easily
(defun sum-list-top (l1 l2)
  (declare (xargs :guard (and (small-integer-listp l1)
                              (small-integer-listp l2)
                              (equal (len l1) (len l2)))))
  (sum-list l1 l2))

(defun scorelist-sum-list (l1 l2)
  (declare (xargs :guard (and (matching-lens l1 l2)
                              (small-integer-list-listp l1)
                              (small-integer-list-listp l2))))
  (if (atom l1)
      nil
    (cons (sum-list-top (car l1) (car l2))
          (scorelist-sum-list (cdr l1) (cdr l2)))))

(defthmd small-integerp-min-list
  (implies (and (small-integer-listp list)
                (small-integerp curMin))
           (small-integerp (min-list list curMin))))

(defun sum-minima-helper (scorelist curSum)
  (declare (xargs :guard (and (small-integerp curSum)
                              (small-integer-list-listp scorelist))
                  :guard-hints (("Subgoal 5.3'''" :use (:instance
                                                      small-integerp-min-list
                                                      (list scorelist1)
                                                      (curMin -1)))
                                ("Subgoal 4" :use (:instance
                                                      small-integerp-min-list
                                                      (list (car scorelist))
                                                      (curMin -1)))
                                ("Subgoal 2.3'''" :use (:instance
                                                      small-integerp-min-list
                                                      (list scorelist1)
                                                      (curMin -1)))
                                ("Subgoal 1" :use (:instance
                                                      small-integerp-min-list
                                                      (list (car scorelist))
                                                      (curMin -1))))))
  (if (atom scorelist)
      curSum
    (sum-minima-helper (cdr scorelist)
                (plus-nil-inf (min-list (car scorelist) -1)
                              curSum))))

(defun sum-minima (scorelist)
  (declare (xargs :guard (small-integer-list-listp scorelist)))
  (sum-minima-helper scorelist 0))

(defun make-leaf-score-list (seq cssl-map)
  (declare (xargs :guard t))
  (if (atom seq)
      nil
    (let ((scoreList (het (car seq) cssl-map)))
      (cons (cdr scoreList)
            (make-leaf-score-list (cdr seq) cssl-map)))))

(defun find-smallest-addition (curList translist)
  (declare (xargs :guard (and (small-integer-listp curList)
                              (small-integer-listp translist)
                              (equal (len curList)
                                     (len translist)))
                  :verify-guards nil))
  (if (atom curList)
      -1 ;; for infinity
    (min-nil-inf (plus-nil-inf (car curList) (car translist))
                 (find-smallest-addition (cdr curList) (cdr translist)))))

(defthm find-smallest-addition-small-integerp
  (implies (and (small-integer-listp x)
                (small-integer-listp y)
                (equal (len x) (len y)))
           (small-integerp (find-smallest-addition x y))))

(local (defthm len-zero-not-consp
         (implies (equal (len x) 0)
                  (not (consp x)))))

(verify-guards find-smallest-addition
               :hints (("Subgoal 7" :in-theory
                        (disable find-smallest-addition-small-integerp)
                        :use (:instance find-smallest-addition-small-integerp
                                 (x (cdr curlist))
                                 (y (cdr translist))))
                       ("Subgoal 2" :in-theory
                        (disable find-smallest-addition-small-integerp)
                        :use (:instance find-smallest-addition-small-integerp
                                 (x (cdr curlist))
                                 (y (cdr translist))))))

(defun raise-score-to-parent (child matrix-lists)
  (declare (xargs :guard (and (small-integer-listp child)
                              (small-integer-list-listp matrix-lists)
                              (good-len-list (len child) matrix-lists))))
  (if (atom matrix-lists)
      nil
    (hons (find-smallest-addition child (car matrix-lists))
          (raise-score-to-parent child (cdr matrix-lists)))))

(defun raise-scorelist-to-parent (child matrix-lists)
  (declare (xargs :guard (and (small-integer-list-listp child)
                              (small-integer-list-listp matrix-lists)
                              (good-len-lists child matrix-lists))))
  (if (atom child)
      nil
    (cons (raise-score-to-parent (car child) matrix-lists)
          (raise-scorelist-to-parent (cdr child) matrix-lists))))

(defthm small-integer-listp-through-raise-score
  (implies (and (small-integer-listp x)
                (small-integer-list-listp y)
                (good-len-list (len x) y))
           (small-integer-listp (raise-score-to-parent x y))))

(defthm small-integer-list-listp-through-raise-scorelist
  (implies (and (small-integer-list-listp x)
                (small-integer-list-listp y)
                (good-len-lists x y))
           (small-integer-list-listp
            (raise-scorelist-to-parent x y))))

(mutual-recursion
(defun score-tree-and-sequences
  (tree          ; to be scored
   sequence-score-lists ; map from taxon names to sequence scorelists
   matrix-lists  ; (STRIP-CDRS *dna-matrix*)
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
            (cdr (het tree sequence-score-lists))
          "Error: Taxon not in sequences"))
    ;; Sum contributions of all children:
    (let ((curScores (score-tree-and-sequences
                      (car tree) sequence-score-lists matrix-lists)))
      (if (and (small-integer-list-listp curScores)
               (good-len-lists curScores matrix-lists))
          (let ((first-tree-score-list
                 (raise-scorelist-to-parent
                  curScores
                  matrix-lists)))
            (score-tree-and-sequences-list
             (cdr tree) sequence-score-lists matrix-lists
             first-tree-score-list))
        "Error passed on"))))

(defun score-tree-and-sequences-list
  (tree sequence-score-lists matrix-lists parentSoFar)
  (declare (xargs :measure (make-ord 1 (1+ (acl2-count tree)) 0)
                  :guard (and (small-integer-list-listp matrix-lists)
                              (good-len-lists-mapping sequence-score-lists
                                                      matrix-lists)
                              (map-to-small-integer-list-listp
                               sequence-score-lists)
                              (small-integer-list-listp parentSoFar))))
  ;; List of trees
  (if (atom tree)
      parentSoFar
    (let ((curScores1 (score-tree-and-sequences (car tree)
                                                sequence-score-lists
                                                matrix-lists))
          (curScores2 (score-tree-and-sequences-list
                       (cdr tree) sequence-score-lists
                       matrix-lists parentSoFar)))
      (if (and (small-integer-list-listp curScores1)
               (small-integer-list-listp curScores2)
               (good-len-lists curScores1 matrix-lists))
          (let ((raised (raise-scorelist-to-parent curScores1 matrix-lists)))
            (if (matching-lens raised curScores2)
                (scorelist-sum-list
                 raised
                 curScores2)
              "Error: lengths don't match"))
        "Error passed on in list branch"))))
)

(defun make-sequence-score-lists (sequences cssl-map alist)
  (declare (xargs :guard (alistp-gen sequences)))
  (if (atom sequences)
      alist
    (make-sequence-score-lists (cdr sequences) cssl-map
                               (hut (caar sequences)
                                    (make-leaf-score-list (cdar sequences) cssl-map)
                                    alist))))

(defun pscore-tree-helper (tree sequence-score-lists matrix-lists)
  (declare (xargs :guard (and (map-to-small-integer-list-listp
                               sequence-score-lists)
                              (good-len-lists-mapping sequence-score-lists
                                                      matrix-lists)
                              (small-integer-list-listp matrix-lists))))
  (let ((scores (score-tree-and-sequences tree sequence-score-lists matrix-lists)))
    (if (small-integer-list-listp scores)
        (sum-minima scores)
      "Error: Needed good scores from score-tree-and-sequences")))

(defun pscore-tree (tree sequences cssl-map matrix)
  (declare (xargs :guard (and (alistp-gen sequences)
                              (alistp-gen matrix))))
  (let* ((sequence-score-lists (make-sequence-score-lists sequences cssl-map
                                                          'make-sequence-score-lists))
         (matrix-lists (strip-cdrs-gen matrix)))
    (if (and (map-to-small-integer-list-listp sequence-score-lists)
             (good-len-lists-mapping sequence-score-lists
                                     matrix-lists)
             (small-integer-list-listp matrix-lists))
        (pscore-tree-helper tree sequence-score-lists matrix-lists)
      "Error: Need good sequences and matrix in pscore-tree")))

(defun pscore-trees-helper (trees sequence-score-lists matrix-lists)
  (declare (xargs :guard (and (map-to-small-integer-list-listp
                               sequence-score-lists)
                              (good-len-lists-mapping sequence-score-lists
                                                      matrix-lists)
                              (small-integer-list-listp matrix-lists))))
  (if (atom trees)
      nil
    (cons (pscore-tree-helper  (car trees) sequence-score-lists matrix-lists)
          (pscore-trees-helper (cdr trees) sequence-score-lists matrix-lists))))

(defun pscore-trees (trees sequences cssl-map matrix)
  (declare (xargs :guard (and (alistp-gen sequences)
                              (alistp-gen matrix))))
  (let* ((sequence-score-lists (make-sequence-score-lists sequences cssl-map
                                                          'make-sequence-score-lists))
         (matrix-lists (strip-cdrs-gen matrix)))
    (if (and (map-to-small-integer-list-listp sequence-score-lists)
             (good-len-lists-mapping sequence-score-lists
                                     matrix-lists)
             (small-integer-list-listp matrix-lists))
        (pscore-trees-helper trees sequence-score-lists matrix-lists)
      "Error: Need good sequences and matrix in pscore-trees")))


;; Initialization

(defun make-default-costlist (currstate alphabet cost)
  (declare (xargs :guard t))
  (if (atom alphabet)
      nil
    ;;hons up tuples
    (hons (if (equal (car alphabet) currstate) 0 cost)
          (make-default-costlist currstate (cdr alphabet) cost))))

(defun make-default-cmat (alphabet whole cost)
  (declare (xargs :guard t))
  (if (atom alphabet)
      nil
    (cons (cons (car alphabet)
                (make-default-costlist (car alphabet) whole cost))
          (make-default-cmat (cdr alphabet) whole cost))))

;;made up of conses cause its not that big and we rip down it.
(defun make-default-cost-matrix (alphabet cost)
  (declare (xargs :guard t))
  (make-default-cmat alphabet alphabet cost))

(defconst *dna-matrix*
  (make-default-cost-matrix '(a c g t) 1))

(defconst *dna-cssl*
  (build-fast-alist-from-alist
   '((a     0 -1 -1 -1)
     (c    -1  0 -1 -1)
     (g    -1 -1  0 -1)
     (t    -1 -1 -1  0)
     (-     0  0  0  0)
     (r     0 -1  0 -1)
     (y    -1  0 -1  0)
     (m     0  0 -1 -1)
     (k    -1 -1  0  0)
     (s    -1  0  0 -1)
     (w     0 -1 -1  0)
     (h     0  0 -1  0)
     (b    -1  0  0  0)
     (v     0  0  0 -1)
     (d     0 -1  0  0)
     (n     0  0  0  0)
     (?     0  0  0  0))
   'dna-cssl))
