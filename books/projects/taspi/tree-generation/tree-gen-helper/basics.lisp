(in-package "ACL2")
(include-book "../../code/build/build-term-guards")
(include-book "../../tree-score/pscores")

(defun build-unrooted-binary-tree-helper (list)
  (declare (xargs :guard (<= 2 (len list))))
  (if (consp list)
      (if (consp (cdr list))
          (if (consp (cddr list))
              (hons (car list)
                    (hist (build-unrooted-binary-tree-helper
                           (cdr list))))
            list)
        "shouldn't happen")
    "also shouldn't happen"))


;; builds a ladder tree
(defun build-unrooted-binary-tree (taxa)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns a binary unrooted ladder tree with taxa names given.~/
;  ~/
;  Arguments:
;     (1) taxa - a list of taxa names

;  "
  (declare (xargs :guard t))
  (if (>= 3 (len taxa))
      taxa
    (hist (car taxa)
          (cadr taxa)
          (build-unrooted-binary-tree-helper (cddr taxa)))))

;; builds a two-ladder tree (each level has two taxa instead of one)
;; orders taxa opposite to basic ladder
(defun build-arbitraryTree-helper (taxa ans)
  (declare (xargs :guard t))
  (if (consp taxa)
      (if (consp (cdr taxa))
          (build-arbitraryTree-helper (cddr taxa)
                                      (hons (hist (car taxa)
                                                  (cadr taxa))
                                            (hist ans)))
        (hons (car taxa) (list ans)))
    ans))

;Returns abitrary rooted binary tree
; reverses taxa for outgroup possibilities
(defun build-arbitraryTree (list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns a binary unrooted two-ladder tree with taxa names given reversed.~/
;  ~/
;  Arguments:
;     (1) taxa - a list of taxa names

;  "
  (declare (xargs :guard t))
  (let ((taxa (taspi-rev list)))
    (build-arbitraryTree-helper (cdr taxa) (car taxa))))

;;doesn't reverse taxa list in order to get a different bound on the score
(defun build-arbitraryTree1 (list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns a binary unrooted two-ladder tree with taxa names given.~/
;  ~/
;  Arguments:
;     (1) taxa - a list of taxa names

;  "
  (declare (xargs :guard t))
  (if (consp list)
      (build-arbitraryTree-helper (cdr list) (car list))
    list))

;Takes a tree part (tree1) to be spliced onto all trees in list
(defun splice (tree1 list ans)
  (declare (xargs :guard t))
  (if (consp list)
      (splice tree1 (cdr list) (hons (hist tree1 (car list)) ans))
    ans))
;(splice '(a (b c)) '((d (e f)) (e (d f))) nil)
;  ->(((A (B C)) (E (D F)))
;     ((A (B C)) (D (E F))))

(defun orderly-splice (piece1 pieces ans tia)
  (declare (xargs :guard (good-taxon-index-halist tia)))
  (if (consp pieces)
      (if (and (subset (mytips piece1)
                       (get-taxa-from-taxon-index tia))
               (member-gen (first-taxon (car pieces))
                           (get-taxa-from-taxon-index tia)))
          (if (consp piece1)
              (if (taspip nil piece1)
                  (orderly-splice piece1 (cdr pieces)
                                  (hons (orderly-cons (car pieces)
                                                (hist piece1) tia)
                                        ans) tia)
                "Error: Need pieces to match tia in orderly-splice")
            (if (taspip nil (list piece1))
                (orderly-splice piece1 (cdr pieces)
                                  (hons (orderly-cons (car pieces)
                                                (hist piece1) tia)
                                        ans) tia)
              "Error: Need second branch pieces to match tia
                      in orderly-splice"))
        "Error: Need third branch pieces to match tia")
    ans))

(defmacro hppend (&rest args) `(hons-append ,@args))

(defun splice2 (x list ans)
  (declare (xargs :guard t))
  (if (consp list)
      (splice2 x (cdr list)
              (hons (hppend x (hist (car list))) ans))
    ans))

(defun orderly-splice2 (piece1 pieces ans tia)
  (declare (xargs :guard (good-taxon-index-halist tia)))
  (if (consp pieces)
      (if (and (subset (mytips piece1)
                       (get-taxa-from-taxon-index tia))
               (member-gen (first-taxon (car pieces))
                           (get-taxa-from-taxon-index tia))
               (taspip nil (list (car pieces)))
               (subset (mytips (car pieces))
                       (get-taxa-from-taxon-index tia)))
          (if (consp piece1)
              (if (taspip nil piece1)
                  (orderly-splice2 piece1 (cdr pieces)
                                  (hons (orderly-append
                                         piece1
                                         (hist (car pieces))
                                          tia)
                                        ans) tia)
                "Error: Need pieces to match tia in orderly-splice")
            (if (taspip nil (list piece1))
                (orderly-splice2 piece1 (cdr pieces)
                                  (hons (orderly-append
                                         (hist piece1)
                                         (hist (car pieces))
                                        tia)
                                        ans) tia)
              "Error: Need second branch pieces to match tia
                      in orderly-splice"))
        "Error: Need third branch pieces to match tia")
    ans))


;Returns list of all possible rooted trees from adding x to
;; rooted binary tree tree
(defun addTaxa-rooted (x tree)
  (declare (xargs :guard t))
  (if (and (consp tree)
           (consp (cdr tree)))
      (hppend (hist (hist x tree))
              (splice (car tree) (addTaxa-rooted x (cadr tree)) nil)
              (splice (cadr tree) (addTaxa-rooted x (car tree)) nil))
    (hist (hist x tree))))

(defun orderly-addTaxa-rooted (x tree tia)
  (declare (xargs :guard (good-taxon-index-halist tia)))
  (if (and (consp tree)
           (consp (cdr tree)))
      (if (and (member-gen (first-taxon x)
                           (get-taxa-from-taxon-index tia))
               (subset (mytips (list tree))
                       (get-taxa-from-taxon-index tia))
               (taspip nil (list tree)))
          (hppend (hist (orderly-cons x (hist tree) tia))
                   (orderly-splice (car tree)
                                   (orderly-addTaxa-rooted
                                    x (cadr tree) tia)
                                   nil tia)
                   (orderly-splice (cadr tree)
                                   (orderly-addTaxa-rooted
                                    x (car tree) tia)
                                   nil tia))
        "Error: Need well-formed taxa and tree in orderly-addTaxa-rooted")
    (if (and (member-gen (first-taxon x)
                           (get-taxa-from-taxon-index tia))
               (subset (mytips (list tree))
                       (get-taxa-from-taxon-index tia))
               (taspip nil (list tree)))
        (hist (orderly-cons x (hist tree) tia))
      "Error: Need well-formed taxa and tree in second
              branch of orderly-addTaxa-rooted")))

(defun addTaxa-unrooted (x tree)
  (declare (xargs :guard (= 3 (len tree))))
  (hppend (splice2 (cdr tree)
                   (addTaxa-rooted x (car tree))
                   nil)
          (splice2 (hist (car tree)
                         (caddr tree))
                   (addTaxa-rooted x (cadr tree))
                   nil)
          (splice2 (hist (car tree) (cadr tree))
                   (addTaxa-rooted x (caddr tree))
                   nil)))

(defun orderly-addTaxa-unrooted (x tree tia)
  (declare (xargs :guard (and (= 3 (len tree))
                              (good-taxon-index-halist tia))))
  (hppend (orderly-splice2 (cdr tree)
                            (orderly-addTaxa-rooted x (car tree) tia)
                            nil tia)
           (orderly-splice2 (hist (car tree)
                                  (caddr tree))
                            (orderly-addTaxa-rooted x (cadr tree) tia)
                            nil tia)
           (orderly-splice2 (hist (car tree) (cadr tree))
                            (orderly-addTaxa-rooted x (caddr tree) tia)
                            nil tia)))

;(addTaxa-rooted 'a '(b (c d)))
;->((A (B (C D)))
;   (B (D (A C)))
;   (B (C (A D)))
;   (B (A (C D)))
;   ((C D) (A B)))


;Of trees in list, input sequences seq,
; return best score and trees achieving that score
(defun get-best-trees (list curScore curTrees seq cssl-map matrix)
  (declare (xargs :guard
                  (and (valid-sequences-same-length seq)
                       (charstate-scorelist-map-p cssl-map (len matrix))
                       (rationalp curScore)
                       (cost-matrixp-nstates matrix (len matrix)))))
  (if (consp list)
      (if (tree-matches-sequences t (car list) seq)
          (let ((newScore (pscore-tree (car list) seq cssl-map matrix)))
            (if (rationalp newScore)
                (if (< newScore curScore)
                    (get-best-trees (cdr list) newScore
                                    (hist (car list)) seq
                                    cssl-map matrix)
                  (if (= newScore curScore)
                      (get-best-trees (cdr list) newScore
                                      (hons (car list) curTrees) seq
                                      cssl-map matrix)
                    (get-best-trees (cdr list) curScore curTrees seq
                                    cssl-map matrix)))
              (mv 'Error "Error: Need rational score in get-best-trees")))
        (mv 'Error "Error: Need trees to match sequences in get-best-trees"))
    (mv curScore curTrees)))
