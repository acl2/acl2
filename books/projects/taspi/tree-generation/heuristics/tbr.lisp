(in-package "ACL2")

(include-book "spr")

;to do TBR we're going to use spr-helper, where we mutate the piece
; to be attached according to various connection points
; first get-pieces, then attach each piece in every way

;get-pieces returns alist of branched piece to attach and unrooted
; tree
; so, we need to take each branched piece, and rebranch at all
; possible places.
; what does this look like??

;; x is at most binary, cause its a piece to attach
(defun get-tbr-pieces (flg x rest tia)
  (declare (xargs :guard (good-taxon-index-halist tia)))
  (if (equal flg 'top)
      (if (and (consp x)
               (consp (cdr x))
               (atom (cddr x)))
          (hppend (if (consp (car x))
                      (if (and (consp (cdar x))
                               (subset (mytips (cdr x))
                                       (get-taxa-from-taxon-index
                                        tia))
                               (member-gen (first-taxon (cadar x))
                                           (get-taxa-from-taxon-index
                                            tia))
                               (member-gen (first-taxon (caar x))
                                           (get-taxa-from-taxon-index
                                            tia))
                               (taspip nil (cdr x)))
                          (hppend
                           (get-tbr-pieces 'inside (caar x)
                                           (orderly-cons (cadar x)
                                                         (cdr x)
                                                         tia)
                                           tia)
                           (get-tbr-pieces 'inside (cadar x)
                                           (orderly-cons (caar x)
                                                         (cdr x)
                                                         tia)
                                           tia))
                        "Error: Need binary tree or pieces matching
                                in get-tbr-pieces")
                    (hist x))
                   (if (consp (cdr x))
                       (if (and (consp (cadr x))
                                (subset (mytips (cdadr x))
                                        (get-taxa-from-taxon-index
                                         tia))
                                (subset (mytips (list (caadr x)))
                                        (get-taxa-from-taxon-index
                                         tia))
                                (member-gen (first-taxon (car x))
                                            (get-taxa-from-taxon-index
                                             tia))
                                (taspip nil (cdadr x))
                                (taspip nil (list (caadr x))))
                           (hppend
                            (get-tbr-pieces 'inside (caadr x)
                                            (orderly-cons (car x)
                                                          (cdadr x) tia)
                                            tia)
                            (if (consp (cdadr x))
                                (get-tbr-pieces 'inside (car (cdadr x))
                                                (orderly-cons (car x)
                                                              (hist
                                                               (caadr x))
                                                              tia)
                                                tia)
                              "Error: Need binary tree 1 in get-tbr-pieces"))
                         (hist x))
                     "Error: Need binary tree in second branch get-tbr-pieces")
                  (if (and (consp (car x))
                           (consp (cadr x)))
                      (hist x)
                    nil))
        (hist x)) ;this is the only piece
    ;flg is not top, rest is part of a tree
    (if (consp x)
        (hppend (if (consp (car x))
                     (if (and (consp (cdar x))
                              (consp (cdr x))
                              (member-gen (first-taxon (cadr x))
                                          (get-taxa-from-taxon-index tia))
                              (member-gen (first-taxon (cadar x))
                                          (get-taxa-from-taxon-index tia))
                              (member-gen (first-taxon (car x))
                                          (get-taxa-from-taxon-index tia))
                              (member-gen (first-taxon (caar x))
                                          (get-taxa-from-taxon-index tia))
                              (subset (mytips (list rest))
                                      (get-taxa-from-taxon-index tia))
                              (taspip nil (list rest))
                              (subset (mytips (list (orderly-cons
                                                        (cadr x)
                                                        (list rest)
                                                        tia)))
                                      (get-taxa-from-taxon-index tia))
                              (taspip nil (list (orderly-cons
                                                          (cadr x)
                                                          (list rest)
                                                          tia)))
                                         )
                         (hppend (get-tbr-pieces
                                   'inside (caar x)
                                   (orderly-cons (cadar x)
                                                 (hist (orderly-cons
                                                        (cadr x)
                                                        (hist rest)
                                                        tia))
                                                 tia)
                                   tia)
                                  (get-tbr-pieces 'inside (cadar x)
                                                  (orderly-cons
                                                   (caar x)
                                                   (hist (orderly-cons
                                                          (cadr x)
                                                          (hist rest)
                                                          tia))
                                                   tia)
                                                  tia)
                                  (hist (orderly-cons (car x)
                                                      (hist (orderly-cons
                                                             (cadr x)
                                                             (hist rest)
                                                             tia))
                                                      tia)))
                       "Error: Need binary tree in third branch
                               get-tbr-pieces")
                   (if (and (consp (cdr x))
                            (subset (mytips (list rest))
                                    (get-taxa-from-taxon-index tia))
                            (taspip nil (list rest))
                            (member-gen (first-taxon (cadr x))
                                        (get-taxa-from-taxon-index tia))
                            (subset (mytips (hist (orderly-cons (cadr x)
                                                                       (hist rest)
                                                                       tia)))
                                    (get-taxa-from-taxon-index tia))
                            (taspip nil (hist (orderly-cons (cadr x)
                                                                       (hist rest)
                                                                       tia)))
                            (member-gen (first-taxon (car x))
                                        (get-taxa-from-taxon-index tia)))
                       (hist (orderly-cons (car x) (hist (orderly-cons (cadr x)
                                                                       (hist rest)
                                                                       tia))
                                           tia))
                     "Error: Need binary tree in 3rd branch get-tbr-pieces"))
                 (if (consp (cdr x))
                     (if (consp (cadr x))
                         (if (and (consp (cdadr x))
                                  (member-gen (first-taxon (car (cdadr x)))
                                              (get-taxa-from-taxon-index tia))
                                  (member-gen (first-taxon (caadr x))
                                              (get-taxa-from-taxon-index tia))
                                  (subset (mytips (list rest))
                                          (get-taxa-from-taxon-index tia))
                                  (taspip nil (list rest))
                                  (taspip nil (list
                                               (orderly-cons
                                                (car (cdadr x))
                                                (list rest)
                                                tia)))
                                  (subset (mytips (list
                                               (orderly-cons
                                                (car (cdadr x))
                                                (list rest)
                                                tia)))
                                          (get-taxa-from-taxon-index tia))
                                  (taspip nil  (list (orderly-cons (caadr x)
                                                                           (list rest)
                                                                           tia)))
                                  (subset (mytips (list (orderly-cons (caadr x)
                                                                           (list rest)
                                                                           tia)))
                                          (get-taxa-from-taxon-index tia))
                                  (member-gen (first-taxon (car x))
                                              (get-taxa-from-taxon-index tia))
                                  (subset (mytips (hist (orderly-cons (car x)
                                                                        (hist rest)
                                                                        tia)))
                                          (get-taxa-from-taxon-index tia))
                                  (taspip nil (hist (orderly-cons (car x)
                                                                        (hist rest)
                                                                        tia)))
                                  (member-gen (first-taxon (cadr x))
                                              (get-taxa-from-taxon-index tia)))
                             (hppend (get-tbr-pieces 'inside (caadr x)
                                                      (orderly-cons (car x)
                                                                    (hist
                                                                     (orderly-cons
                                                                      (car (cdadr x))
                                                                      (hist rest)
                                                                      tia))
                                                                    tia)
                                                      tia)
                                      (get-tbr-pieces 'inside (car (cdadr x))
                                                      (orderly-cons
                                                       (car x)
                                                       (hist (orderly-cons (caadr x)
                                                                           (hist rest)
                                                                           tia))
                                                       tia)
                                                      tia)
                                      (hist (orderly-cons (cadr x)
                                                          (hist (orderly-cons (car x)
                                                                        (hist rest)
                                                                        tia))
                                                          tia)))
                           "Error: Need binary tree in fourth branch
                                        get-tbr-pieces")
                       (if (and (member-gen (first-taxon (car x))
                                            (get-taxa-from-taxon-index tia))
                                (subset (mytips (list rest))
                                        (get-taxa-from-taxon-index tia))
                                (taspip nil (list rest))
                                (member-gen (first-taxon (cadr x))
                                            (get-taxa-from-taxon-index tia))
                                (subset (mytips (hist (orderly-cons (car x) (hist
                                                                            rest)
                                                                   tia)))
                                        (get-taxa-from-taxon-index tia))
                                (taspip nil (hist (orderly-cons (car x) (hist
                                                                            rest)
                                                                   tia))))
                           (hist (orderly-cons (cadr x)
                                               (hist (orderly-cons (car x) (hist
                                                                            rest)
                                                                   tia))
                                       tia))
                         "Error: Need pieces to match in get-tbr-pieces"))
                   "Error: Need binary tree in last branch get-tbr-pieces")
                 (if (and (member-gen (first-taxon x)
                                      (get-taxa-from-taxon-index tia))
                          (taspip nil (list rest))
                          (subset (mytips (list rest))
                                  (get-taxa-from-taxon-index tia)))
                     (hist (orderly-cons x (hist rest) tia))
                   "Error: Need pieces to match 2 in get-tbr-pieces")
                 )
       (if (and (member-gen (first-taxon x)
                                      (get-taxa-from-taxon-index tia))
                          (taspip nil (list rest))
                          (subset (mytips (list rest))
                                  (get-taxa-from-taxon-index tia)))
           (hist (orderly-cons x (hist rest) tia))
         "Error: Need pieces to match last in get-tbr-pieces"))))


;(get-tbr-pieces 'inside '(a (b c)) (d (e f)))
;(get-tbr-pieces 'top '(((a (b c)) ((d e) f)) (g h)) nil)
;(get-tbr-pieces 'inside '(a (b c)) '(d (e f)))
;(get-tbr-pieces 'top '((a b) (c d)) nil)
;(get-tbr-pieces 'top '(((a b) c) d) nil)
;(get-tbr-pieces 'top '(a (b (c d))) nil)

(defun spliceConsBack (piece1 pieces ans)
  (declare (xargs :guard t));(good-taxon-index-halist tia)))
  (if (consp pieces)
      (spliceConsBack piece1 (cdr pieces)
                      (hons (hons (car pieces) piece1)
                            ans))
    ans))

(defun make-spr-pieces-to-do-tbr (x ans tia)
  (declare (xargs :guard (good-taxon-index-halist tia)))
  (if (consp x)
      (if (consp (car x))
          (make-spr-pieces-to-do-tbr
           (cdr x)
           (spliceConsBack (cdar x)
                           (get-tbr-pieces 'top (caar x) nil tia)
                           ans)
           tia)
        "Error: Need an alist in make-spr-pieces-to-do-tbr")
    ans))

;takes an unrooted tree as input and returns tbr neighbours.
(defun phylo-tbr (x tia)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the tbr (tree bisect reconnect) neighbors of the input tree~/
;  ~/
;  Arguments:
;    (1) x - a tree
;    (2) tia - a mapping of taxa names to integers

;  Details: The tree should have the taxa names in the tia.  The tree should be
;           unrooted.  Does not handle branch lengths."
  (declare (xargs :guard (good-taxon-index-halist tia)))
  (if (and (consp x)
           (consp (cdr x))
           (consp (cddr x))
           (atom (cdddr x)))
      (if (and (atom (car x))
               (atom (cadr x))
               (atom (caddr x)))
          x
        (let ((spr-pieces (make-spr-pieces-to-do-tbr
                           (orderly-get-pieces x nil nil tia)
                           nil tia)))
          (if (alistp-gen spr-pieces)
              (orderly-do-spr
                spr-pieces
               tia nil)
            "Error: Need good alist in phylo-tbr")))
    "Error: Need unrooted tree in phylo-tbr"))

#||

(phylo-tbr '(a b c) (make-tia '(a b c)))
(phylo-tbr '(a b (c d)) (make-tia '(a b c d)))
(phylo-tbr '(a (b (c e)) d) (make-tia '(a b c d e)))
(phylo-tbr '(a ((b f)(c e)) d) (make-tia '(a b c d e f)))
(phylo-tbr '(a ((b (c e)) (d f)) g) (make-tia '(a b c d e f g)))

((A B (C E) D)
 ((A D) B C E)
 (B A (C E) D)
 ((C E) A B D)
 (C (A D) B E)
 (E (A D) B C)
 (D A B (C E))
 ((A D) B C E))


||#
