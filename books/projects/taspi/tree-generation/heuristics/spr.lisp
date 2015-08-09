;; a subset of tbr moves are spr's at the edges of the tree...
;;  gonna start there

;; piece is the piece taken off, rest is the pruned tree we are attaching to
;; need to reattach at all possible places

(in-package "ACL2")
(include-book "../tree-gen-helper/basics")
(include-book "../../code/tree-manip/top")

;takes a well-formed piece (which means it is a binary tree,
; whose attaching point is defined by the root), with an unrooted
; rest of the tree
; Returns result of attaching the piece to every point within
; resulting in a binary unrooted tree
;; ASSUMES piece binary rooted and rest binary unrooted
(defun orderly-spr-helper (flg piece rest tia)
  (declare (xargs :guard (good-taxon-index-halist tia)))
  (if (equal flg 'topnode)
      (if (and (consp rest)
               (consp (cdr rest))
               (consp (cddr rest)))
          (hppend (orderly-splice (cdr rest)
                                   (orderly-spr-helper 'not-top
                                                       piece
                                                       (car rest)
                                                       tia)
                                   nil
                                   tia)
                   (orderly-splice (hist (car rest)
                                         (caddr rest))
                                   (orderly-spr-helper 'not-top
                                                       piece
                                                       (cadr rest)
                                                       tia)
                                   nil
                                   tia)
                   (orderly-splice
                    (hist (car rest) (cadr rest))
                    (orderly-spr-helper 'not-top piece
                                        (caddr rest)
                                        tia)
                    nil
                    tia))
        "Error: Must start with unrooted tree in orderly-spr-helper")
    ;'not-top-node case, so in binary two pieces
    (if (consp rest)
        (if (consp (cdr rest))
            (if (and (taspip nil (list rest))
                     (subset (mytips (list rest))
                             (get-taxa-from-taxon-index tia))
                     (member-gen (first-taxon piece)
                                 (get-taxa-from-taxon-index tia)))
                (hppend (hist (orderly-cons piece (hist rest) tia))
                         (orderly-splice (car rest)
                                         (orderly-spr-helper 'not-top piece
                                                             (cadr rest)
                                                             tia)
                                         nil tia)
                         (orderly-splice (cadr rest)
                                         (orderly-spr-helper 'not-top
                                                             piece
                                                             (car rest)
                                                              tia)
                                         nil tia))
              "Error: Need pieces to match tia in orderly-spr-helper")
          "Error: Rest must be binary in orderly-spr-helper")
      (if (and (taspip nil (list rest))
               (subset (mytips (list rest))
                       (get-taxa-from-taxon-index tia))
               (member-gen (first-taxon piece)
                           (get-taxa-from-taxon-index tia)))
          (hist (orderly-cons piece (hist rest) tia))
        "Error: Need pieces to match tia in second branch of orderly-spr-helper"))))


;returns true if there are interesting things to be done to x
; short circuits execution -- we should only get to three
; symbols and never to all of them in a tree if there are more
; than three
(defun go-on?-helper (x n)
  (declare (xargs :guard (rationalp n)
                  :verify-guards nil))
  (if (> n 2)
      (mv t n)
    (if (consp x)
        (mv-let (yes1 val1)
                (go-on?-helper (car x) (1+ n))
                (if yes1 (mv t val1)
                  (mv-let (yes2 val2)
                          (go-on?-helper (cdr x) (1+ n))
                          (if yes2 (mv t val2)
                            (let ((newVal (+ val1 val2)))
                              (if (> newVal 2)
                                  (mv t newVal)
                                (mv nil newVal)))))))
      (mv nil 0))))

(defthmd go-on?-helper-rationalp
  (implies (rationalp n)
           (rationalp (mv-nth 1 (go-on?-helper x n)))))

(verify-guards
 go-on?-helper
 :hints (("Subgoal 3''"
          :use (:instance go-on?-helper-rationalp
                          (n (+ 1 n))
                          (x x1)))
         ("Subgoal 2'" :use ((:instance go-on?-helper-rationalp
                                       (n (+ 1 n))
                                       (x x1))
                             (:instance go-on?-helper-rationalp
                                        (n (+ 1 n))
                                        (x x2))))
         ("Subgoal 1''"
          :use (:instance go-on?-helper-rationalp
                          (n (+ 1 n))
                          (x x2)))
         ))

(defun go-on? (x)
  (declare (xargs :guard t))
  (mv-let (var val)
          (go-on?-helper x 0)
          (declare (ignore val))
          var))

(defun orderly-get-pieces (x rest ans tia)
  (declare (xargs :guard (good-taxon-index-halist tia)))
  (if (and (consp x)
           (consp (cdr x))
           (consp (cddr x)))
      (hppend (orderly-get-pieces (car x) (cdr x) nil tia)
              (orderly-get-pieces (cadr x) (hons (car x) (cddr x)) nil tia)
              (orderly-get-pieces (caddr x) (hist (car x) (cadr x)) nil tia)
              (if (go-on? (caddr x))
                  (let ((newRest (branch-to-node (caddr x) tia)))
                    (if (and (taspip t newRest)
                             (subset (mytips newRest)
                                     (get-taxa-from-taxon-index tia)))
                        (hons (hons (hist (car x) (cadr x))
                                    (order-by-insertion-one-level newRest
                                                                  tia))
                              nil)
                      "Error: Need good newRest in orderly-get-pieces"))
                nil)
              (if (go-on? (cadr x))
                  (let ((newRest (branch-to-node (cadr x) tia)))
                    (if (and (taspip t newRest)
                             (subset (mytips newRest)
                                     (get-taxa-from-taxon-index tia)))
                        (hons (hons (hist (car x) (caddr x))
                                    (order-by-insertion-one-level newRest
                                                                  tia))
                              nil)
                      "Error: Need good newRest in second branch of orderly-get-pieces"))
                nil)
              )
    (if (consp x)
        (if (or (atom rest) ;we want rest always length 2
                (atom (cdr rest)))
            ans
          ;we have a rest rooted at a branch
          (hppend
           (if (and (atom (car rest)) ; we have a simple branch
                    (atom (cadr rest)))
               ans ; don't add anything here
             (let ((newRest (branch-to-node rest tia)))
               (if (and (taspip t newRest)
                        (subset (mytips newRest)
                                (get-taxa-from-taxon-index tia)))
                   (hons (hons x (order-by-insertion-one-level newRest
                                                               tia))
                               ans)
                 "Error: Need good newRest in third branch of orderly-get-pieces")))
           (if (go-on? x)
               (let ((newRest (branch-to-node x tia)))
                 (if (and (taspip t newRest)
                          (subset (mytips newRest)
                                  (get-taxa-from-taxon-index tia)))
                     (hons-acons rest
                                 (order-by-insertion-one-level newRest tia)
                                 nil)
                   "Error: Need good newRest in fourth branch of orderly-get-pieces"))
             nil)
           (if (consp (cdr x))
               (if (and (subset (mytips (list rest))
                                (get-taxa-from-taxon-index tia))
                        (member-gen (first-taxon (cadr x))
                                    (get-taxa-from-taxon-index tia))
                        (member-gen (first-taxon (car x))
                                    (get-taxa-from-taxon-index tia))
                        (taspip nil (list rest)))
                   (hppend
                    (orderly-get-pieces (car x)
                                        (orderly-cons (cadr x) (hist rest) tia)
                                        nil tia)
                    (orderly-get-pieces (cadr x)
                                        (orderly-cons (car x) (hist rest) tia)
                                        nil tia))
                 "Error: Need properties for orderly-cons in orderly-get-pieces")
             "Error: need binary trees in get-pieces")
            ))
      (let ((newRest (branch-to-node rest tia)))
        (if (and (taspip t newRest)
                 (subset (mytips newRest)
                         (get-taxa-from-taxon-index tia)))
            (hons (hons x (order-by-insertion-one-level newRest tia)) ans)
          "Error: Need good newRest in last branch of orderly-get-pieces")))))

(defun mv-root-and-remove-dups (list tia hash)
  (declare (xargs :guard (and (good-taxon-index-halist tia)
                              (alistp-gen hash))))
  (if (consp list)
      (let ((normed (mv-root (car list) tia)))
        (if (het normed hash)
            (mv-root-and-remove-dups (cdr list) tia hash)
          (mv-root-and-remove-dups (cdr list) tia
                                   (hut normed t hash))))
    hash))

(defun orderly-do-spr (pieces tia hash)
  (declare (xargs :guard (and (alistp-gen pieces)
                              (alistp-gen hash)
                              (good-taxon-index-halist tia))))
  (if (consp pieces)
      (let ((newHash
             (mv-root-and-remove-dups
              (orderly-spr-helper 'topnode (caar pieces)
                                  (cdar pieces) tia)
              tia hash)))
              (if (alistp-gen newHash)
                  (orderly-do-spr (cdr pieces)
                                  tia
                                  newHash)
                "Error: Need good hash table returned in orderly-do-spr"))
    (strip-cars-gen hash)))

(defun orderly-spr (x tia)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the spr (subtree prune regraft) neighbors of the input tree~/
;  ~/
;  Arguments:
;    (1) x - a tree
;    (2) tia - a mapping of taxa names to integers

;  Details: The tree should have the taxa names in the tia.  The tree should be
;           unrooted. NB: Does not handle branch lengths."
  (declare (xargs :guard (good-taxon-index-halist tia)))
  (if (and (consp x)
           (consp (cdr x))
           (consp (cddr x))
           (atom (cdddr x)))
      (if (and (atom (car x))
               (atom (cadr x))
               (atom (caddr x)))
          x
        (let ((pieces (orderly-get-pieces x nil nil tia)))
          (if (alistp-gen pieces)
              (orderly-do-spr
               (orderly-get-pieces x nil nil tia)
           tia nil)
            "Error: Need good pieces from orderly-get-pieces in orderly-spr")))
    "Error: Need unrooted tree in orderly-spr"))


#||
(orderly-spr '(a (b e) (c d)) (make-tia '(a b c d e)))
(len (orderly-spr '(a ((b (c e)) f) g) (make-tia '(a b c e f g))))
(len (orderly-spr '(a ((b (c e)) (d f)) g) (make-tia '(a b c d e f g))))
(orderly-spr-helper 'topnode 'g '(a (b (c e)) f) (make-tia '(a b c d e f g)))
||#
