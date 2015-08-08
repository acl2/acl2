;; We are going to guard on the assumption that the
;; input tree is already ordered, so if the tree
;; is rooted, we need do nothing to get in a good
;; state.  However, if the tree is unrooted, we want
;; to move the root of the tree so that the result
;; is a tree with the same ordering whose representation
;; is rooted at the node connecting the least taxon
;; (as specified by the taxon-index-alist) to the rest
;; of the tree

;; Ordering is required, because we need fringes
;; computations to be consistent

;(d (e (b (a c))))
;(c ((a b) (d e)))
; The two above need to result in common fringe (d e)
; normal forms: (a (b (d e) c))
;               (a b (c (d e)))

(in-package "ACL2")
(include-book "../build/build-term-guards")

(defun rooted-at-branch (x)
  (declare (xargs :guard t))
  (< (len x) 3))

;; moves root of rep closer to first taxon of tree
;; if root is already at node closest to first taxon
;; returns tree unchanged
(defun node-to-node (x tia)
  "Called on a rep rooted at a node"
  (declare (xargs :guard (good-taxon-index-halist tia)))
  (if (consp x)
      (if (consp (car x))
          (if (and (taspip nil (cdar x))
                   (taspip nil (list (cdr x)))
                   (subset (mytips (cdar x))
                           (get-taxa-from-taxon-index tia))
                   (subset (mytips (cdr x))
                           (get-taxa-from-taxon-index tia)))
              (hons (caar x)
                    (orderly-append (cdar x) (list (cdr x)) tia))
            "Error: x does not match tia in node-to-node")
        x)
    x))

;; unchanged fringes only if treep x
;(node-to-node '((a b) c (d e)))
;(node-to-node '(a b (c d ( e f))))
;(node-to-node '(((a) b) c (d e f)))

;; moves root of rep to side of branch closest
;; to first taxon
(defun branch-to-node (x tia)
  "Called on a rep rooted at a branch"
  (declare (xargs :guard (good-taxon-index-halist tia)))
  (if (consp x)
      (if (consp (car x))
          (if (and (taspip nil (car x))
                   (taspip nil (cdr x))
                   (subset (mytips (car x))
                           (get-taxa-from-taxon-index tia))
                   (subset (mytips (cdr x))
                           (get-taxa-from-taxon-index tia)))
              (orderly-append (car x) (cdr x) tia)
            "Error: Need x to match tia in branch-to-node")
        ;; we're on a branch, so only two elements
        ;; even if we're on the branch connecting
        ;; the first taxon, this will work to move
        ;; us to the node at which the first-taxon
        ;; is connected
        (if (consp (cdr x))
            (if (and (taspip nil (cadr x))
                     (subset (mytips (cadr x))
                             (get-taxa-from-taxon-index tia))
                     (member-gen (first-taxon (car x))
                                 (get-taxa-from-taxon-index tia)))
                (orderly-cons (car x) (cadr x) tia)
              "Error: Need x to match tia in second branch of branch-to-node")
          x))
    x))

; again, only good unchanged fringes if treep
;(branch-to-node '((a b) (c (d e))))
;(branch-to-node '(((a (b c) d) (e f)) g))
;(branch-to-node '(a (b c d)))
;(branch-to-node '((a b c) (d e)))

(defun num-moves (x)
  (if (consp x)
      (1+ (num-moves (car x)))
    0))

(defun mv-root-helper (x tia)
  (declare (xargs :guard (good-taxon-index-halist tia)
                  :measure (num-moves x)))
  (let ((new (node-to-node x tia)))
    (if (equal new x)
        x
      (mv-root-helper new tia))))

(defun mv-root (x tia)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the structurally unchanged unrooted tree now with a representation
;  rooted at the node connecting the first taxon according to the mapping
;  given to the rest of the tree.~/
;  ~/
;  Arguments:
;    (1) x - an unrooted tree
;    (2) tia - a mapping from each taxa name to an integer

;  Details: Must be called on an unrooted tree in order to not change
;           structure.  If the initial representation is ordered according
;           to the mapping given, the resulting representation will be as
;           well.  Taxa names in the tree must match up with the taxa names
;           in the mapping."
  (declare (xargs :guard (good-taxon-index-halist tia)))
  (if (rooted-at-branch x)
      (if (int-symlist x)
          x
        (mv-root-helper (branch-to-node x tia) tia))
    (mv-root-helper x tia)))

(defun mv-root-list (list tia ans)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the list of structurally unchanged unrooted trees now each with a
;  representation rooted at the node connecting the first taxon according to
;  the mapping given to the rest of the tree.~/
;  ~/
;  Arguments:
;    (1) list - a list of unrooted trees
;    (2) tia - a mapping from each taxa name to an integer
;    (3) ans - accumulator (initally nil)

;  Details: Must be called on a list of unrooted trees in order to not change
;           structure.  If each of the initial representations is ordered
;           according to the mapping given, the resulting representations will
;           be as well.  Taxa names in the trees must match up with the taxa
;           names in the mapping."
  (declare (xargs :guard (good-taxon-index-halist tia)))
  (if (consp list)
      (mv-root-list (cdr list) tia
                    (hons (mv-root (car list) tia) ans))
    ans))

(defthm taspip-through-app
  (implies (and (taspip flg x)
                (taspip nil y))
           (taspip nil (app x y))))

(defthm consp-throug-app
  (implies (consp x)
           (consp (app x y))))

(defthm to-nil
  (implies (and (equal (len x) 0)
                (taspip nil x))
           (equal x nil))
  :rule-classes :forward-chaining)

(defthm taspip-neither-int-sym-cons
  (implies (and (taspip t x)
                (not (integerp x))
                (not (symbolp x)))
           (consp x))
  :rule-classes :forward-chaining)


;(defthm taspip-through-branch-to-node
;  (implies (and (taspip flg x)
;                (<= (len (double-rewrite x)) 2)
;                (not (int-symlist (double-rewrite x))))
;           (taspip flg (branch-to-node x tia))))

(defthm len-app-greater
  (implies (and (consp x)
                (consp y))
           (<= 2 (len (app x (list y))))))

(defthm tree-listp-of-app
  (implies (tree-listp x)
           (equal (tree-listp (app x y))
                  (tree-listp y))))

(defthm tree-listp-of-list
  (implies (and (tree-listp y)
                (<= 2 (len (double-rewrite y))))
           (tree-listp (list y))))

;; gave double rewrite warning twice
;(defthm taspip-through-mv-root-helper
;  (implies (and (taspip flg x)
;                (treep x)
;                (<= 3 (len (double-rewrite x))))
;           (and (taspip flg (mv-root-helper x))
;                (treep (mv-root-helper x))))
;  :hints (("Goal" :in-theory
;           (disable len-greater-1-tree-listp=treep))
;))

(defthm treep-through-app
  (implies (and (treep x)
                (taspip t x)
                (taspip nil y)
                (consp y)
                (consp x)
                (tree-listp y))
           (treep (app x y))))

(defthm len-0-not-consp
  (implies (equal (len x) 0)
           (not (consp x)))
  :rule-classes :forward-chaining)

(defthm to-len-greater-2
  (implies (and (consp x)
                (consp y))
           (<= 2 (len (app x y)))))

(defthm to-len-greater-3
  (implies (and (consp x)
                (treep x)
                (consp y))
           (<= 3 (len (app x y)))))

;(defthm mv-root-preserves-taspip-and-treep
;  (implies (and (taspip flg x)
;                (treep x))
;           (and (taspip flg (mv-root x))
;                (treep (mv-root x))))
;  :hints (("Subgoal 7'4'" :in-theory
;           (disable taspip-through-mv-root-helper)
;           :use (:instance taspip-through-mv-root-helper
;                           (x (app x1 x2))))
;                    ))

(in-theory (disable mv-root))

; These would be nice to get through some day
;(skip-proofs
;(defthm mv-root-perserves-tips
;  (implies (and (treep tree)
;                (taspip t tree)
;                (perm (mytips tree) tl)
;                (orderedp t tree (taxa-list-to-taxon-index tl)))
;           (perm (mytips (mv-root tree)) tl)))
;)

;(skip-proofs
;(defthm ordered-through-mv-root
;  (implies (and (treep tree)
;                (taspip t tree)
;                (perm (mytips tree) (double-rewrite tl))
;                (orderedp t tree (taxa-list-to-taxon-index tl)))
;           (orderedp t (mv-root tree)
;                     (taxa-list-to-taxon-index tl))))
;)
