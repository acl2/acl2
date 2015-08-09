(in-package "ACL2")
(include-book "replete")
(include-book "../brlens/trees-with-brlens")

(defthm halistp-replete-trees
  (implies (alistp-gen db)
           (alistp-gen (replete-trees args parent db))))

(verify-guards replete-trees)

(encapsulate ()

(local (defthm replete-trees-arg-not-in-domain1
         (implies (and (not (proper-subtreep l r)))
                  (equal (assoc-hqual l (replete-trees r o db))
                         (assoc-hqual l db)))) )

(defthm bound-to-nat-list-no-proper-subtrees-in-list
  (implies (and (not (has-proper-subtree-in-list a l))
                (bound-to-nat-list l db))
           (bound-to-nat-list l (replete-trees a b db)))
  :hints (("Goal" :induct (bound-to-nat-list l db))))
)

(verify-guards replete-trees-list-top1)
(verify-guards replete-trees-list-top)
(verify-guards frequency)

(defthm nat-or-cons-range-halistp-replete-trees
  (implies (nat-or-cons-range-halistp db)
           (nat-or-cons-range-halistp (replete-trees args parent db))))


(defthm if-nat-val-key-not-subtree-of-tree-replete-trees
  (implies (if-nat-val-key-not-subtree-of tree db)
           (if-nat-val-key-not-subtree-of tree (replete-trees args parent
                                                              db))))

(defthm if-nat-val-key-not-subtree-of-any-replete-trees
  (implies (if-nat-val-key-not-subtree-of-any list db)
           (if-nat-val-key-not-subtree-of-any list (replete-trees args parent
                                                                  db)))
  :hints (("Goal" :induct (if-nat-val-key-not-subtree-of-any list db))))

(defthm not-subtree-not-not-subtree-gives-proper-subtreep
  (implies (and (not (not-subtree-of-keys
                      l
                      (replete-trees tree parent db)))
                (not-subtree-of-keys l db))
           (proper-subtreep l tree)))

(defthm not-not-subtree-of-keys-gives-has-proper-subtree-in-list
  (implies (and (not (not-subtree-of-keys
                      l1
                      (replete-trees tree parent db)))
                (not-subtree-of-keys l1 db)
                (not-subtree-of-keys-list l2 db)
                (not (proper-subtreep l1 tree))
                )
           (has-proper-subtree-in-list tree l2)))

(defthm not-subtree-of-keys-list-replete-trees
  (implies (and (not-subtree-of-keys-list l db)
                (not (has-proper-subtree-in-list tree l)))
           (not-subtree-of-keys-list l (replete-trees tree parent db)))
  :hints (("Goal" :in-theory (enable proper-subtreep subtreep))))

(defun replete-trees-ind (args parent db parents)
  ;; Guard is to make parent relevant so we can use as induction scheme
  (declare (xargs :guard (and (alistp-gen db) (equal parents parents))
                  :verify-guards nil))
  (if (atom args)
      db
    (if (atom (car args))
        (replete-trees-ind (cdr args) parent db parents)
      (let ((p (het (car args) db)))
        (if p
            (replete-trees-ind
             (cdr args) parent (hut (car args) (cons parent (cdr p)) db) parents)
          (prog2$
           (replete-trees-ind
            (cdr args) parent
            (hut (car args) (cons parent (cdr p))
                 (replete-trees (car args) (car args) db))
            parents)
           (replete-trees-ind (car args) (car args) db (cons (car args)
                                                             parents))))))))

(defthm if-cons-range-subset-of-domain-halistp-replete-trees1
  (implies (and (if-cons-range-subset-of-domain-or-list db db parents)
                (nat-or-cons-range-halistp db)
                (if-nat-val-key-not-subtree-of parent db)
                (subset args parent)
                (member-hqual parent parents))
           (if-cons-range-subset-of-domain-or-list
            (replete-trees args parent db)
            (replete-trees args parent db)
            parents))
  :hints (("Goal" :induct (replete-trees-ind args parent db parents))))

(defthm if-cons-range-subset-of-domain-halistp-replete-trees
  (implies (and (if-cons-range-subset-of-domain-halistp db db)
                (nat-or-cons-range-halistp db)
                (if-nat-val-key-not-subtree-of parent db)
                (subset args parent))
           (if-cons-range-subset-of-domain-halistp
            (cons (cons parent 1) (replete-trees args parent db))
            (cons (cons parent 1) (replete-trees args parent db))))
  :hints (("Goal" :use (:instance
                        if-cons-range-subset-of-domain-halistp-replete-trees1
                        (parents (list parent)))
           :in-theory (disable
                       if-cons-range-subset-of-domain-halistp-replete-trees1))))

(defthm if-cons-range-member-of-all-replete-trees
  (implies (and (if-cons-range-member-of-all-halistp db)
                (nat-or-cons-range-halistp db)
                (if-nat-val-key-not-subtree-of parent db)
                (subset args parent))
           (if-cons-range-member-of-all-halistp
            (replete-trees args parent db)))
  :hints (("Goal" :induct (replete-trees args parent db))))

(defthm replete-trees-list-top1-type
  (implies (and (alistp-gen db)
                (not-subtree-of-keys-list l db)
                (if-cons-range-subset-of-domain-halistp db db)
                (nat-or-cons-range-halistp db)
                (if-nat-val-key-not-subtree-of-any l db)
                (if-cons-range-member-of-all-halistp db)
                (bound-to-nat-list l db)
                (non-subtree-listp l l))
           (and (alistp-gen (replete-trees-list-top1 l db))
                (if-cons-range-subset-of-domain-halistp
                 (replete-trees-list-top1 l db)
                 (replete-trees-list-top1 l db))
                (nat-or-cons-range-halistp
                 (replete-trees-list-top1 l db))
                (if-cons-range-member-of-all-halistp
                 (replete-trees-list-top1 l db))))
  :hints (("Goal" :induct (replete-trees-list-top1 l db))))

(defthm replete-trees-list-top-type
  (implies (non-subtree-listp l l)
           (and (alistp-gen (replete-trees-list-top l))
                (if-cons-range-subset-of-domain-halistp
                 (replete-trees-list-top l)
                 (replete-trees-list-top l))
                (nat-or-cons-range-halistp
                 (replete-trees-list-top l))
                (if-cons-range-member-of-all-halistp
                 (replete-trees-list-top l))))
  :hints (("Goal" :in-theory (enable replete-trees-list-top))))

(defthm tree-alist-replete-trees
  (implies (and (tree-listp args)
                (tree-list-domain-alistp db))
           (tree-list-domain-alistp (replete-trees args parent db))))

(defthm tree-alist-replete-trees-list-top1
  (implies (and (tree-list-listp l)
                (tree-list-domain-alistp db))
           (tree-list-domain-alistp (replete-trees-list-top1 l db))))

(defthm tree-alist-replete-trees-list-top
  (implies (tree-list-listp l)
           (tree-list-domain-alistp (replete-trees-list-top l)))
  :hints (("Goal" :in-theory (enable replete-trees-list-top))))

;; Functions that first remove-brlens and then call
;; appropriate function

;; the idea here is that l is a tree-listp-brlens
(defun replete-trees-list-brlens (l)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns a replete mapping of trees and subtrees in the input list to either
;  the number of times the tree occurs or to a list of each subtrees immediate
;  parents.~/
;  ~/
;  Arguments:
;     (1) l - a list of trees no member of which is a proper subtree of another

;  Details: The trees should all be ordered according to the same taxa list.
;           Branch lengths are allowed, but not preserved
;           (see replete-trees-list-top)."
  (declare (xargs :guard t))
  (let ((removed (remove-brlens-list l)))
    (if (non-subtree-listp removed removed)
        (replete-trees-list-top removed)
      'invalid-input-to-replete)))

#||
(replete-trees-list-brlens '((((a b) (c d)) . 4) ((e . 5) f)
                             ))

||#
