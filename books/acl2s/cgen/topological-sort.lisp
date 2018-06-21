#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t :ttags :all);$ACL2s-Preamble$|#

;;; Author: Harsh Raju Chamarthi (harshrc)
;;; Modified from centaur/misc/ and centaur/depgraph books.

(in-package "CGEN")
;; (include-book "utilities")
;; (include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)
(include-book "centaur/misc/dfs-measure" :dir :system)
(include-book "centaur/misc/hons-extra" :dir :system)

;; DFS on graphs. G is a fast-alist representing the adjacency-list
;; form of graph to be traversed. nodes is the vertices of G left to
;; explore. seen is a fast-alist stack that records the status of
;; nodes of G (initially it is len of G), as unbound (not started),
;; :started, :finished. G should have bindings for all nodes that
;; appear in it. Loops are ignored.

(defun dfs (nodes G seen)
  (declare (xargs :well-founded-relation acl2::nat-list-<
                  :measure (acl2::dfs-measure nodes G seen)
                  :guard t :verify-guards nil))
  (b* (((when (atom nodes)) seen)
       (node (car nodes))
       ((when (hons-get node seen))
        ;; seen this node before.
        (dfs (cdr nodes) G seen))
       (successors (cdr (hons-get node G)))
       (seen1 (hons-acons node :started seen))
       (seen1 (dfs successors G seen1))
       (seen1 (hons-acons node :finished seen1))
       ((unless (mbt (acl2::suffixp seen seen1))) seen1)) ;;for termination

      (dfs (cdr nodes) G seen1)))

(defthm dfs-suffixp
  (acl2::suffixp seen (dfs nodes G seen))
  :hints(("Goal" :induct (dfs nodes G seen))))

(defthm dfs-suffixp-cons
  (acl2::suffixp seen (dfs nodes G (cons x seen)))
  :hints(("Goal" :use (:instance acl2::suffixp-transitive
                       (a seen)
                       (b (cons x seen))
                       (c (dfs nodes G (cons x seen))))
          :in-theory (disable acl2::suffixp-transitive))))

(verify-guards dfs)

;; (defthm dfs-type
;;     (alistp (dfs nodes G seen))
;;   :hints (("Goal" :in-theory (disable (:induction alistp))
;;                   :induct (dfs nodes G seen)))
;;   :rule-classes (:rewrite :type-prescription))

;; get finished nodes in post-order
(defun topologically-ordered-nodes (seen acc)
  (declare (xargs :guard (true-listp acc)))
  (if (atom seen)
      (revappend acc nil)
      (if (and (consp (car seen))
               (eq (cdr (car seen)) :finished))
          (topologically-ordered-nodes (cdr seen) (cons (caar seen) acc))
          (topologically-ordered-nodes (cdr seen) acc))))

(defun topo-sort (G)
  (declare (xargs :guard t))
  (b* (((acl2::with-fast G))
       (nodes (acl2::alist-keys G))
       (seen (dfs nodes G (len nodes)))
       (ordered-nodes (topologically-ordered-nodes seen nil)))
      
      (acl2::fast-alist-free seen)
      ordered-nodes))

(include-book "simple-graph-array")
(defstub topological-sort (*) => *)
(defattach topological-sort topo-sort)
;; (defattach topological-sort approx-topo-sort)
