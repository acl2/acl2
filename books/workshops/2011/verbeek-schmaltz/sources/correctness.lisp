#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#


(in-package "ACL2")
(include-book "invariants3")




;;--------------------------------------
;;--------------------------------------
;; 4.) deadlock -> algorithm returns t
;;--------------------------------------
;;--------------------------------------
;; We prove that if there is some subgraph that can have a deadlock, this subgraph is disjunct with the set of 2-marked nodes.
;; This proof follows the same structure if the invariants. Frist we prove, inductively, that it holds for step 1 (theorem step1-preserves-dl->not2-inductive).
;; Then we prove it for the call of step 1 with prev=-1 (thoerem step1-preserves-dl->not2). Then we prove it for step 2 (theorem step2-preserves-dl->not2).
;; Lastly, for the algorithm as a whole (theorem algo-preserves-dl->not2).
;; From this follows theorem dl->3-after-algo-inductive which states any node in a deadlock will be marked 3 by the algorithm.
;; The final theorem is dl->algo-returns-nil which states that the algorithm returns nil if there is a deadlock.
(defthm not-member-nil-valid-nodes
  (implies (A-valid-nodes nodes nodeset)
           (not (member-equal nil nodes))))
(defthm find-2node-in-2neighbors
  (implies (and (filled-graphp (nodes-length nodeset) graph)
                (valid-graph (nodes-length nodeset) graph nodeset)
                (not (member-equal nil neighbors))
                (natp node)
                (< node (nodes-length nodeset))
                (is-keys-of-alist neighbors neighbors->destsi)
                (subsetp neighbors->destsi (neighbors->destsi node graph))
                (member-equal dest (A-dests-of node (st-filter-2marked-nodes neighbors marks) graph nodeset)))
           (find-2node (st-filter-neighbors-for-dest neighbors->destsi dest) marks))
  :hints (("Goal" :in-theory (disable neighborsi neighbors->destsi depi esci marksi))
          ("Subgoal *1/10" :use (:instance assoc-key-yeilds-field
                                 (key (car neighbors))
                                 (field (car neighbors->destsi))
                                 (alist (neighbors->destsi node graph))))))
(defthm spec-of-A-dests-E-2neighbor
  (implies (and (A-dests-E-2neighbor node dests marks graph)
                (member-equal dest dests))
           (find-2node (st-filter-neighbors-for-dest (neighbors->destsi node graph) dest) marks)))

(defthmd labels-in-graph-subset-A-dests-of
  (implies (and (is-keys-of-alist neighbors neighbors->destsi)
                (no-duplicatesp-equal (keys (neighbors->destsi node graph)))
                (subsetp neighbors->destsi (neighbors->destsi node graph))
                (not (equal node -1)))
           (subsetp (union-of (values-alist neighbors->destsi))
                    (A-dests-of node neighbors graph nodeset)))
  :hints (("Subgoal *1/4" :use ((:instance assoc-key-yeilds-field
                                 (field (car neighbors->destsi))
                                 (key (car neighbors))
                                 (alist (neighbors->destsi node graph)))))))
(defthm 2marked-node-member-of
  (implies (and (A-natp nodes2)
                (natp node)
                (not-in nodes1 (st-filter-2marked-nodes nodes2 marks))
                (not (not-in nodes1 (st-filter-2marked-nodes nodes2 (update-marksi node 2 marks)))))
           (and (member-equal node nodes1)
                (member-equal node nodes2)))
  :hints (("Goal" :in-theory (disable marksi update-marksi)
                  :induct (st-filter-2marked-nodes nodes2 marks))))
(defthm not-in-cons
  (iff (not-in x (cons a y))
       (and (not (member-equal a x))
            (not-in x y))))
(defthm 2marked-node-implies-not-notin-st-filter-2marked-nodes
  (implies (and (equal (marksi node marks) 2)
                (member-equal node nodes1)
                (member-equal node nodes2))
           (not (not-in nodes1 (st-filter-2marked-nodes nodes2 marks)))))
(defthm find-2node-implies-not-notin-st-filter-2marked-nodes
  (implies (and (find-2node nodes1 marks)
                (subsetp nodes1 nodes2)
                (subsetp nodes2 nodes3))
           (not (not-in nodes2 (st-filter-2marked-nodes nodes3 marks))))
  :hints (("Goal" :in-theory (disable marksi))))
(defthm A-valid-nodes-st-all-nodes
  (implies (A-valid-nodes nodes nodeset)
           (subsetp nodes (st-all-nodes nodeset))))
(defthm escape-witness-implies-find-escape
  (implies (and (st-escapep node subgraph (union-of (values-alist (neighbors->destsi node graph))) graph)
                (consp (neighborsi node graph))
                (A-natp nodes)
                (member-equal node nodes))
           (st-find-escape nodes subgraph graph)))
(defthm valid-nodes-are-nats
  (implies (and (A-valid-nodes nodes nodeset)
                (member-equal node nodes))
           (natp node))
  :rule-classes :forward-chaining)
(defthm A-dests-E-2neighbor-subsetp
  (implies (and (subsetp x y)
                (A-dests-E-2neighbor node y marks graph))
           (A-dests-E-2neighbor node x marks graph)))
(defthm parents-have-neighbors
  (implies (and (member-equal node nodes)
                (st-A-parents nodes graph))
           (consp (neighborsi node graph))))




(defthm subsetp-st-filter-2marked-nodes-update-marksi-4;;TODO
  (subsetp (st-filter-2marked-nodes nodes (update-marksi node 4 marks))
           (st-filter-2marked-nodes nodes marks)))








(defthm temp3.6
  (equal (setminus (append x y) z)
         (append (setminus x z)
                 (setminus y z))))
(defthm temp3.11
  (implies (A-valid-nodes nodes nodeset)
           (A-valid-nodes (setminus nodes x) nodeset)))
(defthm temp3.12
  (implies (endp y)
           (equal (setminus x y) x)))
(defthm temp3.13
  (implies (not-in x y)
           (equal (setminus x y) x)))
(defthm temp3.14
  (equal (A-valid-nodes (remove-duplicates-equal x) nodeset)
         (A-valid-nodes x nodeset)))
(defthm temp3.16
  (equal (not-in (remove-duplicates-equal x) y)
         (not-in x y)))
(defthm temp3.17
  (equal (not-in (append x y) z)
         (and (not-in x z)
              (not-in y z))))
(defthm temp3.18
  (not-in (setminus x y) y))
(defthm temp3.19
  (iff (member-equal a (setminus x y))
       (if (member-equal a y)
         nil
         (member-equal a x))))

(defun st-d-pathp (path dest st-graph st-nodeset)
  (declare (xargs :stobjs (st-graph st-nodeset)
                  :verify-guards nil))
  (cond ((endp path)
         nil)
        ((endp (cdr path))
         (and (equal (cdr path) nil)
              (st-valid-node (car path) st-nodeset)))
        (t
         (and (st-valid-node (car path) st-nodeset)
              (st-valid-node (cadr path) st-nodeset)
              (member-equal (cadr path) (st-filter-neighbors-for-dest (neighbors->destsi (car path) st-graph) dest))
              (st-d-pathp (cdr path) dest st-graph st-nodeset)))))
;; Returns t iff there exists a path from `from' to `to' disjunct from `subgraph'
(defun-sk E-d-path-from-to-not-in (from to subgraph dest graph nodeset)
  (exists (path)
          (and (st-d-pathp path dest graph nodeset)
               (not-in path subgraph)
               (equal (car path) from)
               (equal (car (last path)) to))))
(defun E-from-E-d-path-from-to-not-in (nodes node subgraph dest graph nodeset)
  (cond ((endp nodes)
         nil)
        ((E-d-path-from-to-not-in (car nodes) node subgraph dest graph nodeset)
         (list (car nodes)))
        (t
         (E-from-E-d-path-from-to-not-in (cdr nodes) node subgraph dest graph nodeset))))

(defthm temp3.27
  (implies (and (st-d-pathp path dest graph nodeset)
                (member-equal node path))
           (st-d-pathp (member-equal node path) dest graph nodeset)))
(defthm temp3.28
  (implies (not-in x y)
           (not-in (member-equal a x) y)))
(defthm temp3.29
  (equal (car (last (member-equal a x)))
         (if (member-equal a x)
           (car (last x))
           nil)))
(defthm temp3.30
  (equal (car (member-equal a x))
         (if (member-equal a x)
           a
           nil)))

(defun skip-to-last-occ (x a)
  (if (not (member-equal a x))
    x
    (skip-to-last-occ (cdr (member-equal a x)) a)))
(defthm temp3.33
  (implies (and (st-d-pathp path dest graph nodeset)
                (member-equal node path)
                (not (equal (car (last path)) node)))
           (member-equal (cadr (member-equal node path)) (st-filter-neighbors-for-dest (neighbors->destsi node graph) dest))))
(defthm temp3.34
  (implies (and (member-equal a x)
                (not (equal (car (last x)) a)))
           (equal (car (last (cdr (member-equal a x))))
                  (car (last x)))))
(defthm temp3.35
  (implies (and (member-equal node path)
                (not (equal (car (last path)) node))
                (st-d-pathp path dest graph nodeset))
           (st-d-pathp (cdr (member-equal node path)) dest graph nodeset)))
(defthm temp3.32
  (implies (and (st-d-pathp path dest graph nodeset)
                (member-equal node path)
                (not (equal (car (last path)) node)))
           (member-equal (car (skip-to-last-occ path node)) (st-filter-neighbors-for-dest (neighbors->destsi node graph) dest)))
  :hints (("Goal" :in-theory (disable neighbors->destsi))))
(defthm temp3.39
  (implies (and (member-equal a x)
                (not (equal (car (last x)) a)))
           (equal (car (last (skip-to-last-occ x a)))
                  (car (last x)))))
(defthm temp3.40
  (not (member-equal a (skip-to-last-occ x a))))
(defthm temp3.42
  (implies (not-in x y)
           (not-in (cdr (member-equal a x)) y)))
(defthm temp3.41
  (implies (not-in x y)
           (not-in (skip-to-last-occ x a) y)))
(defthm temp3.43
  (implies (and (st-d-pathp path dest graph nodeset)
                (member-equal node path)
                (not (equal (car (last path)) node)))
           (st-d-pathp (skip-to-last-occ path node) dest graph nodeset)))

(defthm neighborsi-irreflexive
  (implies (and (< node n)
                (natp node)
                (natp n)
                (filled-graphp n graph))
           (not (member-equal node (neighborsi node graph)))))

(defthm temp20.0
  (equal (setminus x (append y z))
         (setminus (setminus x y) z)))
(defthm temp2.2
  (equal (no-duplicatesp-equal (append x z))
         (and (no-duplicatesp-equal x)
              (no-duplicatesp-equal z)
              (not-in x z))))
(defthm temp2.4
  (implies (no-duplicatesp-equal x)
           (no-duplicatesp-equal (setminus x z))))
(defthm temp2.5
  (not-in (setminus (setminus x y) z) y))
(defthm temp3.21
  (equal (E-from-E-d-path-from-to-not-in (append x1 y1) to subgraph dest graph nodeset)
         (or (E-from-E-d-path-from-to-not-in x1 to subgraph dest graph nodeset)
             (E-from-E-d-path-from-to-not-in y1 to subgraph dest graph nodeset)))
  :hints (("Goal" :in-theory (disable E-d-path-from-to-not-in)
                  :induct (E-from-E-d-path-from-to-not-in x1 to subgraph dest graph nodeset))))

(defthm temp21.3
  (implies (and (E-d-path-from-to-not-in from to subgraph dest graph nodeset)
                (member-equal from froms))
           (E-from-E-d-path-from-to-not-in froms to subgraph dest graph nodeset))
  :hints (("Goal" :in-theory (disable E-d-path-from-to-not-in))))


(defthm temp3.23
  (implies (and (E-d-path-from-to-not-in from to subgraph dest graph nodeset)
                (member-equal from froms))
           (E-from-E-d-path-from-to-not-in froms to subgraph dest graph nodeset)))

(defthm temp3.31
  (implies (and (E-d-path-from-to-not-in from to subgraph dest graph nodeset)
                (not (equal from to)))
           (E-from-E-d-path-from-to-not-in (st-filter-neighbors-for-dest (neighbors->destsi from graph) dest) to (cons from subgraph) dest graph nodeset))
  :hints (("Goal" :use ((:instance temp3.23
                         (from (car (skip-to-last-occ (E-d-path-from-to-not-in-witness from to subgraph dest graph nodeset) from)))
                         (froms (st-filter-neighbors-for-dest (neighbors->destsi from graph) dest))
                         (subgraph (cons from subgraph)))
                        (:instance temp3.32
                         (path (E-d-path-from-to-not-in-witness from to subgraph dest graph nodeset))
                         (node from))
                        (:instance E-d-path-from-to-not-in-suff
                         (from (car (skip-to-last-occ (E-d-path-from-to-not-in-witness from to subgraph dest graph nodeset) from)))
                         (path (skip-to-last-occ (E-d-path-from-to-not-in-witness from to subgraph dest graph nodeset) from))
                         (subgraph (cons from subgraph)))
                        (:instance temp3.43
                         (path (E-d-path-from-to-not-in-witness from to subgraph dest graph nodeset))
                         (node from))
                        (:instance temp3.39
                         (x (E-d-path-from-to-not-in-witness from to subgraph dest graph nodeset))
                         (a from))))))
(defthm temp3.31v2
  (implies (member-equal from subgraph)
           (not (E-d-path-from-to-not-in from to subgraph dest graph nodeset))))

(defthmd temp21.2.1
  (implies (and (is-keys-of-alist keys alist)
                (A-valid-nodes keys nodeset)
                (member-equal field alist))
           (st-valid-node (car field) nodeset)))
(defthm temp21.2
  (implies (and (filled-graphp n graph)
                (valid-graph n graph nodeset)
                (natp n)
                (natp node)
                (< node n)
                (subsetp neighbors->destsi (neighbors->destsi node graph)))
           (A-valid-nodes (st-filter-neighbors-for-dest neighbors->destsi dest) nodeset))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :in-theory (disable neighborsi neighbors->destsi nodesi))
          ("Subgoal *1.1/3" :use (:instance temp21.2.1
                                  (keys (neighborsi (1- n) graph))
                                  (alist (neighbors->destsi (1- n) graph))
                                  (field (car neighbors->destsi))))))


(defthm temp21.1
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (filled-graphp (nodes-length nodeset) graph)
                ;;Invariant
                (A-valid-nodes nodes nodeset)
                (E-from-E-d-path-from-to-not-in nodes to stack dest graph nodeset))
           (not (equal (st-find-next-d-step nodes to stack dest graph nodeset) 'failure)))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :induct (st-find-next-d-step nodes to stack dest graph nodeset)
                  :in-theory (disable E-d-path-from-to-not-in))
          ("Subgoal *1/5" :use (:instance temp3.31
                                  (from (car nodes))
                                  (subgraph stack)))))

(defthm temp21.0
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (filled-graphp (nodes-length nodeset) graph)
                (natp n)
                (st-d-pathp path dest graph nodeset)
                (or (equal (marksi (car (last path)) marks) 0)
                    (equal (marksi (car (last path)) marks) 1)
                    (and (equal (marksi (car (last path)) marks) 3)
                         (member-equal dest (depi (car (last path)) marks))
                         (not (member-equal dest (esci (car (last path)) marks)))))
                (natp (car (last path)))
                (st-valid-node (car (last path)) nodeset)
                (< (car (last path)) n)
                (st-valid-node node nodeset)
                (member-equal node path))
           (E-013-marked-E-d-path n node dest marks graph nodeset))
  :hints (("Goal" :induct (E-013-marked-E-d-path n node dest marks graph nodeset)
                  :in-theory (disable marksi E-d-path-from-to-not-in neighbors->destsi))
          ("Subgoal *1/3" :use ((:instance temp21.1
                                 (nodes (st-filter-neighbors-for-dest (neighbors->destsi node graph) dest))
                                 (to (1- n))
                                 (stack (list node)))
                                (:instance temp3.31
                                 (from node)
                                 (to (1- n))
                                 (subgraph nil))
                                (:instance E-d-path-from-to-not-in-suff
                                 (from node)
                                 (to (1- n))
                                 (subgraph nil)
                                 (path (member-equal node path)))))))

(defthm temp21.4
  (implies (st-d-pathp path dest graph nodeset)
           (natp (car (last path)))))
(defthm temp21.5
  (implies (st-d-pathp path dest graph nodeset)
           (< (car (last path)) (nodes-length nodeset)))
  :rule-classes :linear)
(defthmd temp14.1v2
  (implies (st-d-pathp path dest graph nodeset)
           (st-valid-node (car (last path)) nodeset)))
(defthmd temp14.1v3
  (implies (and (st-d-pathp path dest graph nodeset)
                (member-equal node path))
           (st-valid-node node nodeset)))
(defthm temp21.00
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (filled-graphp (nodes-length nodeset) graph)
                (natp n)
                (st-d-pathp path dest graph nodeset)
                (or (equal (marksi (car (last path)) marks) 0)
                    (equal (marksi (car (last path)) marks) 1)
                    (and (equal (marksi (car (last path)) marks) 3)
                         (member-equal dest (depi (car (last path)) marks))
                         (not (member-equal dest (esci (car (last path)) marks)))))
                (natp dest)
                (< dest n)
                (equal (nodesi dest nodeset) 1)
                (member-equal node path))
           (E-d-E-d-path-to-013-marked-node n node marks graph nodeset))
  :hints (("Goal" :induct (E-d-E-d-path-to-013-marked-node n node marks graph nodeset))
          ("Subgoal *1/3" :use ((:instance temp21.0
                                   (n (nodes-length nodeset)))
                                  (:instance temp14.1v2)
                                  (:instance temp14.1v3)
                                   ))))

(defthm temp3.1
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (filled-graphp (nodes-length nodeset) graph)
                (st-d-pathp path dest graph nodeset)
                (st-valid-node dest nodeset)
                (member-equal node path)
                (or (equal (marksi (car (last path)) marks) 0)
                    (equal (marksi (car (last path)) marks) 1)
                    (and (equal (marksi (car (last path)) marks) 3)
                         (member-equal dest (depi (car (last path)) marks))
                         (not (member-equal dest (esci (car (last path)) marks))))))
           (E-d-path-to-013-marked-node node marks graph nodeset)))





(defun paths-satisfy-condition (paths dests subgraph st-graph st-nodeset)
  (declare (xargs :stobjs (st-graph st-nodeset)
                  :verify-guards nil))
  (if (or (endp paths) (endp dests))
    (and (endp paths) (endp dests))
    (and (subsetp (st-filter-neighbors-for-dest (neighbors->destsi (car (last (car paths))) st-graph) (car dests)) subgraph)
         (st-d-pathp (car paths) (car dests) st-graph st-nodeset)
         (member-equal (car dests) (A-dests-of (car (last (car paths))) (neighborsi (car (last (car paths))) st-graph) st-graph st-nodeset))
         (paths-satisfy-condition (cdr paths) (cdr dests) subgraph st-graph st-nodeset))))

(defun find-d-path-containing (paths dests node)
  (cond ((endp paths)
         nil)
        ((member-equal node (car paths))
         (list (car paths) (car dests)))
        (t
         (find-d-path-containing (cdr paths) (cdr dests) node))))
(defthm temp1.10
  (implies (find-d-path-containing paths dests node)
           (member-equal (car (find-d-path-containing paths dests node)) paths)))
(defthm temp1.11
  (implies (member-equal node (union-of paths))
           (find-d-path-containing paths dests node)))
(defthm temp1.12
  (implies (find-d-path-containing paths dests node)
           (member-equal node (car (find-d-path-containing paths dests node))))
  :rule-classes :forward-chaining)

(defthm temp3.0
  (implies (and (paths-satisfy-condition paths dests subgraph graph nodeset)
                (member-equal node (union-of paths)))
           (st-d-pathp (car (find-d-path-containing paths dests node)) (cadr (find-d-path-containing paths dests node)) graph nodeset)))

(defthm temp1.13
  (implies (and (paths-satisfy-condition paths dests subgraph graph nodeset)
                (find-d-path-containing paths dests node))
           (subsetp (st-filter-neighbors-for-dest (neighbors->destsi (car (last (car (find-d-path-containing paths dests node)))) graph) (cadr (find-d-path-containing paths dests node)))
                    subgraph)))
(defthm temp1.13v2
  (implies (and (paths-satisfy-condition paths dests subgraph graph nodeset)
                (find-d-path-containing paths dests node))
           (member-equal (cadr (find-d-path-containing paths dests node))
                         (A-dests-of (car (last (car (find-d-path-containing paths dests node)))) (neighborsi (car (last (car (find-d-path-containing paths dests node)))) graph) graph nodeset))))




(defthm temp6.0
  (implies (legal-mark x)
           (or (equal x 0)
               (equal x 1)
               (equal x 2)
               (equal x 3)
               (equal x 4)))
  :rule-classes nil)


(defthm temp1.5
  (implies (is-keys-of-alist neighbors neighbors->destsi)
           (iff (endp neighbors)
                (endp neighbors->destsi)))
  :rule-classes nil)

(defthm temp21.6
  (implies (and (find-d-path-containing paths dests node)
                (paths-satisfy-condition paths dests subgraph graph nodeset)
                (A-valid-nodes dests nodeset))
           (st-valid-node (cadr (find-d-path-containing paths dests node)) nodeset)))

(defthm node-where-dest-leads-to-2marked-nodes-only-is-escape-for-subgraph-of-not2-marked-nodes
  (implies (and (A-valid-nodes subgraph nodeset)
                (find-2node (st-filter-neighbors-for-dest neighbors->destsi dest) marks)
                (not-in subgraph (st-filter-2marked-nodes (st-all-nodes nodeset) marks)))
           (not (subsetp (st-filter-neighbors-for-dest neighbors->destsi dest) subgraph)))
  :hints (("Goal" :in-theory (disable nodes-length))))

(defthm temp25.1
  (implies (and (member-equal a x)
                (subsetp x (append y z))
                (subsetp y z))
           (member-equal a z)))
(defthm temp25.2
  (implies (and (member-equal a x)
                (subsetp x (append y z))
                (not (member-equal a y)))
           (member-equal a z))
  :hints (("Goal" :induct (member-equal a x))))
(defthm temptemp
  (implies (and (not-in x y)
                (subsetp z y))
           (not-in x z)))
(defthm step1-preserves-dl->not2-inductive
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  (A-valid-nodes nodes nodeset)
                  ;; If there is deadlock:
                  (paths-satisfy-condition paths dests (union-of paths) graph nodeset)
                  (st-A-parents (union-of paths) graph)
                  (A-valid-nodes (union-of paths) nodeset)
                  (A-valid-nodes dests nodeset)
                  ;; Invariant:
                  (natp prev)
                  (equal (marksi prev marks) 1)
                  (subsetp nodes (neighborsi prev graph))
                  (invariant-legal (nodes-length nodeset) marks)
                  (invariant-4marks (nodes-length nodeset) marks)
                  (invariant-2marks (nodes-length nodeset) marks graph)
                  (invariant-comp (nodes-length nodeset) marks graph nodeset)
                  (invariant-escs2 (nodes-length nodeset) marks graph)
                  ;; Then the deadlock will not be marked 2
                  (not-in (union-of paths) (st-filter-2marked-nodes (st-all-nodes nodeset) marks)))
             (not-in (union-of paths) (st-filter-2marked-nodes (st-all-nodes nodeset) marks-after))))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset)
                  :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi E-d-path-to-013-marked-node
                                      marksi-update-marksi subsetp-st-filter-2marked-nodes-update-marksi-3 subsetp-st-filter-2marked-nodes-update-marksi-4 legal-mark spec-of-A-dests-E-2neighbor
                                      spec-of-invariant-escs2 temp1.11 spec-of-invariant-2marks temp21.4 temp21.5 temp21.6 neighbors-are-keys-of-neighbors->destsi
                                      temp1.13v2))
          ("Subgoal *1/7.12" :use (:instance subsetp-st-filter-2marked-nodes-update-marksi-3
                                  (node (car nodes))
                                  (nodes (st-all-nodes nodeset))
                                  (marks (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset))))
          ("Subgoal *1/7.8" :use (:instance subsetp-st-filter-2marked-nodes-update-marksi-4
                                  (node (car nodes))
                                  (nodes (st-all-nodes nodeset))
                                  (marks (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset))))
          ("Subgoal *1/7.4" :use ((:instance node-where-dest-leads-to-2marked-nodes-only-is-escape-for-subgraph-of-not2-marked-nodes
                                   (neighbors->destsi (neighbors->destsi (car (last (car (find-d-path-containing paths dests (car nodes))))) graph))
                                   (dest (cadr (find-d-path-containing paths dests (car nodes))))
                                   (marks (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset))
                                   (subgraph (union-of paths)))
                                  (:instance temp1.11
                                   (node (car nodes)))
                                  (:instance 2marked-node-member-of
                                   (nodes1 (union-of paths))
                                   (nodes2 (st-all-nodes nodeset))
                                   (node (car nodes))
                                   (marks (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))
          ("Subgoal *1/7.4.2" :use ((:instance temp8.3
                                     (n (nodes-length nodeset))
                                     (i (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                     (marks (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))
                                    (:instance temp21.5
                                     (path (car (find-d-path-containing paths dests (car nodes))))
                                     (dest (cadr (find-d-path-containing paths dests (car nodes)))))
                                    (:instance temp21.4
                                     (path (car (find-d-path-containing paths dests (car nodes))))
                                     (dest (cadr (find-d-path-containing paths dests (car nodes))))))
                              :expand (LEGAL-MARK (MARKSI (CAR (LAST (CAR (FIND-D-PATH-CONTAINING PATHS DESTS (CAR NODES)))))
                                                          (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset))))
          ("Subgoal *1/7.4.2.5" :use (;marking of header of path is equal to 0
                                      (:instance temp3.1
                                       (node (car nodes))
                                       (path (car (find-d-path-containing paths dests (car nodes))))
                                       (dest (cadr (find-d-path-containing paths dests (car nodes))))
                                       (marks (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))
                                      (:instance temp21.6
                                        (node (car nodes))
                                        (subgraph (union-of paths)))))
          ("Subgoal *1/7.4.2.4" :use (;marking of header of path is equal to 1
                                      (:instance temp3.1
                                       (node (car nodes))
                                       (path (car (find-d-path-containing paths dests (car nodes))))
                                       (dest (cadr (find-d-path-containing paths dests (car nodes))))
                                       (marks (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))
                                      (:instance temp21.6
                                        (node (car nodes))
                                        (subgraph (union-of paths)))))
          ("Subgoal *1/7.4.2.3" :use (;marking of header of path is equal to 2
                                      (:instance spec-of-invariant-escs2
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                       (marks (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))
                                      (:instance spec-of-A-dests-E-2neighbor
                                       (node (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                       (dests (esci (car (last (car (find-d-path-containing paths dests (car nodes)))))
                                                    (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))
                                       (dest (cadr (find-d-path-containing paths dests (car nodes))))
                                       (marks (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))
                                      (:instance spec-of-invariant-comp2
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                       (marks (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))
                                      (:instance spec-of-invariant-2marks
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                       (marks (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))
                                      (:instance temp1.13v2
                                       (node (car nodes))
                                       (subgraph (union-of paths)))))
          ("Subgoal *1/7.4.2.2" :use (;marking of header of path is equal to 3
                                      (:instance temp3.1
                                       (node (car nodes))
                                       (path (car (find-d-path-containing paths dests (car nodes))))
                                       (dest (cadr (find-d-path-containing paths dests (car nodes))))
                                       (marks (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))
                                       (:instance temp21.6
                                        (node (car nodes))
                                        (subgraph (union-of paths)))
                                       (:instance spec-of-invariant-escs2
                                        (n (nodes-length nodeset))
                                        (i (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                        (marks (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))
                                       (:instance spec-of-A-dests-E-2neighbor
                                        (node (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                        (dests (esci (car (last (car (find-d-path-containing paths dests (car nodes)))))
                                                     (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))
                                        (dest (cadr (find-d-path-containing paths dests (car nodes))))
                                        (marks (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))
                                       (:instance spec-of-invariant-comp
                                        (n (nodes-length nodeset))
                                        (i (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                        (marks (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))
                                       (:instance temp1.13v2
                                        (node (car nodes))
                                        (subgraph (union-of paths)))
                                      ))
          ("Subgoal *1/7.4.2.1" :use (;marking of header of path is equal to 4
                                      (:instance spec-of-invariant-escs2
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                       (marks (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))
                                      (:instance spec-of-A-dests-E-2neighbor
                                       (node (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                       (dests (esci (car (last (car (find-d-path-containing paths dests (car nodes)))))
                                                    (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))
                                       (dest (cadr (find-d-path-containing paths dests (car nodes))))
                                       (marks (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))
                                      (:instance spec-of-invariant-comp4
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                       (marks (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))
                                      (:instance spec-of-invariant-4marks
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                       (marks (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))
                                      (:instance temp1.13v2
                                       (node (car nodes))
                                       (subgraph (union-of paths)))))
          ("Subgoal *1/5" :use ((:instance 2marked-node-member-of
                                 (nodes1 (union-of paths))
                                 (nodes2 (st-all-nodes nodeset))
                                 (node (car nodes)))))))

(defthm step1-preserves-dl->not2
  (let* ((marks-after (st-escapable-inv (list node) -1 graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  (equal (nodesi node nodeset) 1)
                  ;; If there is deadlock:
                  (paths-satisfy-condition paths dests (union-of paths) graph nodeset)
                  (st-A-parents (union-of paths) graph)
                  (A-valid-nodes (union-of paths) nodeset)
                   (A-valid-nodes dests nodeset)
                  ;; Invariant:
                  (invariant-legal (nodes-length nodeset) marks)
                  (invariant-4marks (nodes-length nodeset) marks)
                  (invariant-2marks (nodes-length nodeset) marks graph)
                  (invariant-comp (nodes-length nodeset) marks graph nodeset)
                  (invariant-escs2 (nodes-length nodeset) marks graph)
                  (not-in (union-of paths) (st-filter-2marked-nodes (st-all-nodes nodeset) marks)))
             (not-in (union-of paths) (st-filter-2marked-nodes (st-all-nodes nodeset) marks-after))))
  :otf-flg t
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :expand (st-escapable-inv (list node) -1 graph marks nodeset)
                  :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi E-d-path-to-013-marked-node
                                      marksi-update-marksi subsetp-st-filter-2marked-nodes-update-marksi-3 subsetp-st-filter-2marked-nodes-update-marksi-4 legal-mark spec-of-A-dests-E-2neighbor
                                      spec-of-invariant-escs2 temp1.11 spec-of-invariant-2marks temp21.4 temp21.5 temp21.6 neighbors-are-keys-of-neighbors->destsi
                                      temp1.13v2

                                      subsetp-st-filter-2marked-nodes-update-marksi-3 step1-preserves-dl->not2-inductive))
          ("Subgoal 4" :use ((:instance step1-preserves-dl->not2-inductive
                              (nodes (neighborsi node graph))
                              (prev node)
                              (marks (update-marksi node 1 marks)))
                             (:instance subsetp-st-filter-2marked-nodes-update-marksi-3
                              (nodes (st-all-nodes nodeset))
                              (marks (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset)))))
          ("Subgoal 2" :use ((:instance step1-preserves-dl->not2-inductive
                              (nodes (neighborsi node graph))
                              (prev node)
                              (marks (update-marksi node 1 marks)))
                             (:instance subsetp-st-filter-2marked-nodes-update-marksi-4
                              (nodes (st-all-nodes nodeset))
                              (marks (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset)))))
          ("Subgoal 3" :use ((:instance node-where-dest-leads-to-2marked-nodes-only-is-escape-for-subgraph-of-not2-marked-nodes
                              (neighbors->destsi (neighbors->destsi (car (last (car (find-d-path-containing paths dests node)))) graph))
                              (dest (cadr (find-d-path-containing paths dests node)))
                              (marks (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset))
                              (subgraph (union-of paths)))
                             (:instance temp1.11)
                             (:instance 2marked-node-member-of
                              (nodes1 (union-of paths))
                              (nodes2 (st-all-nodes nodeset))
                              (marks (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset)))
                             (:instance step1-preserves-dl->not2-inductive
                              (nodes (neighborsi node graph))
                              (prev node)
                              (marks (update-marksi node 1 marks)))))
          ("Subgoal 3.2" :use ((:instance temp8.3
                                (n (nodes-length nodeset))
                                (i (car (last (car (find-d-path-containing paths dests node)))))
                                (marks (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset)))
                               (:instance temp21.5
                                (path (car (find-d-path-containing paths dests node)))
                                (dest (cadr (find-d-path-containing paths dests node))))
                               (:instance temp21.4
                                (path (car (find-d-path-containing paths dests node)))
                                (dest (cadr (find-d-path-containing paths dests node)))))
                         :expand (legal-mark (marksi (car (last (car (find-d-path-containing paths dests node))))
                                                     (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset))))
          ("Subgoal 3.2.5" :use (;marking of header of path is equal to 0
                                      (:instance temp3.1
                                       (path (car (find-d-path-containing paths dests node)))
                                       (dest (cadr (find-d-path-containing paths dests node)))
                                       (marks (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset)))
                                      (:instance temp21.6
                                       (node node)
                                       (subgraph (union-of paths)))))
          ("Subgoal 3.2.4" :use (;marking of header of path is equal to 1
                                      (:instance temp3.1
                                       (path (car (find-d-path-containing paths dests node)))
                                       (dest (cadr (find-d-path-containing paths dests node)))
                                       (marks (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset)))
                                      (:instance temp21.6
                                       (node node)
                                       (subgraph (union-of paths)))))
          ("Subgoal 3.2.3" :use (;marking of header of path is equal to 2
                                      (:instance spec-of-invariant-escs2
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests node)))))
                                       (marks (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset)))
                                      (:instance spec-of-A-dests-E-2neighbor
                                       (node (car (last (car (find-d-path-containing paths dests node)))))
                                       (dests (esci (car (last (car (find-d-path-containing paths dests node))))
                                                    (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset)))
                                       (dest (cadr (find-d-path-containing paths dests node)))
                                       (marks (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset)))
                                      (:instance spec-of-invariant-comp2
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests node)))))
                                       (marks (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset)))
                                      (:instance spec-of-invariant-2marks
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests node)))))
                                       (marks (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset)))
                                      (:instance temp1.13v2
                                       (node node)
                                       (subgraph (union-of paths)))))
          ("Subgoal 3.2.2" :use (;marking of header of path is equal to 3
                                      (:instance temp3.1
                                       (path (car (find-d-path-containing paths dests node)))
                                       (dest (cadr (find-d-path-containing paths dests node)))
                                       (marks (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset)))
                                      (:instance temp21.6
                                       (node node)
                                       (subgraph (union-of paths)))
                                      (:instance spec-of-invariant-escs2
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests node)))))
                                       (marks (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset)))
                                      (:instance spec-of-A-dests-E-2neighbor
                                       (node (car (last (car (find-d-path-containing paths dests node)))))
                                       (dests (esci (car (last (car (find-d-path-containing paths dests node))))
                                                    (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset)))
                                       (dest (cadr (find-d-path-containing paths dests node)))
                                       (marks (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset)))
                                      (:instance spec-of-invariant-comp
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests node)))))
                                       (marks (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset)))
                                      (:instance temp1.13v2
                                       (node node)
                                       (subgraph (union-of paths)))))
          ("Subgoal 3.2.1" :use (;marking of header of path is equal to 4
                                      (:instance spec-of-invariant-escs2
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests node)))))
                                       (marks (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset)))
                                      (:instance spec-of-A-dests-E-2neighbor
                                       (node (car (last (car (find-d-path-containing paths dests node)))))
                                       (dests (esci (car (last (car (find-d-path-containing paths dests node))))
                                                    (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset)))
                                       (dest (cadr (find-d-path-containing paths dests node)))
                                       (marks (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset)))
                                      (:instance spec-of-invariant-comp4
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests node)))))
                                       (marks (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset)))
                                      (:instance spec-of-invariant-4marks
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests node)))))
                                       (marks (st-escapable-inv (neighborsi node graph) node graph (update-marksi node 1 marks) nodeset)))
                                      (:instance temp1.13v2
                                       (subgraph (union-of paths)))))
          ("Subgoal 1" :use ((:instance 2marked-node-member-of
                              (nodes1 (union-of paths))
                              (nodes2 (st-all-nodes nodeset)))
                             (:instance parents-have-neighbors
                              (nodes (union-of paths)))))))

(defthm A-natp-show-nodeset
  (A-natp (show-nodeset n nodeset)))

(defthm temp9.3
  (implies (and (subsetp x (append y z))
                (subsetp y z))
           (subsetp x z)))
(defthm temp9.4
  (implies (and (st-A-parents nodes graph)
                (member-equal node nodes))
           (neighborsi node graph)))
(defthm temp9.6
  (implies (st-d-pathp path dest graph nodeset)
           (member-equal (car (last path)) path)))
(defthm temp9.5
  (implies (and (paths-satisfy-condition paths dests subgraph graph nodeset)
                (find-d-path-containing paths dests node))
           (member-equal (car (last (car (find-d-path-containing paths dests node)))) (union-of paths))))

(defthm temp9.7
  (equal (A-dests-E-2neighbor node dests (append-to-esc i x marks) graph)
         (A-dests-E-2neighbor node dests marks graph))
  :hints (("Goal" :in-theory (disable update-esci))))


(defthm temp25.3
  (implies (subsetp x (append y z))
           (subsetp x (append y w z))))

(defthmd temp25.4
  (implies (and (member-equal a x)
                (subsetp x (append y z))
                (subsetp y (append w z))
                (not (member-equal a z)))
           (member-equal a w))
  :hints (("Goal" :induct (member-equal a x))))


(defthm step2-preserves-dl->not2
  (let* ((marks-after (process-escs-eff nodes stack marks graph nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  (A-valid-nodes nodes nodeset)
                  ;; If there is deadlock:
                  (paths-satisfy-condition paths dests (union-of paths) graph nodeset)
                  (st-A-parents (union-of paths) graph)
                  (A-valid-nodes (union-of paths) nodeset)
                  (A-valid-nodes dests nodeset)
                  ;; Invariant:
                  (invariant-legal (nodes-length nodeset) marks)
                  (invariant-4marks (nodes-length nodeset) marks)
                  (invariant-2marks (nodes-length nodeset) marks graph)
                  (invariant-comp (nodes-length nodeset) marks graph nodeset)
                  (invariant-escs2 (nodes-length nodeset) marks graph)
                  ;; Then the deadlock will not be marked 2
                  (not-in (union-of paths) (st-filter-2marked-nodes (st-all-nodes nodeset) marks)))
             (not-in (union-of paths) (st-filter-2marked-nodes (st-all-nodes nodeset) marks-after))))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :induct (process-escs-eff nodes stack marks graph nodeset)
                  :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi E-d-path-to-013-marked-node
                                      marksi-update-marksi subsetp-st-filter-2marked-nodes-update-marksi-3 subsetp-st-filter-2marked-nodes-update-marksi-4 legal-mark spec-of-A-dests-E-2neighbor
                                      spec-of-invariant-escs2 temp1.11 spec-of-invariant-2marks temp21.4 temp21.5 temp21.6 neighbors-are-keys-of-neighbors->destsi
                                      temp1.13v2 spec-of-invariant-comp temp8.3 TEMP1.16
                                      ))
          ("Subgoal *1/3.1" :use (:instance subsetp-st-filter-2marked-nodes-update-marksi-4
                                  (node (car nodes))
                                  (nodes (st-all-nodes nodeset))))
          ("Subgoal *1/3.3" :use ((:instance update-marksi-4-preserves-invariant-comp-visited
                                   (n (nodes-length nodeset))
                                   (i (car nodes))
                                   (marks (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks) graph nodeset) marks)))
                                  (:instance spec-of-invariant-comp
                                   (n (nodes-length nodeset))
                                   (i (car nodes))
                                   (marks (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks) graph nodeset) marks)))))

          ("Subgoal *1/4" :use ((:instance node-where-dest-leads-to-2marked-nodes-only-is-escape-for-subgraph-of-not2-marked-nodes
                                 (neighbors->destsi (neighbors->destsi (car (last (car (find-d-path-containing paths dests (car nodes))))) graph))
                                 (dest (cadr (find-d-path-containing paths dests (car nodes))))
                                 (subgraph (union-of paths))
                                 (marks (update-marksi (car nodes) 4
                                                       (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks)
                                                                                              graph nodeset) marks))))
                                (:instance temp1.11
                                 (node (car nodes)))
                                (:instance 2marked-node-member-of
                                 (nodes1 (union-of paths))
                                 (nodes2 (st-all-nodes nodeset))
                                 (node (car nodes)))
                                (:instance subsetp-st-filter-2marked-nodes-update-marksi-4
                                 (node (car nodes))
                                 (nodes (st-all-nodes nodeset)))))
          ("Subgoal *1/4.2" :use ((:instance temp8.3
                                   (n (nodes-length nodeset))
                                   (i (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                   (marks (update-marksi (car nodes) 4
                                                         (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks)
                                                                                                graph nodeset) marks))))
                                  (:instance temp21.5
                                   (path (car (find-d-path-containing paths dests (car nodes))))
                                   (dest (cadr (find-d-path-containing paths dests (car nodes)))))
                                  (:instance temp21.4
                                   (path (car (find-d-path-containing paths dests (car nodes))))
                                   (dest (cadr (find-d-path-containing paths dests (car nodes))))))
                            :expand (legal-mark (marksi (car (last (car (find-d-path-containing paths dests (car nodes)))))
                                                        (update-marksi (car nodes) 4
                                                                       (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc-equal (car nodes) stack))) marks)
                                                                                                              graph nodeset) marks)))))
          ("Subgoal *1/4.2.5" :use (;marking of header of path is equal to 0
                                      (:instance temp3.1
                                       (node (car nodes))
                                       (path (car (find-d-path-containing paths dests (car nodes))))
                                       (dest (cadr (find-d-path-containing paths dests (car nodes))))
                                       (marks (update-marksi (car nodes) 4
                                                                       (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks)
                                                                                                              graph nodeset) marks))))
                                      (:instance temp21.6
                                        (node (car nodes))
                                        (subgraph (union-of paths)))))
          ("Subgoal *1/4.2.4" :use (;marking of header of path is equal to 1
                                      (:instance temp3.1
                                       (node (car nodes))
                                       (path (car (find-d-path-containing paths dests (car nodes))))
                                       (dest (cadr (find-d-path-containing paths dests (car nodes))))
                                       (marks (update-marksi (car nodes) 4
                                                                       (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks)
                                                                                                              graph nodeset) marks))))
                                      (:instance temp21.6
                                        (node (car nodes))
                                        (subgraph (union-of paths)))))
          ("Subgoal *1/4.2.3" :use (;marking of header of path is equal to 2
                                      (:instance spec-of-invariant-escs2
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                       (marks (update-marksi (car nodes) 4
                                                                       (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks)
                                                                                                              graph nodeset) marks))))
                                      (:instance spec-of-A-dests-E-2neighbor
                                       (node (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                       (dests (esci (car (last (car (find-d-path-containing paths dests (car nodes)))))
                                                    (update-marksi (car nodes) 4
                                                                       (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks)
                                                                                                              graph nodeset) marks))))
                                       (dest (cadr (find-d-path-containing paths dests (car nodes))))
                                       (marks (update-marksi (car nodes) 4
                                                                       (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks)
                                                                                                              graph nodeset) marks))))
                                      (:instance spec-of-invariant-comp2
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                       (marks (update-marksi (car nodes) 4
                                                                       (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks)
                                                                                                              graph nodeset) marks))))
                                      (:instance spec-of-invariant-2marks
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                       (marks (update-marksi (car nodes) 4
                                                                       (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks)
                                                                                                              graph nodeset) marks))))
                                      (:instance temp1.13v2
                                       (node (car nodes))
                                       (subgraph (union-of paths)))
                                      (:instance subsetp-st-filter-2marked-nodes-update-marksi-4
                                       (node (car nodes))
                                       (nodes (st-all-nodes nodeset)))
                                      (:instance spec-of-invariant-comp
                                       (n (nodes-length nodeset))
                                       (i (car nodes)))))
          ("Subgoal *1/4.2.2" :use (;marking of header of path is equal to 3
                                    (:instance temp3.1
                                     (node (car nodes))
                                     (path (car (find-d-path-containing paths dests (car nodes))))
                                     (dest (cadr (find-d-path-containing paths dests (car nodes))))
                                     (marks (update-marksi (car nodes) 4
                                                           (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks)
                                                                                                  graph nodeset) marks))))
                                    (:instance temp21.6
                                     (node (car nodes))
                                     (subgraph (union-of paths)))
                                    (:instance spec-of-invariant-escs2
                                     (n (nodes-length nodeset))
                                     (i (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                     (marks (update-marksi (car nodes) 4
                                                           (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks)
                                                                                                  graph nodeset) marks))))
                                    (:instance spec-of-A-dests-E-2neighbor
                                     (node (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                     (dests (esci (car (last (car (find-d-path-containing paths dests (car nodes)))))
                                                  (update-marksi (car nodes) 4
                                                                 (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks)
                                                                                                        graph nodeset) marks))))
                                     (dest (cadr (find-d-path-containing paths dests (car nodes))))
                                     (marks (update-marksi (car nodes) 4
                                                           (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks)
                                                                                                  graph nodeset) marks))))
                                    (:instance spec-of-invariant-comp
                                     (n (nodes-length nodeset))
                                     (i (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                     (marks (update-marksi (car nodes) 4
                                                           (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks)
                                                                                                  graph nodeset) marks))))
                                    (:instance temp1.13v2
                                     (node (car nodes))
                                     (subgraph (union-of paths)))
                                    (:instance spec-of-invariant-comp
                                       (n (nodes-length nodeset))
                                       (i (car nodes)))))
          ("Subgoal *1/4.2.1" :use (;marking of header of path is equal to 4
                                    (:instance spec-of-invariant-escs2
                                     (n (nodes-length nodeset))
                                     (i (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                     (marks (update-marksi (car nodes) 4
                                                           (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks)
                                                                                                  graph nodeset) marks))))
                                    (:instance spec-of-A-dests-E-2neighbor
                                     (node (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                     (dests (esci (car (last (car (find-d-path-containing paths dests (car nodes)))))
                                                  (update-marksi (car nodes) 4
                                                           (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks)
                                                                                                  graph nodeset) marks))))
                                     (dest (cadr (find-d-path-containing paths dests (car nodes))))
                                     (marks (update-marksi (car nodes) 4
                                                           (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks)
                                                                                                  graph nodeset) marks))))
                                    (:instance spec-of-invariant-comp4
                                     (n (nodes-length nodeset))
                                     (i (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                     (marks (update-marksi (car nodes) 4
                                                           (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks)
                                                                                                  graph nodeset) marks))))
                                    (:instance spec-of-invariant-4marks
                                     (n (nodes-length nodeset))
                                     (i (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                     (marks (update-marksi (car nodes) 4
                                                           (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks)
                                                                                                  graph nodeset) marks))))
                                    (:instance temp1.13v2
                                     (node (car nodes))
                                     (subgraph (union-of paths)))
                                    (:instance subsetp-st-filter-2marked-nodes-update-marksi-4
                                       (node (car nodes))
                                       (nodes (st-all-nodes nodeset)))
                                    (:instance spec-of-invariant-comp
                                       (n (nodes-length nodeset))
                                       (i (car nodes)))
                                    (:instance temp25.4
                                     (a (cadr (find-d-path-containing paths dests (car nodes))))
                                     (x (A-DESTS-OF (CAR NODES) (NEIGHBORSI (CAR NODES) GRAPH) GRAPH NODESET))
                                     (y (depi (car nodes) marks))
                                     (z (esci (car nodes) marks))
                                     (w (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks) graph nodeset)))))


          ("Subgoal *1/8.2" :use ((:instance node-where-dest-leads-to-2marked-nodes-only-is-escape-for-subgraph-of-not2-marked-nodes
                                   (neighbors->destsi (neighbors->destsi (car (last (car (find-d-path-containing paths dests (car nodes))))) graph))
                                   (dest (cadr (find-d-path-containing paths dests (car nodes))))
                                   (subgraph (union-of paths)))
                                  (:instance temp1.11
                                   (node (car nodes)))
                                  (:instance 2marked-node-member-of
                                   (nodes1 (union-of paths))
                                   (nodes2 (st-all-nodes nodeset))
                                   (node (car nodes)))))
          ("Subgoal *1/8.2.2" :use ((:instance temp8.3
                                     (n (nodes-length nodeset))
                                     (i (car (last (car (find-d-path-containing paths dests (car nodes)))))))
                                    (:instance temp21.5
                                     (path (car (find-d-path-containing paths dests (car nodes))))
                                     (dest (cadr (find-d-path-containing paths dests (car nodes)))))
                                    (:instance temp21.4
                                     (path (car (find-d-path-containing paths dests (car nodes))))
                                     (dest (cadr (find-d-path-containing paths dests (car nodes))))))
                              :expand (LEGAL-MARK (MARKSI (car (last (car (find-d-path-containing paths dests (car nodes))))) marks)))
          ("Subgoal *1/8.2.2.4" :use (;marking of header of path is equal to 0
                                      (:instance temp3.1
                                       (node (car nodes))
                                       (path (car (find-d-path-containing paths dests (car nodes))))
                                       (dest (cadr (find-d-path-containing paths dests (car nodes)))))
                                      (:instance temp21.6
                                       (node (car nodes))
                                       (subgraph (union-of paths)))))
          ("Subgoal *1/8.2.2.3" :use (;marking of header of path is equal to 1
                                      (:instance temp3.1
                                       (node (car nodes))
                                       (path (car (find-d-path-containing paths dests (car nodes))))
                                       (dest (cadr (find-d-path-containing paths dests (car nodes)))))
                                      (:instance temp21.6
                                       (node (car nodes))
                                       (subgraph (union-of paths)))))
          ("Subgoal *1/8.2.2.2" :use (;marking of header of path is equal to 3
                                      (:instance temp3.1
                                       (node (car nodes))
                                       (path (car (find-d-path-containing paths dests (car nodes))))
                                       (dest (cadr (find-d-path-containing paths dests (car nodes)))))
                                      (:instance temp21.6
                                       (node (car nodes))
                                       (subgraph (union-of paths)))
                                      (:instance spec-of-invariant-escs2
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests (car nodes)))))))
                                      (:instance spec-of-A-dests-E-2neighbor
                                       (node (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                       (dests (esci (car (last (car (find-d-path-containing paths dests (car nodes))))) marks))
                                       (dest (cadr (find-d-path-containing paths dests (car nodes)))))
                                      (:instance spec-of-invariant-comp
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests (car nodes)))))))
                                      (:instance temp1.13v2
                                       (node (car nodes))
                                       (subgraph (union-of paths)))))
          ("Subgoal *1/8.2.2.1" :in-theory (set-difference-theories
                                            (current-theory :here)
                                            '(spec-of-invariant-comp))
                                :use (;marking of header of path is equal to 4
                                      (:instance spec-of-invariant-escs2
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests (car nodes)))))))
                                      (:instance spec-of-A-dests-E-2neighbor
                                       (node (car (last (car (find-d-path-containing paths dests (car nodes))))))
                                       (dests (esci (car (last (car (find-d-path-containing paths dests (car nodes))))) marks))
                                       (dest (cadr (find-d-path-containing paths dests (car nodes)))))
                                      (:instance spec-of-invariant-comp4
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests (car nodes)))))))
                                      (:instance spec-of-invariant-4marks
                                       (n (nodes-length nodeset))
                                       (i (car (last (car (find-d-path-containing paths dests (car nodes)))))))
                                      (:instance temp1.13v2
                                       (node (car nodes))
                                       (subgraph (union-of paths)))))

           ))

(defthm algo-does-not-alter-3marking
  (let ((marks-after (st-A-nodes-escapable-inv n graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (natp node)
                  (equal (marksi node marks) 3))
             (equal (marksi node marks-after) 3)))
  :hints (("Goal" :in-theory (disable marksi))
          ("Subgoal *1/2" :use ((:instance algo-preserves-3marking
                                 (nodes (list (1- n)))
                                 (prev -1))))))
(defthm algo-does-not-alter-4marking
  (let ((marks-after (st-A-nodes-escapable-inv n graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (natp node)
                  (equal (marksi node marks) 4))
             (equal (marksi node marks-after) 4)))
  :hints (("Goal" :in-theory (disable marksi))
          ("Subgoal *1/2" :use ((:instance algo-preserves-4marking
                                 (nodes (list (1- n)))
                                 (prev -1))))))

(defthm step2-does-not-change-0-markings
  (let ((marks-after (process-escs-eff nodes stack marks graph nodeset)))
    (implies (and (natp i)
                  (equal (marksi i marks) 0))
             (equal (marksi i marks-after) 0)))
  :hints (("Goal" :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi))))
(defthm step2-does-not-change-1-markings
  (let ((marks-after (process-escs-eff nodes stack marks graph nodeset)))
    (implies (and (natp i)
                  (equal (marksi i marks) 1))
             (equal (marksi i marks-after) 1)))
  :hints (("Goal" :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi))))
(defthm step2-does-not-change-2-markings
  (let ((marks-after (process-escs-eff nodes stack marks graph nodeset)))
    (implies (and (natp i)
                  (equal (marksi i marks) 2))
             (equal (marksi i marks-after) 2)))
  :hints (("Goal" :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi))))
(defthm step2-marks-4marked-node-either-2-or-4
  (let ((marks-after (process-escs-eff nodes stack marks graph nodeset)))
    (implies (and (natp i)
                  (equal (marksi i marks) 4)
                  (not (equal (marksi i marks-after) 4)))
             (equal (marksi i marks-after) 2)))
  :hints (("Goal" :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi temp1.16))))
(defthm step2-marks-3marked-node-either-2-or-3-or-4
  (let ((marks-after (process-escs-eff nodes stack marks graph nodeset)))
    (implies (and (natp i)
                  (equal (marksi i marks) 3)
                  (not (equal (marksi i marks-after) 3))
                  (not (equal (marksi i marks-after) 4)))
             (equal (marksi i marks-after) 2)))
  :hints (("Goal" :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi temp1.16))))




(defthm dl->3-or-4-after-algo-inductive
  (let ((marks-after (st-A-nodes-escapable-inv n graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  (A-valid-nodes (st-all-nodes nodeset) nodeset)
                  (natp n)
                  (<= n (nodes-length nodeset))
                  ;; If a node is in a deadlock:
                  (paths-satisfy-condition paths dests (union-of paths) graph nodeset)
                  (st-A-parents (union-of paths) graph)
                  (A-valid-nodes (union-of paths) nodeset)
                  (A-valid-nodes dests nodeset)
                  (member-equal node (union-of paths))
                  (< node n)
                  (natp node)
                  (not (equal (marksi node marks) 1))
                  (legal-mark (marksi node marks))
                  ;; Invariant:
                  (invariant-legal (nodes-length nodeset) marks)
                  (invariant-4marks (nodes-length nodeset) marks)
                  (invariant-2marks (nodes-length nodeset) marks graph)
                  (invariant-comp (nodes-length nodeset) marks graph nodeset)
                  (invariant-escs2 (nodes-length nodeset) marks graph)
                  (not-in (union-of paths) (st-filter-2marked-nodes (st-all-nodes nodeset) marks)))
             ;; Then the node will be marked 3 or 4
             (or (equal (marksi node marks-after) 3)
                 (equal (marksi node marks-after) 4))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable esci depi update-marksi neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi st-escapable-inv legal-mark
                                      step2-marks-3marked-node-either-2-or-3-or-4 temp8.3)
                  :do-not '(eliminate-destructors generalize))
          ("Subgoal *1/17" :expand (legal-mark (marksi (1- n) marks)))
          ("Subgoal *1/12" :use (:instance step1-preserves-dl->not2
                                 (node (1- n))))
          ("Subgoal *1/11" :use ((:instance step1-preserves-invariant-escs2
                                 (node (1- n)))))
          ("Subgoal *1/7" :use (:instance step1-preserves-invariant-legal
                                (nodes (list (1- n)))
                                (prev -1)))
          ("Subgoal *1/6" :use ((:instance temp8.3
                                 (n (nodes-length nodeset))
                                 (i node)
                                 (marks (st-escapable-inv (list (1- n)) -1 graph marks nodeset)))
                                (:instance step1-preserves-invariant-legal
                                 (nodes (list (1- n)))
                                 (prev -1))))
          ("Subgoal *1/5" :use (:instance step1-does-not-mark-nodes-1
                                (node (1- n))
                                (node2 node)))
            ("Subgoal *1/4" :use ((:instance step1-does-not-mark-nodes-1
                                     (node (1- n))
                                     (node2 (1- n)))
                                    (:instance step1-marks-node-123
                                     (node (1- n)))
                                    (:instance step1-preserves-dl->not2
                                     (node (1- n)))
                      ))))


(defthm algo-preserves-dl->not2
  (let* ((marks-after (st-A-nodes-escapable-inv n graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  ;; If there is deadlock:
                  (paths-satisfy-condition paths dests (union-of paths) graph nodeset)
                  (st-A-parents (union-of paths) graph)
                  (A-valid-nodes (union-of paths) nodeset)
                  (A-valid-nodes dests nodeset)
                  ;; Invariant:
                  (invariant-legal (nodes-length nodeset) marks)
                  (invariant-4marks (nodes-length nodeset) marks)
                  (invariant-2marks (nodes-length nodeset) marks graph)
                  (invariant-comp (nodes-length nodeset) marks graph nodeset)
                  (invariant-escs2 (nodes-length nodeset) marks graph)
                  (not-in (union-of paths) (st-filter-2marked-nodes (st-all-nodes nodeset) marks)))
             (not-in (union-of paths) (st-filter-2marked-nodes (st-all-nodes nodeset) marks-after))))
  :hints (("Goal" :do-not '(eliminate-destructors generalize))
          ("Subgoal *1/7" :use (:instance step1-preserves-dl->not2
                                (node (1- n))))
          ("Subgoal *1/6" :use (:instance step1-preserves-invariant-escs2
                                (node (1- n))))
          ("Subgoal *1/5" :use (:instance step1-preserves-invariant-comp
                                (n (nodes-length nodeset))
                                (node (1- n))))
          ("Subgoal *1/2" :use (:instance step1-preserves-invariant-legal
                                (nodes (list (1- n)))
                                (prev -1)))))



(defthm dl->3-or-4-after-algo
  (let ((marks-after (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  (A-valid-nodes (st-all-nodes nodeset) nodeset)
                  (natp n)
                  (<= n (nodes-length nodeset))
                  ;; If there is deadlock:
                  (paths-satisfy-condition paths dests (union-of paths) graph nodeset)
                  (st-A-parents (union-of paths) graph)
                  (A-valid-nodes (union-of paths) nodeset)
                  (A-valid-nodes dests nodeset)
                  (member-equal node (union-of paths))
                  (< node n)
                  (natp node)
                  (not (equal (marksi node marks) 1))
                  (legal-mark (marksi node marks))
                  ;; Invariant:
                  (invariant-legal (nodes-length nodeset) marks)
                  (invariant-4marks (nodes-length nodeset) marks)
                  (invariant-2marks (nodes-length nodeset) marks graph)
                  (invariant-comp (nodes-length nodeset) marks graph nodeset)
                  (invariant-escs2 (nodes-length nodeset) marks graph)
                  (not-in (union-of paths) (st-filter-2marked-nodes (st-all-nodes nodeset) marks)))
             (or (equal (marksi node (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) marks-after nodeset)
                                                               (filter-4marked-nodes (nodes-length nodeset) marks-after nodeset))
                                                       nil
                                                       marks-after graph nodeset))
                        3)
                 (equal (marksi node (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) marks-after nodeset)
                                                               (filter-4marked-nodes (nodes-length nodeset) marks-after nodeset))
                                                       nil
                                                       marks-after graph nodeset))
                        4))))
  :otf-flg t
  :rule-classes nil
  :hints (("Goal" :in-theory (disable esci depi update-marksi neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi st-escapable-inv legal-mark
                                      step2-marks-3marked-node-either-2-or-3-or-4 temp8.3 algo-preserves-dl->not2 nodes-length
                                      step2-marks-4marked-node-either-2-or-4 step2-preserves-dl->not2)
                  :do-not '(eliminate-destructors generalize)
                  :use ((:instance dl->3-or-4-after-algo-inductive
                         (n (nodes-length nodeset)))
                        (:instance step2-marks-3marked-node-either-2-or-3-or-4
                         (nodes (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                        (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)))
                         (i node)
                         (stack nil)
                         (marks (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)))
                        (:instance step2-preserves-dl->not2
                         (nodes (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                        (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)))
                         (stack nil)
                         (marks (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)))
                        (:instance algo-preserves-dl->not2
                         (n (nodes-length nodeset)))
                        (:instance step2-marks-4marked-node-either-2-or-4
                         (nodes (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                        (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)))
                         (stack nil)
                         (i node)
                         (marks (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)))
                         ))))

(defthm A-clear-implies-st-filter-2marked-nodes=nil
  (implies (and (A-clear (nodes-length nodeset) marks)
                (A-valid-nodes nodes nodeset))
           (equal (st-filter-2marked-nodes nodes marks) nil))
  :hints (("Goal" :in-theory (disable marksi))))


(defthm temp12.0
  (implies (and (paths-satisfy-condition paths dests subgraph graph nodeset)
                (consp paths))
           (member-equal (caar paths) (union-of paths))))

(defthm spec-of-filter-4marked-nodes
  (iff (member-equal i (filter-4marked-nodes n marks nodeset))
       (and (natp i)
            (natp n)
            (< i n)
            (equal (nodesi i nodeset) 1)
            (equal (marksi i marks) 4))))
(defthm dl->algo-returns-nil
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (filled-graphp (nodes-length nodeset) graph)
                ;; If there is deadlock:
                (paths-satisfy-condition paths dests (union-of paths) graph nodeset)
                (consp paths)
                (st-A-parents (union-of paths) graph)
                (A-valid-nodes (union-of paths) nodeset)
                (A-valid-nodes dests nodeset)
                ;; Initially:
                (A-clear (nodes-length nodeset) marks))
           (equal (mv-nth 0 (algorithm graph marks nodeset)) nil))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (A-valid-nodes-show-nodeset) (esci depi update-marksi neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi
                                                                     spec-of-filter-3marked-nodes st-escapable-inv legal-mark spec-of-filter-4marked-nodes))
                  :use ((:instance dl->3-or-4-after-algo
                         (node (caar paths))
                         (n (nodes-length nodeset)))
                        (:instance A-clear-implies-st-filter-2marked-nodes=nil
                         (nodes (st-all-nodes nodeset)))
                        (:instance spec-of-filter-3marked-nodes
                         (i (caar paths))
                         (n (nodes-length nodeset))
                         (marks (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                          (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                  nil
                                                  (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                  graph nodeset)))
                        (:instance spec-of-filter-4marked-nodes
                         (i (caar paths))
                         (n (nodes-length nodeset))
                         (marks (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                          (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                  nil
                                                  (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                  graph nodeset)))))))

(in-theory (disable member-valid-nodes->nodesi=1
                    legal-mark (:executable-counterpart legal-mark)
                    step1-preserves-dl->not2
                    step1-preserves-invariant-escs2
                    update-marksi-2-append-escs-preserves-invariant-escs2
                    update-marksi-2-preserves-invariant-escs2
                    update-marksi-2-preserves-A-dests-E-2neighbor
                    step1-preserves-dl->not2-inductive
                    step1-does-not-alter-escs-2marked-nodes
                    step1-does-not-alter-escs-3marked-nodes
                    step1-does-not-alter-deps-2marked-nodes
                    step1-does-not-alter-deps-3marked-nodes))#|ACL2s-ToDo-Line|#

