#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#


(in-package "ACL2")
(include-book "correctness")

;;---------------------------------------
;;---------------------------------------
;; 5.) algorithm returns t --> deadlock
;;---------------------------------------
;;---------------------------------------
;; First we prove that the set of 3-marked ports has no escape (theorems node-in-subgraph-of-3marked-nodes-is-no-escape and subgraph-of-3marked-nodes-has-no-escape).
(defthm update-marksi-update-marksi
  (equal (update-marksi i x (update-marksi i y marks))
         (update-marksi i x marks)))
(defthm A-dests-of-remove
  (subsetp (A-dests-of node (remove-equal x nodes) graph nodeset)
           (A-dests-of node nodes graph nodeset)))
(defthm subsetp-append-r-l
  (implies (subsetp y z)
           (subsetp (append x y)
                    (append x z))))
(defthm neighbors-in-subgraph-implies-no-escape
  (implies (and (member-equal dest dests)
                (subsetp (st-filter-neighbors-for-dest (neighbors->destsi node graph) dest) subgraph))
           (not (st-escapep node subgraph dests graph))))
(defthm rewrite-find-member-not-in
  (implies (not (member-equal nil x))
           (iff (find-member-not-in x y)
                (not (subsetp x y)))))
(defthm spec-of-find-member-not-in-not-member
  (let ((a (find-member-not-in x y)))
    (implies a
             (not (member-equal a y)))))
(defthm spec-of-find-member-not-in-member
  (let ((a (find-member-not-in x y)))
    (implies a
             (member-equal a x))))

(defthm dest-that-leads-not-to-012-marked-nodes-leads-to-34marked-nodes
  (implies (and (natp node)
                (< node (nodes-length nodeset))
                (subsetp neighbors (neighborsi node graph))
                (is-keys-of-alist neighbors neighbors->destsi)
                (subsetp neighbors->destsi (neighbors->destsi node graph))
                (filled-graphp (nodes-length nodeset) graph)
                (valid-graph (nodes-length nodeset) graph nodeset)
                (not (member-equal dest (A-dests-of node (st-filter-unmarked123-nodes neighbors marks ) graph nodeset)))
                (not (member-equal dest (A-dests-of node (st-filter-1marked-nodes neighbors marks) graph nodeset)))
                (not (member-equal dest (A-dests-of node (st-filter-2marked-nodes neighbors marks) graph nodeset))))
           (subsetp (st-filter-neighbors-for-dest neighbors->destsi dest)
                    (append (filter-3marked-nodes (nodes-length nodeset) marks nodeset)
                            (filter-4marked-nodes (nodes-length nodeset) marks nodeset))))
  :hints (("Goal" :in-theory (disable marksi neighbors->destsi neighborsi A-valid-nodes-neighbors))
          ("Subgoal *1/8" :use ((:instance assoc-key-yeilds-field
                                 (key (car neighbors))
                                 (field (car neighbors->destsi))
                                 (alist (neighbors->destsi node graph)))
                                (:instance A-valid-nodes-neighbors
                                 (i node)
                                 (n (nodes-length nodeset)))))))

(defthm 3marked-node-in-subgraph-of-34marked-nodes-is-no-escape
  (implies (and (filled-graphp (nodes-length nodeset) graph)
                (valid-graph (nodes-length nodeset) graph nodeset)
                (st-valid-node node nodeset)
                (equal (marksi node marks) 3)
                (unresolved node marks)
                (equal (st-filter-1marked-nodes (neighborsi node graph) marks) nil)
                (invariant-3marks (nodes-length nodeset) marks graph nodeset)
                (invariant-deps (nodes-length nodeset) marks graph nodeset)
                (invariant-escs-total (nodes-length nodeset) marks graph nodeset))
           (subsetp (st-filter-neighbors-for-dest (neighbors->destsi node graph) (find-member-not-in (depi node marks) (esci node marks)))
                    (append (filter-3marked-nodes (nodes-length nodeset) marks nodeset)
                            (filter-4marked-nodes (nodes-length nodeset) marks nodeset))))
  :otf-flg t
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :in-theory (disable dest-that-leads-not-to-012-marked-nodes-leads-to-34marked-nodes esci depi update-marksi neighborsi dests-of-edge neighbors->destsi append-to-esc
                                      append-to-dep E-d-path-to-013-marked-node spec-of-invariant-escs-total spec-of-find-member-not-in-not-member
                                      nodes-length marksi)
                  :use ((:instance dest-that-leads-not-to-012-marked-nodes-leads-to-34marked-nodes
                         (neighbors (neighborsi node graph))
                         (neighbors->destsi (neighbors->destsi node graph))
                         (dest (find-member-not-in (depi node marks) (esci node marks))))
                        (:instance spec-of-find-member-not-in-not-member
                         (x (depi node marks))
                         (y (esci node marks)))
                        (:instance rewrite-find-member-not-in
                         (x (depi node marks))
                         (y (esci node marks)))
                        (:instance spec-of-invariant-escs-total
                         (n (nodes-length nodeset))
                         (i node))
                        (:instance not-member-nil-depi
                         (n (nodes-length nodeset))
                         (i node))
                        ))))


(defthm neighbors-are-valid-nodes
    (implies (and (valid-graph n graph nodeset)
                  (< i n)
                  (natp i)
                  (natp n))
             (subsetp (neighborsi i graph) (st-all-nodes nodeset))))

(defun-sk E-d-path-to-3mark (node marks graph nodeset)
  (exists (path dest)
          (and (st-d-pathp path dest graph nodeset)
               (st-valid-node dest nodeset)
               (equal (car path) node)
               (equal (marksi (car (last path)) marks) 3)
               (member-equal dest (depi (car (last path)) marks))
               (not (member-equal dest (esci (car (last path)) marks))))))

(defun invariant-4marks-paths (n uncertain marks graph nodeset)
  (cond ((zp n)
         t)
        ((and (not (member-equal (1- n) uncertain))
              (equal (nth (1- n) (nth *nodesi* nodeset)) 1)
              (equal (nth (1- n) (nth *marksi* marks)) 4))
         (and (E-d-path-to-3mark (1- n) marks graph nodeset)
              (invariant-4marks-paths (1- n) uncertain marks graph nodeset)))
        (t
         (invariant-4marks-paths (1- n) uncertain marks graph nodeset))))

(defthm temp13.4
  (equal (nth i (car marks)) (marksi i marks)))
(defthm temp13.5
  (implies (and (equal (marksi i marks) x)
                x)
           (consp marks)))

(in-theory (disable temp13.4 temp13.5))
(defthm temp13.6
  (implies (and (invariant-4marks-paths n uncertain marks graph nodeset)
                (not (equal (marksi (car uncertain) marks) 4)))
           (invariant-4marks-paths n (cdr uncertain) marks graph nodeset))
  :hints (("Goal" :in-theory (disable E-d-path-to-3mark))))
(defthm temp13.8
  (implies (and (E-d-path-to-3mark node marks graph nodeset)
                (not (equal (marksi i marks) 3)))
           (E-d-path-to-3mark node (update-marksi i 2 marks) graph nodeset))
  :hints (("Goal" :use ((:instance E-d-path-to-3mark-suff
                         (path (car (E-d-path-to-3mark-witness node marks graph nodeset)))
                         (dest (mv-nth 1 (E-d-path-to-3mark-witness node marks graph nodeset)))
                         (marks (update-marksi i 2 marks)))))))
(defthm temp13.7
  (implies (and (invariant-4marks-paths n uncertain marks graph nodeset)
                (not (equal (marksi node marks) 3)))
           (invariant-4marks-paths n uncertain (update-marksi node 2 marks) graph nodeset))
  :hints (("Goal" :in-theory (e/d (temp13.4 temp13.5) (marksi E-d-path-to-3mark update-marksi )))))
(defthm temp13.11
  (implies (and (invariant-4marks-paths n uncertain marks graph nodeset)
                (not (equal (marksi node marks) 3)))
           (invariant-4marks-paths n (append x (remove-equal node uncertain)) (update-marksi node 2 marks) graph nodeset))
  :hints (("Goal" :in-theory (e/d (temp13.4 temp13.5) (marksi update-marksi marksi E-d-path-to-3mark)))))
(defthm temp13.12
  (implies (and (invariant-4marks-paths n uncertain marks graph nodeset)
                (equal (marksi node marks) 3))
           (invariant-4marks-paths n (remove-equal node uncertain) marks graph nodeset))
  :hints (("Goal" :in-theory (e/d (temp13.4 temp13.5) (marksi update-marksi marksi E-d-path-to-3mark)))))
(defthm temp13.13
  (implies (and (invariant-4marks-paths n uncertain marks graph nodeset)
                (equal (marksi node marks) 4)
                (E-d-path-to-3mark node marks graph nodeset))
           (invariant-4marks-paths n (remove-equal node uncertain) marks graph nodeset))
  :hints (("Goal" :in-theory (e/d (temp13.4 temp13.5) (marksi update-marksi marksi E-d-path-to-3mark)))))

(defun E-d-path-from-to-all (from tos dest graph nodeset)
  (if (endp tos)
    t
    (and (E-d-path-from-to-not-in from (car tos) nil dest graph nodeset)
         (E-d-path-from-to-all from (cdr tos) dest graph nodeset))))
(defthm temp13.15
  (implies (and (E-d-path-from-to-all from tos dest graph nodeset)
                (member-equal to tos))
           (E-d-path-from-to-not-in from to nil dest graph nodeset)))
(defthm temp13.17
  (equal (E-d-path-from-to-all from (append x y) dest graph nodeset)
         (and (E-d-path-from-to-all from x dest graph nodeset)
              (E-d-path-from-to-all from y dest graph nodeset))))
(defthm st-d-pathp-append
  (implies (and (true-listp p1)
                (true-listp p2))
           (iff (st-d-pathp (append p1 p2) dest graph nodeset)
                (cond ((endp p1) (st-d-pathp p2 dest graph nodeset))
                      ((endp p2) (st-d-pathp p1 dest graph nodeset))
                      (t (and (st-d-pathp p1 dest graph nodeset)
                              (st-d-pathp p2 dest graph nodeset)
                              (member-equal (car p2)
                                            (st-filter-neighbors-for-dest (neighbors->destsi (car (last p1)) graph) dest))))))))
(defthm temp13.19
  (implies (st-d-pathp p dest graph nodeset)
           (true-listp p)))
(defthm temp13.20
  (equal (car (last (append x y)))
         (if (consp y)
           (car (last y))
           (car (last x)))))
(defthm temp13.20.1
  (equal (car (append x y))
         (cond ((consp x)
                (car x))
               ((consp y)
                (car y))
               (t
                nil))))
(defthm temp13.18
  (implies (and (E-d-path-from-to-not-in from to nil dest graph nodeset)
                (A-valid-nodes neighbors nodeset)
                (subsetp neighbors (st-filter-neighbors-for-dest (neighbors->destsi to graph) dest)))
           (E-d-path-from-to-all from neighbors dest graph nodeset))
  :hints (("Subgoal *1/3" :use (:instance E-d-path-from-to-not-in-suff
                                (path (append (E-d-path-from-to-not-in-witness from to nil dest graph nodeset) (list (car neighbors))))
                                (to (car neighbors))
                                (subgraph nil)))))
(defthm temp13.21
  (subsetp (setminus x y) x))
(defthm temp13.22
  (implies (and (E-d-path-from-to-all from tos2 dest graph nodeset)
                (subsetp tos1 tos2))
           (E-d-path-from-to-all from tos1 dest graph nodeset)))
(defun no-01-marks (n st-marks st-nodeset)
  (declare (xargs :stobjs (st-marks st-nodeset)
                  :verify-guards nil))
  (if (zp n)
    t
    (and (or (and (not (equal (marksi (1- n) st-marks) 0))
                  (not (equal (marksi (1- n) st-marks) 1)))
             (not (equal (nodesi (1- n) st-nodeset) 1)))
         (no-01-marks (1- n) st-marks st-nodeset))))
(defthmd temp13.23
  (implies (and (no-01-marks n marks nodeset)
                (natp i)
                (natp n)
                (equal (nodesi i nodeset) 1)
                (< i n))
           (and (not (equal (marksi i marks) 0))
                (not (equal (marksi i marks) 1)))))

(defthmd temp13.14.1
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (filled-graphp (nodes-length nodeset) graph)
                (A-valid-nodes nodes nodeset)
                (st-valid-node dest nodeset)
                (E-d-path-from-to-all from nodes dest graph nodeset)
                (not (equal (st-find-next-d-step nodes to stack dest graph nodeset) 'failure))
                (equal (marksi to marks) 3)
                (member-equal dest (depi to marks))
                (not (member-equal dest (esci to marks))))
           (E-d-path-to-3mark from marks graph nodeset))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :in-theory (disable marksi neighborsi E-d-path-to-3mark))
          ("Subgoal *1/6" :use (:instance temp13.18
                                  (neighbors (st-filter-neighbors-for-dest (neighbors->destsi (car nodes) graph) dest))
                                  (to (car nodes))))))
(defthm temp13.14.3
  (implies (and (subsetp neighbors (st-filter-neighbors-for-dest (neighbors->destsi from graph) dest))
                (A-valid-nodes neighbors nodeset)
                (st-valid-node from nodeset))
           (E-d-path-from-to-all from neighbors dest graph nodeset))
  :hints (("Subgoal *1/3" :use ((:instance E-d-path-from-to-not-in-suff
                                 (to (car neighbors))
                                 (subgraph nil)
                                 (path (list from (car neighbors))))))))

(defthmd temp13.14.2
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (filled-graphp (nodes-length nodeset) graph)
                (no-01-marks (nodes-length nodeset) marks nodeset)
                (natp n)
                (<= n (nodes-length nodeset))
                (st-valid-node from nodeset)
                (st-valid-node dest nodeset)
                (E-013-marked-E-d-path n from dest marks graph nodeset))
           (E-d-path-to-3mark from marks graph nodeset))
  :hints (("Goal" :induct (E-013-marked-E-d-path n from dest marks graph nodeset)
                  :do-not '(eliminate-destructors generalize)
                  :in-theory (disable marksi neighborsi E-d-path-to-3mark nodesi))
          ("Subgoal *1/2" :use ((:instance temp13.23
                                 (n (nodes-length nodeset))
                                 (i (1- n)))
                                (:instance E-d-path-to-3mark-suff
                                 (path (list (1- n)))
                                 (node (1- n)))
                                (:instance temp13.14.1
                                 (to (1- n))
                                 (nodes (st-filter-neighbors-for-dest (neighbors->destsi from graph) dest))
                                 (stack (list from)))))))

(defthmd temp13.14.4
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (filled-graphp (nodes-length nodeset) graph)
                (no-01-marks (nodes-length nodeset) marks nodeset)
                (st-valid-node from nodeset)
                (<= n (nodes-length nodeset))
                (E-d-E-d-path-to-013-marked-node n from marks graph nodeset))
           (E-d-path-to-3mark from marks graph nodeset))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :in-theory (disable marksi neighborsi E-d-path-to-3mark))
          ("Subgoal *1/2" :use (:instance temp13.14.2
                                (n (nodes-length nodeset))
                                (dest (1- n))))))

(defthmd temp13.14
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (filled-graphp (nodes-length nodeset) graph)
                (no-01-marks (nodes-length nodeset) marks nodeset)
                (st-valid-node from nodeset)
                (E-d-path-to-013-marked-node from marks graph nodeset))
           (E-d-path-to-3mark from marks graph nodeset))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :in-theory (disable marksi neighborsi E-d-path-to-3mark)
                  :use ((:instance temp13.14.4
                         (n (nodes-length nodeset)))))))

(defthm temp13.24
  (equal (no-01-marks n (append-to-esc i x marks) nodeset)
         (no-01-marks n marks nodeset)))
(defthm temp13.25
  (implies (natp j)
           (equal (no-01-marks n (update-marksi j y (append-to-esc i x marks)) nodeset)
                  (no-01-marks n (update-marksi j y marks) nodeset)))
  :hints (("Goal" :in-theory (disable marksi update-esci update-marksi))))
(defthm temp13.26
  (implies (and (natp i)
                (no-01-marks n marks nodeset))
           (no-01-marks n (update-marksi i 2 marks) nodeset)))
(defthm temp13.27
  (implies (and (natp i)
                (no-01-marks n marks nodeset))
           (no-01-marks n (update-marksi i 4 marks) nodeset)))


(defthm temp13.28.1
  (implies (and (natp i)
                (natp j))
           (equal (nth i (car (update-marksi j x marks)))
                  (if (equal i j)
                    x
                    (nth i (car marks))))))

(defun st-pathp (path st-graph st-nodeset)
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
              (member-equal (cadr path) (neighborsi (car path) st-graph))
              (st-pathp (cdr path) st-graph st-nodeset)))))
(defun-sk E-path-from-to-not-in (from to subgraph graph nodeset)
  (exists (path)
          (and (st-pathp path graph nodeset)
               (not-in path subgraph)
               (equal (car path) from)
               (equal (car (last path)) to))))
(defun E-path-from-to-all (from tos graph nodeset)
  (if (endp tos)
    t
    (and (E-path-from-to-not-in from (car tos) nil graph nodeset)
         (E-path-from-to-all from (cdr tos) graph nodeset))))
(defthm st-pathp-append
  (implies (and (true-listp p1)
                (true-listp p2))
           (iff (st-pathp (append p1 p2) graph nodeset)
                (cond ((endp p1) (st-pathp p2 graph nodeset))
                      ((endp p2) (st-pathp p1 graph nodeset))
                      (t (and (st-pathp p1 graph nodeset)
                              (st-pathp p2 graph nodeset)
                              (member-equal (car p2)
                                            (neighborsi (car (last p1)) graph))))))))
(defthm temp20.6
  (implies (st-pathp p graph nodeset)
           (true-listp p)))
(defthm temp14.1
  (implies (st-pathp path graph nodeset)
           (st-valid-node (car (last path)) nodeset)))
(defthm temp20.5
  (implies (and (E-path-from-to-not-in from to nil graph nodeset)
                (A-valid-nodes neighbors nodeset)
                (subsetp neighbors (neighborsi to graph)))
           (E-path-from-to-all from neighbors graph nodeset))
  :hints (("Subgoal *1/3" :use (:instance E-path-from-to-not-in-suff
                                (path (append (E-path-from-to-not-in-witness from to nil graph nodeset) (list (car neighbors))))
                                (to (car neighbors))
                                (subgraph nil)))))
(defthm temp20.4
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (E-path-from-to-all from nodes graph nodeset))
           (st-find-next-step nodes to stack graph nodeset))
  :hints (("Goal" :in-theory (disable E-path-from-to-not-in))
          ("Subgoal *1/10.1" :use (:instance temp20.5
                                   (to (car nodes))
                                   (neighbors (neighborsi (car nodes) graph))))))


(defthm temp14.0
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (natp n)
                (natp from)
                (< from n)
                (< from (nodes-length nodeset))
                (E-path-from-to-not-in from to nil graph nodeset)
                (equal (nodesi from nodeset) 1)
                (equal (marksi from marks) 4)
                (not (equal from to)))
           (member-equal from (upwards-4marked-reach n to marks graph nodeset)))
  :hints (("Goal" :in-theory (disable E-path-from-to-not-in))
          ("Subgoal *1/3.10" :use ((:instance temp20.4
                                 (stack (list from))
                                 (nodes (neighborsi from graph)))
                                (:instance temp20.5
                                 (to from)
                                 (neighbors (neighborsi from graph)))
                                (:instance E-path-from-to-not-in-suff
                                 (to from)
                                 (path (list from))
                                 (subgraph nil))))))
(defthmd temp13.28.3
  (implies (and (filled-graphp n graph)
                (natp n)
                (natp node)
                (< node n)
                (member-equal neighbor (st-filter-neighbors-for-dest (neighbors->destsi node graph) dest)))
           (member-equal neighbor (neighborsi node graph))))
(defthm temp13.28.2
  (implies (and (filled-graphp (nodes-length nodeset) graph)
                (st-d-pathp path dest graph nodeset))
           (st-pathp path graph nodeset))
  :hints (("Subgoal *1/8" :use (:instance temp13.28.3
                                (n (nodes-length nodeset))
                                (node (car path))
                                (neighbor (cadr path))))))
#|
(defthm temp13.28
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (filled-graphp (nodes-length nodeset) graph)
                (invariant-4marks-paths n uncertain marks graph nodeset)
                (natp n)
                (<= n (nodes-length nodeset))
                (st-valid-node node nodeset)
                (equal (marksi node marks) 3)
                (E-d-path-to-3mark node (update-marksi node 4 marks) graph nodeset))
           (invariant-4marks-paths n (append (upwards-4marked-reach (nodes-length nodeset) node (update-marksi node 4 marks) graph nodeset) (remove-equal node uncertain))
                                   (update-marksi node 4 marks) graph nodeset))
  :hints (("Goal" :in-theory (disable E-d-path-to-3mark neighborsi temp21.4 update-marksi E-path-from-to-not-in)
                  :do-not '(eliminate-destructors generalize))
          ("Subgoal *1/6" :expand (E-d-path-to-3mark (1- n) marks graph nodeset)
                          :use (
                                (:instance E-d-path-to-3mark-suff
                                 (path (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset)))
                                 (dest (mv-nth 1 (E-d-path-to-3mark-witness (1- n) marks graph nodeset)))
                                 (node (1- n))
                                 (marks (update-marksi node 4 marks)))
                                (:instance temp21.4
                                 (path (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset)))
                                 (dest (mv-nth 1 (E-d-path-to-3mark-witness (1- n) marks graph nodeset))))
                                (:instance temp14.0
                                 (n (nodes-length nodeset))
                                 (from (1- n))
                                 (to (car (last (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset)))))
                                 (marks (update-marksi (car (last (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset)))) 4 marks)))
                                (:instance E-path-from-to-not-in-suff
                                 (path (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset)))
                                 (from (1- n))
                                 (to (car (last (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset)))))
                                 (subgraph nil))))))
|#


(defthm temp13.29
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (filled-graphp (nodes-length nodeset) graph)
                (invariant-4marks-paths n uncertain marks graph nodeset)
                (natp n)
                (<= n (nodes-length nodeset))
                (st-valid-node node nodeset)
                (not (equal (marksi node marks) 3)))
           (invariant-4marks-paths n (append (st-filter-3parents node (nodes-length nodeset) marks graph nodeset) (remove-equal node uncertain))
                                   (update-marksi node 2 marks) graph nodeset))
  :hints (("Goal" :in-theory (disable E-d-path-to-3mark neighborsi temp21.4 update-marksi E-path-from-to-not-in))))
(defthm temp26.1
  (implies (and (not (equal (marksi i marks) 3))
                (natp i)
                (E-d-path-to-3mark node marks graph nodeset))
           (E-d-path-to-3mark node (append-to-esc i x marks) graph nodeset))
  :hints (("Goal" :use (:instance E-d-path-to-3mark-suff
                        (path (car (E-d-path-to-3mark-witness node marks graph nodeset)))
                        (dest (mv-nth 1 (E-d-path-to-3mark-witness node marks graph nodeset)))
                        (marks (append-to-esc i x marks))))))
(defthm temp26.0
  (implies (and (invariant-4marks-paths n uncertain marks graph nodeset)
                (natp node)
                (not (equal (marksi node marks) 3)))
           (invariant-4marks-paths n uncertain (append-to-esc node x marks) graph nodeset))
  :hints (("Goal" :in-theory (e/d (temp13.4 temp13.5) ( E-d-path-to-3mark marksi append-to-esc)))))

#|
          ("Subgoal *1/6" :expand (E-d-path-to-3mark (1- n) marks graph nodeset)
                          :use ((:instance E-d-path-to-3mark-suff
                                 (path (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset)))
                                 (dest (mv-nth 1 (E-d-path-to-3mark-witness (1- n) marks graph nodeset)))
                                 (node (1- n))
                                 (marks (update-marksi node 2 marks)))
                                (:instance temp21.4
                                 (path (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset)))
                                 (dest (mv-nth 1 (E-d-path-to-3mark-witness (1- n) marks graph nodeset))))
                                (:instance temp14.0
                                 (n (nodes-length nodeset))
                                 (from (1- n))
                                 (to (car (last (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset)))))
                                 (marks (update-marksi (car (last (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset)))) 2 marks)))
                                (:instance E-path-from-to-not-in-suff
                                 (path (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset)))
                                 (from (1- n))
                                 (to (car (last (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset)))))
                                 (subgraph nil))
                                 ))))
|#

(in-theory (disable temp13.28.1))



(defthm temp26.3
  (implies (and (filled-graphp (nodes-length nodeset) graph)
                (E-d-path-to-3mark node marks graph nodeset)
                (not (E-d-path-to-3mark node (append-to-esc to x marks) graph nodeset))
                (natp to))
           (E-path-from-to-not-in node to nil graph nodeset))
  :hints (("Goal" :in-theory (disable E-d-path-to-3mark esci marksi depi append-to-esc)
                  :expand (E-d-path-to-3mark node marks graph nodeset)
                  :use ((:instance E-path-from-to-not-in-suff
                         (from node)
                         (subgraph nil)
                         (path (car (E-d-path-to-3mark-witness node marks graph nodeset))))))))

(defthm temp26.2
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (filled-graphp (nodes-length nodeset) graph)
                (<= n (nodes-length nodeset))
                (natp node)
                (equal (marksi node marks) 3)
                (invariant-4marks-paths n uncertain marks graph nodeset))
           (invariant-4marks-paths n
                                   (append (upwards-4marked-reach (nodes-length nodeset) node marks graph nodeset) (remove-equal node uncertain))
                                   (append-to-esc node x marks) graph nodeset))
  :hints (("Goal" :in-theory (e/d (temp13.4 temp13.5) (E-d-path-to-3mark marksi append-to-esc temp26.3 E-path-from-to-not-in)))
          ("Subgoal *1/5" :use ((:instance temp26.3
                                 (to node)
                                 (node (1- n)))
                                (:instance temp14.0
                                 (from (1- n))
                                 (to node)
                                 (n (nodes-length nodeset)))))))

(defthm temp26.5
  (implies (and (filled-graphp (nodes-length nodeset) graph)
                (E-d-path-to-3mark node marks graph nodeset)
                (not (E-d-path-to-3mark node (update-marksi to 2 marks) graph nodeset))
                (natp to))
           (E-path-from-to-not-in node to nil graph nodeset))
  :hints (("Goal" :in-theory (disable  E-d-path-to-3mark esci marksi depi update-marksi temp1.16)
                  :expand (E-d-path-to-3mark node marks graph nodeset)
                  :use ((:instance E-path-from-to-not-in-suff
                         (from node)
                         (subgraph nil)
                         (path (car (E-d-path-to-3mark-witness node marks graph nodeset))))))))

(defthm temp26.4
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (filled-graphp (nodes-length nodeset) graph)
                (invariant-4marks-paths n uncertain marks graph nodeset)
                (natp n)
                (<= n (nodes-length nodeset))
                (st-valid-node node nodeset)
                (equal (marksi node marks) 3))
           (invariant-4marks-paths n (append (st-filter-3parents node (nodes-length nodeset) marks graph nodeset)
                                             (upwards-4marked-reach (nodes-length nodeset) node marks graph nodeset)
                                             (remove-equal node uncertain))
                                   (update-marksi node 2 (append-to-esc node x marks)) graph nodeset))
  :hints (("Goal" :in-theory (e/d (temp13.4 temp13.5) (E-d-path-to-3mark marksi neighborsi temp21.4 update-marksi append-to-esc E-path-from-to-not-in)))
          ("Subgoal *1/6" :use ((:instance temp26.3
                                 (to node)
                                 (node (1- n)))
                                (:instance temp14.0
                                 (from (1- n))
                                 (to node)
                                 (n (nodes-length nodeset)))))))
(defthm temp26.8
  (implies (and (filled-graphp (nodes-length nodeset) graph)
                (E-d-path-to-3mark node marks graph nodeset)
                (not (E-d-path-to-3mark node (update-marksi to 4 (append-to-esc to x marks)) graph nodeset))
                (natp to))
           (E-path-from-to-not-in node to nil graph nodeset))
  :hints (("Goal" :in-theory (disable  E-d-path-to-3mark esci marksi depi update-marksi append-to-esc temp1.16)
                  :expand (E-d-path-to-3mark node marks graph nodeset)
                  :use ((:instance E-path-from-to-not-in-suff
                         (from node)
                         (subgraph nil)
                         (path (car (E-d-path-to-3mark-witness node marks graph nodeset))))))))

(defthm temp26.7
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (filled-graphp (nodes-length nodeset) graph)
                (invariant-4marks-paths n uncertain marks graph nodeset)
                (natp n)
                (<= n (nodes-length nodeset))
                (st-valid-node node nodeset)
                (equal (marksi node marks) 3)
                (E-d-path-to-3mark node (update-marksi node 4 (append-to-esc node x marks)) graph nodeset))
           (invariant-4marks-paths n (append (upwards-4marked-reach (nodes-length nodeset) node (update-marksi node 4 marks) graph nodeset) (remove-equal node uncertain))
                                   (update-marksi node 4 (append-to-esc node x marks)) graph nodeset))
  :hints (("Goal" :in-theory (e/d (temp13.4 temp13.5) (E-d-path-to-3mark marksi neighborsi temp21.4 update-marksi append-to-esc E-path-from-to-not-in))
                  :do-not '(eliminate-destructors generalize))
          ("Subgoal *1/6.3" :use ((:instance temp26.8
                                 (to node)
                                 (node (1- n)))
                                (:instance temp14.0
                                 (from (1- n))
                                 (to node)
                                 (marks (update-marksi node 4 (append-to-esc node x marks)))
                                 (n (nodes-length nodeset)))))))

(defthm temp13.00
  (let* ((marks-after (process-escs-eff nodes stack marks graph nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  (A-valid-nodes nodes nodeset)
                  (no-01-marks (nodes-length nodeset) marks nodeset)
                  (<= n (nodes-length nodeset))
                  ;; Invariant
                  (A-consp stack)
                  (invariant-4marks-paths n nodes marks graph nodeset))
             (invariant-4marks-paths n nil marks-after graph nodeset)))
  :hints (("Goal" :induct (process-escs-eff nodes stack marks graph nodeset)
                  :do-not '(eliminate-destructors generalize)
                  :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi E-d-path-to-3mark E-d-path-from-to-not-in
                                      ))
          ("Subgoal *1/7" :use ((:instance temp13.13
                                 (n (nodes-length nodeset))
                                 (node (car nodes))
                                 (uncertain nodes))
                                (:instance temp13.14
                                 (from (car nodes)))))
          ("Subgoal *1/4" :use (:instance temp26.4
                                (x (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks) graph nodeset))
                                (uncertain nodes)
                                (node (car nodes))))
          ("Subgoal *1/3.2" :use ((:instance temp26.7
                                   (x (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks) graph nodeset))
                                   (uncertain nodes)
                                   (node (car nodes)))
                                  (:instance temp13.14
                                   (from (car nodes))
                                   (marks (update-marksi (car nodes) 4 (append-to-esc (car nodes)
                                          (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks) graph nodeset) marks)
))
)))))




(defun-sk E-paths-that-satisfy-condition (graph nodeset)
  (exists (paths dests)
          (and (consp paths)
               (A-valid-nodes dests nodeset)
               (st-A-parents (union-of paths) graph)
               (paths-satisfy-condition paths dests (union-of paths) graph nodeset))))
(set-irrelevant-formals-ok t)
(defun-nx create-paths-witness-from-34markings (n marks graph nodeset)
  (cond ((zp n)
         nil)
        ((and (equal (nth (1- n) (nth *nodesi* nodeset)) 1)
              (equal (nth (1- n) (nth *marksi* marks)) 4))
         (cons (mv-nth 0 (E-d-path-to-3mark-witness (1- n) marks graph nodeset))
               (create-paths-witness-from-34markings (1- n) marks graph nodeset)))
        ((equal (nth (1- n) (nth *marksi* marks)) 3)
         (cons (list (1- n))
               (create-paths-witness-from-34markings (1- n) marks graph nodeset)))
        (t
         (create-paths-witness-from-34markings (1- n) marks graph nodeset))))
(defun-nx create-dests-witness-from-34markings (n marks graph nodeset)
  (cond ((zp n)
         nil)
        ((and (equal (nth (1- n) (nth *nodesi* nodeset)) 1)
              (equal (nth (1- n) (nth *marksi* marks)) 4))
         (cons (mv-nth 1 (E-d-path-to-3mark-witness (1- n) marks graph nodeset))
               (create-dests-witness-from-34markings (1- n) marks graph nodeset)))
        ((equal (nth (1- n) (nth *marksi* marks)) 3)
         (cons (find-member-not-in (depi (1- n) marks) (esci (1- n) marks))
               (create-dests-witness-from-34markings (1- n) marks graph nodeset)))
        (t
         (create-dests-witness-from-34markings (1- n) marks graph nodeset))))


(defthmd temp14.2
  (implies (and (equal (st-filter-1marked-nodes nodes marks) nil)
                (member-equal node nodes))
           (not (equal (marksi node marks) 1))))
(defthm temp14.3
  (equal (subsetp nodes (st-all-nodes nodeset))
         (A-valid-nodes nodes nodeset)))

(defthm 3marked-node-in-subgraph-of-34marked-nodes-is-no-escape-dest
  (implies (and (filled-graphp (nodes-length nodeset) graph)
                (valid-graph (nodes-length nodeset) graph nodeset)
                (st-valid-node node nodeset)
                (equal (marksi node marks) 3)
                (member-equal dest (depi node marks))
                (not (member-equal dest (esci node marks)))
                (equal (st-filter-1marked-nodes (neighborsi node graph) marks) nil)
                (invariant-3marks (nodes-length nodeset) marks graph nodeset)
                (invariant-deps (nodes-length nodeset) marks graph nodeset)
                (invariant-escs-total (nodes-length nodeset) marks graph nodeset))
           (subsetp (st-filter-neighbors-for-dest (neighbors->destsi node graph) dest)
                    (append (filter-3marked-nodes (nodes-length nodeset) marks nodeset)
                            (filter-4marked-nodes (nodes-length nodeset) marks nodeset))))
  :otf-flg t
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :in-theory (disable dest-that-leads-not-to-012-marked-nodes-leads-to-34marked-nodes esci depi update-marksi neighborsi dests-of-edge neighbors->destsi append-to-esc
                                      append-to-dep E-d-path-to-013-marked-node spec-of-invariant-escs-total spec-of-find-member-not-in-not-member
                                      nodes-length marksi)
                  :use ((:instance dest-that-leads-not-to-012-marked-nodes-leads-to-34marked-nodes
                         (neighbors (neighborsi node graph))
                         (neighbors->destsi (neighbors->destsi node graph)))
                        (:instance spec-of-invariant-escs-total
                         (n (nodes-length nodeset))
                         (i node))
                        (:instance not-member-nil-depi
                         (n (nodes-length nodeset))
                         (i node))
                        ))))

(defthm temp14.00
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (filled-graphp (nodes-length nodeset) graph)
                (natp n)
                (<= n (nodes-length nodeset))
                (invariant-escs-total (nodes-length nodeset) marks graph nodeset)
                (invariant-3marks (nodes-length nodeset) marks graph nodeset)
                (invariant-deps (nodes-length nodeset) marks graph nodeset)
                (not (st-filter-1marked-nodes (st-all-nodes nodeset) marks))
                (invariant-unresolved (nodes-length nodeset) marks graph nodeset)
                (invariant-4marks-paths n nil marks graph nodeset))
           (paths-satisfy-condition (create-paths-witness-from-34markings n marks graph nodeset)
                                    (create-dests-witness-from-34markings n marks graph nodeset)
                                    (append (filter-3marked-nodes (nodes-length nodeset) marks nodeset) (filter-4marked-nodes (nodes-length nodeset) marks nodeset))
                                    graph nodeset))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :induct (create-paths-witness-from-34markings n marks graph nodeset)
                  :in-theory (disable esci depi temp14.1 temp21.4 temp9.2 neighborsi spec-of-find-member-not-in-member))
          ("Subgoal *1/3" :use ((:instance 3marked-node-in-subgraph-of-34marked-nodes-is-no-escape
                                 (node (1- n)))
                                (:instance spec-of-invariant-unresolved
                                 (n (nodes-length nodeset))
                                 (node (1- n)))
                                (:instance temp14.3
                                 (nodes (neighborsi (1- n) graph)))
                                (:instance spec-of-invariant-3marks-valid-nodes
                                 (n (nodes-length nodeset))
                                 (i (1- n)))
                                (:instance spec-of-invariant-deps
                                 (n (nodes-length nodeset))
                                 (i (1- n)))
                                (:instance spec-of-find-member-not-in-member
                                 (x (depi (1- n) marks))
                                 (y (esci (1- n) marks)))
                                (:instance not-member-nil-depi
                                 (n (nodes-length nodeset))
                                 (i (1- n)))
                                (:instance labels-in-graph-subset-A-dests-of
                                 (node (1- n))
                                 (neighbors (neighborsi (1- n) graph))
                                 (neighbors->destsi (neighbors->destsi (1- n) graph)))
                                (:instance neighbors-are-keys-of-neighbors->destsi
                                 (n (nodes-length nodeset))
                                 (node (1- n)))
                                (:instance nodups-keys-neighbors->destsi
                                 (n (nodes-length nodeset))
                                 (node (1- n)))))
          ("Subgoal *1/2" :use ((:instance 3marked-node-in-subgraph-of-34marked-nodes-is-no-escape-dest
                                 (node (car (last (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset)))))
                                 (dest (mv-nth 1 (E-d-path-to-3mark-witness (1- n) marks graph nodeset))))
                                (:instance temp14.3
                                 (nodes (neighborsi (car (last (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset)))) graph)))
                                (:instance temp14.1
                                 (path (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset))))
                                (:instance spec-of-invariant-deps
                                 (n (nodes-length nodeset))
                                 (i (car (last (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset))))))
                                (:instance not-member-nil-depi
                                 (n (nodes-length nodeset))
                                 (i (car (last (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset))))))
                                (:instance labels-in-graph-subset-A-dests-of
                                 (node (car (last (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset)))))
                                 (neighbors (neighborsi (car (last (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset)))) graph))
                                 (neighbors->destsi (neighbors->destsi (car (last (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset)))) graph)))
                                (:instance neighbors-are-keys-of-neighbors->destsi
                                 (n (nodes-length nodeset))
                                 (node (car (last (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset))))))
                                (:instance nodups-keys-neighbors->destsi
                                 (n (nodes-length nodeset))
                                 (node (car (last (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset))))))))
          ))


(defthm temp14.4
  (implies (<= n (nodes-length nodeset))
           (invariant-4marks-paths n (append (filter-3marked-nodes (nodes-length nodeset) marks nodeset) (filter-4marked-nodes (nodes-length nodeset) marks nodeset)) marks graph nodeset)))
(defthmd temp14.6
  (implies (and (equal (marksi node marks) 1)
                (member-equal node nodes))
           (member-equal node (st-filter-1marked-nodes nodes marks))))
(defthmd step1-leaves-no-0markings
  (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                (A-valid-nodes nodes nodeset)
                (natp prev)
                (natp node)
                (equal (marksi node (st-escapable-inv nodes prev  graph marks nodeset)) 0))
           (equal (marksi node marks) 0))
  :hints (("Goal" :in-theory (disable esci depi update-marksi neighborsi update-depi update-esci marksi dests-of-edge update-marksi valid-graph)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset)
                  :do-not '(eliminate-destructors generalize))))
(defthmd step1-does-not-mark-nodes-0
  (let* ((marks-after (st-escapable-inv (list node) -1 graph marks nodeset)))
    (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                  (natp node)
                  (natp node2)
                  (equal (marksi node2 marks-after) 0))
           (equal (marksi node2 marks) 0)))
  :hints (("Goal" :in-theory (disable esci depi update-marksi neighborsi update-depi update-esci marksi dests-of-edge update-marksi valid-graph temp1.16)
                  :expand (st-escapable-inv (list node) -1 graph marks nodeset)
                  :use ((:instance step1-leaves-no-0markings
                         (node node2)
                         (nodes (neighborsi node graph))
                         (prev node)
                         (marks (update-marksi node 1 marks)))))))
(defthm temp14.8
  (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                (natp node)
                (equal (marksi node (st-A-nodes-escapable-inv n graph marks nodeset)) 0))
           (equal (marksi node marks) 0))
  :hints (("Goal" :in-theory (disable marksi st-escapable-inv nodesi))
          ("Subgoal *1/3" :use (:instance step1-does-not-mark-nodes-0
                                (node (1- n))
                                (node2 node)))))

(defthmd step1-marks-0node-not0
  (let* ((marks-after (st-escapable-inv (list node) -1 graph marks nodeset)))
    (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                  (st-valid-node node nodeset))
             (not (equal (marksi node marks-after) 0))))
  :hints (("Goal" :in-theory (e/d (A-valid-nodes-show-nodeset) (esci depi update-marksi neighborsi update-depi update-esci marksi dests-of-edge update-marksi valid-graph temp1.16))
                  :expand (st-escapable-inv (list node) -1 graph marks nodeset))))

(defthm temp14.7
  (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                (natp n)
                (<= n (nodes-length nodeset))
                (natp node)
                (< node n)
                (equal (nodesi node nodeset) 1))
           (not (equal (marksi node (st-A-nodes-escapable-inv n graph marks nodeset)) 0)))
  :hints (("Goal" :in-theory (disable marksi st-escapable-inv nodesi))
          ("Subgoal *1/8" :use (:instance temp14.8
                                (node (1- n))
                                (n (1- n))))
          ("Subgoal *1/4" :use ((:instance temp14.8
                                 (node (1- n))
                                 (n (1- n))
                                 (marks (st-escapable-inv (list (1- n)) -1 graph marks nodeset)))
                                (:instance step1-marks-0node-not0
                                 (node (1- n)))))))

(defthm temp14.5
  (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                (<= n (nodes-length nodeset))
                (equal (st-filter-1marked-nodes (st-all-nodes nodeset) marks) nil))
           (no-01-marks n (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
  :hints (("Goal" :in-theory (disable marksi st-escapable-inv)
                  :do-not '(eliminate-destructors generalize))
          ("Subgoal *1/4.2" :use ((:instance algo-preserves-st-filter-1marked-nodes=nil
                                   (nodes (st-all-nodes nodeset))
                                   (n (nodes-length nodeset))
                                   (st-nodeset nodeset))
                                  (:instance temp14.6
                                   (nodes (st-all-nodes nodeset))
                                   (node (1- n))
                                   (marks (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)))))
          ("Subgoal *1/4.4" :use (:instance temp14.7
                                  (node (1- n))
                                  (n (nodes-length nodeset))))))

(defthm temp14.77
  (implies (and (subsetp subgraph1 subgraph2)
                (paths-satisfy-condition paths dests subgraph1 graph nodeset))
           (paths-satisfy-condition paths dests subgraph2 graph nodeset)))


(defthm temp14.66
  (implies (invariant-4marks-paths n nil marks graph nodeset)
           (subsetp (append (filter-3marked-nodes n marks nodeset) (filter-4marked-nodes n marks nodeset))
                    (union-of (create-paths-witness-from-34markings n marks graph nodeset)))))
(defthm temp14.88
  (implies (and (natp n)
                (equal (marksi node marks) 4)
                (st-valid-node node nodeset)
                (< node n))
            (consp (create-paths-witness-from-34markings n marks graph nodeset))))
(defthm temp14.9
  (implies (and (natp n)
                (equal (marksi node marks) 3)
                (st-valid-node node nodeset)
                (< node n))
            (consp (create-paths-witness-from-34markings n marks graph nodeset))))
(defthm temp14.11
  (equal (st-A-parents (append x y) graph)
         (and (st-A-parents x graph)
              (st-A-parents y graph))))
(defthm temp14.12
  (implies (and (st-pathp path graph nodeset)
                (consp (neighborsi (car (last path)) graph)))
           (st-A-parents path graph)))
(defthm temp14.10
  (implies (and (filled-graphp (nodes-length nodeset) graph)
                (invariant-4marks-paths n nil marks graph nodeset)
                (invariant-3marks (nodes-length nodeset) marks graph nodeset)
                (<= n (nodes-length nodeset)))
           (st-A-parents (union-of (create-paths-witness-from-34markings n marks graph nodeset)) graph))
  :hints (("Subgoal *1/7" :use (:instance spec-of-invariant-3marks-parent
                                 (n (nodes-length nodeset))
                                 (i (1- n))))
          ("Subgoal *1/4" :use ((:instance temp14.12
                                 (path (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset))))
                                (:instance spec-of-invariant-3marks-parent
                                 (n (nodes-length nodeset))
                                 (i (car (last (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset))))))
                                (:instance temp14.1
                                 (path (car (E-d-path-to-3mark-witness (1- n) marks graph nodeset))))))))

(defthmd temp22.0.1
  (implies (and (A-valid-nodes nodes nodeset)
                (member-equal node nodes))
           (st-valid-node node nodeset)))

(defthm temp22.0
  (implies (and (invariant-deps n marks graph nodeset)
                (invariant-unresolved n marks graph nodeset)
                (invariant-4marks-paths n nil marks graph nodeset))
           (A-valid-nodes (create-dests-witness-from-34markings n marks graph nodeset) nodeset))
  :hints (("Goal" :in-theory (disable neighborsi nodesi spec-of-find-member-not-in-member))
          ("Subgoal *1/9" :use ((:instance spec-of-find-member-not-in-member
                                 (x (depi (1- n) marks))
                                 (y (esci (1- n) marks)))
                                (:instance temp22.0.1
                                 (node (find-member-not-in (depi (1- n) marks) (esci (1- n) marks)))
                                 (nodes (depi (1- n) marks)))))))
;; If:
;; 1.) after termination of the algorithm there are still unresolved dependencies
;; 2.) after postprocessing the node is still marked 3
;; then we can construct a deadlock.
;; This deadlock consists of all the nodes that are still marked 3 after postprocessing.
;; The proof results from the invariants: after termination of both the algorithm and the post-processing, the invariants will hold.
;; By invariant-unresolved, for each 3-marked node there is a d in dep, but not in esc. this d leads only to other 3-marked nodes:
;; it can't lead to a 0 or 1-marked node, since there aren't any. It can't lead to a 2 marked node, since by invariant-escs-total,
;; this would imply that it is also in escs.
;; Thus none of the 3-marked nodes is an escape (lemma subgraph-of-3marked-nodes-has-no-escape) for the set of 3marked nodes: they all contain a destination that
;; leads to 3-marked nodes only.
(defthm dlf->not3
  (let* ((marks-after (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset))
         (marks-after-pp (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) marks-after nodeset)
                                                   (filter-4marked-nodes (nodes-length nodeset) marks-after nodeset))
                                           nil
                                           marks-after graph nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  (A-valid-nodes (show-nodeset (nodes-length nodeset) nodeset) nodeset)
                  ;; If all subgraphs have an escape:
                  (not (E-paths-that-satisfy-condition graph nodeset))
                  ;; Invariant:
                  (not (st-filter-1marked-nodes (st-all-nodes nodeset) marks))
                  (invariant-unresolved (nodes-length nodeset) marks graph nodeset)
                  (invariant-3marks (nodes-length nodeset) marks graph nodeset)
                  (invariant-deps (nodes-length nodeset) marks graph nodeset)
                  ;; Then any valid node:
                  (natp node)
                  (< node (nodes-length nodeset))
                  (equal (nodesi node nodeset) 1))
                  ;; Will not get marked 3 or 4:
             (and (not (equal (marksi node marks-after-pp) 3))
                  (not (equal (marksi node marks-after-pp) 4)))))
  :otf-flg t
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :do-not-induct t
                  :in-theory (disable esci depi update-marksi neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi st-escapable-inv st-filter-1marked-nodes-update-marksi-3
                                      st-A-subgraphs-E-escape step1-marks-all-nodes-in-parameter-1 no-01-marks E-paths-that-satisfy-condition temp14.4 temp14.66 temp14.77 temp14.5)
                  :use (:instance E-paths-that-satisfy-condition-suff
                        (paths (create-paths-witness-from-34markings (nodes-length nodeset)
                                                                     (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                                                               (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                                                       nil
                                                                                       (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                                                       graph nodeset)
                                                                     graph nodeset))
                        (dests (create-dests-witness-from-34markings (nodes-length nodeset)
                                                                     (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                                                               (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                                                       nil
                                                                                       (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                                                       graph nodeset)
                                                                     graph nodeset))))
          ("Subgoal 6" :use ((:instance temp22.0
                              (n (nodes-length nodeset))
                              (marks (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                               (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                       nil
                                                       (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                       graph nodeset)))
                             (:instance temp13.00
                              (n (nodes-length nodeset))
                              (nodes (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                             (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)))
                              (stack nil)
                              (marks (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)))
                             (:instance temp14.5
                              (n (nodes-length nodeset)))
                             (:instance temp14.4
                              (n (nodes-length nodeset))
                              (marks (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)))
                             (:instance algo-preserves-invariant-deps
                              (n (nodes-length nodeset)))
                             (:instance algo-preserves-invariant-unresolved
                              (n (nodes-length nodeset)))))
          ("Subgoal 5" :use ((:instance temp22.0
                              (n (nodes-length nodeset))
                              (marks (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                               (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                       nil
                                                       (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                       graph nodeset)))
                             (:instance temp13.00
                              (n (nodes-length nodeset))
                              (nodes (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                             (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)))
                              (stack nil)
                              (marks (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)))
                             (:instance temp14.5
                              (n (nodes-length nodeset)))
                             (:instance temp14.4
                              (n (nodes-length nodeset))
                              (marks (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)))
                             (:instance algo-preserves-invariant-deps
                              (n (nodes-length nodeset)))
                             (:instance algo-preserves-invariant-unresolved
                              (n (nodes-length nodeset)))))
         ("Subgoal 4" :use ((:instance temp14.00
                              (n (nodes-length nodeset))
                              (marks (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                               (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                       nil
                                                       (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                       graph nodeset)))
                             (:instance temp13.00
                              (n (nodes-length nodeset))
                              (nodes (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                             (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)))
                              (stack nil)
                              (marks (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)))
                             (:instance temp14.4
                              (n (nodes-length nodeset))
                              (marks (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)))
                             (:instance temp14.5
                              (n (nodes-length nodeset)))
                             (:instance algo-preserves-invariant-deps
                              (n (nodes-length nodeset)))
                             (:instance algo-preserves-invariant-unresolved
                              (n (nodes-length nodeset)))
                             (:instance temp14.66
                              (n (nodes-length nodeset))
                              (marks (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                               (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                       nil
                                                       (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                       graph nodeset)))
                             (:instance temp14.77
                              (paths (create-paths-witness-from-34markings (nodes-length nodeset)
                                                                           (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                                                                     (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                                                             nil
                                                                                             (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                                                             graph nodeset)
                                                                           graph nodeset))
                              (dests (create-dests-witness-from-34markings (nodes-length nodeset)
                                                                           (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                                                                     (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                                                             nil
                                                                                             (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                                                             graph nodeset)
                                                                           graph nodeset))
                              (subgraph1 (append (filter-3marked-nodes (nodes-length nodeset) (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                                                                                        (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                                                                                nil
                                                                                                                (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                                                                                graph nodeset) nodeset)
                                                 (filter-4marked-nodes (nodes-length nodeset) (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                                                                                        (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                                                                                nil
                                                                                                                (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                                                                                graph nodeset) nodeset)))
                              (subgraph2 (union-of (create-paths-witness-from-34markings (nodes-length nodeset)
                                                                                         (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                                                                                   (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                                                                           nil
                                                                                                           (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                                                                           graph nodeset)
                                                                                         graph nodeset))))
                             (:instance algo-preserves-st-filter-1marked-nodes=nil
                              (nodes (st-all-nodes nodeset))
                              (n (nodes-length nodeset)))
                             (:instance algo-preserves-invariant-3marks
                              (n (nodes-length nodeset)))
                             (:instance step2-ensures-invariant-escs-total
                              (marks (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)))))
          ("Subgoal 3" :use ((:instance temp14.00
                              (n (nodes-length nodeset))
                              (marks (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                               (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                       nil
                                                       (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                       graph nodeset)))
                             (:instance temp13.00
                              (n (nodes-length nodeset))
                              (nodes (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                             (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)))
                              (stack nil)
                              (marks (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)))
                             (:instance temp14.4
                              (n (nodes-length nodeset))
                              (marks (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)))
                             (:instance step2-ensures-invariant-escs-total
                              (marks (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)))
                             (:instance algo-preserves-invariant-3marks
                              (n (nodes-length nodeset)))
                             (:instance algo-preserves-invariant-unresolved
                              (n (nodes-length nodeset)))
                             (:instance algo-preserves-invariant-deps
                              (n (nodes-length nodeset)))
                             (:instance algo-preserves-st-filter-1marked-nodes=nil
                              (nodes (st-all-nodes nodeset))
                              (n (nodes-length nodeset)))
                             (:instance temp14.66
                              (n (nodes-length nodeset))
                              (marks (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                               (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                       nil
                                                       (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                       graph nodeset)))
                             (:instance temp14.77
                              (paths (create-paths-witness-from-34markings (nodes-length nodeset)
                                                                           (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                                                                     (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                                                             nil
                                                                                             (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                                                             graph nodeset)
                                                                           graph nodeset))
                              (dests (create-dests-witness-from-34markings (nodes-length nodeset)
                                                                           (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                                                                     (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                                                             nil
                                                                                             (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                                                             graph nodeset)
                                                                           graph nodeset))
                              (subgraph1 (append (filter-3marked-nodes (nodes-length nodeset)
                                                                       (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                                                                 (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                                                         nil
                                                                                         (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                                                         graph nodeset) nodeset)
                                                 (filter-4marked-nodes (nodes-length nodeset)
                                                                       (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                                                                 (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                                                         nil
                                                                                         (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                                                         graph nodeset) nodeset)))
                              (subgraph2 (union-of (create-paths-witness-from-34markings (nodes-length nodeset)
                                                                                         (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                                                                                   (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                                                                           nil
                                                                                                           (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                                                                           graph nodeset)
                                                                                         graph nodeset))))
                             (:instance temp14.5
                              (n (nodes-length nodeset)))))
          ("Subgoal 2" :use ((:instance temp14.10
                              (n (nodes-length nodeset))
                              (marks (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                               (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                       nil
                                                       (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                       graph nodeset)))
                             (:instance temp13.00
                              (n (nodes-length nodeset))
                              (nodes (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                             (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)))
                              (stack nil)
                              (marks (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)))
                             (:instance temp14.4
                              (n (nodes-length nodeset))
                              (marks (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)))
                             (:instance algo-preserves-invariant-3marks
                              (n (nodes-length nodeset)))
                             (:instance temp14.5
                              (n (nodes-length nodeset)))))
          ("Subgoal 1" :use ((:instance temp14.10
                              (n (nodes-length nodeset))
                              (marks (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                               (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                       nil
                                                       (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)
                                                       graph nodeset)))
                             (:instance temp13.00
                              (n (nodes-length nodeset))
                              (nodes (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                             (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)))
                              (stack nil)
                              (marks (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)))
                             (:instance temp14.4
                              (n (nodes-length nodeset))
                              (marks (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset)))
                             (:instance algo-preserves-invariant-3marks
                              (n (nodes-length nodeset)))
                             (:instance temp14.5
                              (n (nodes-length nodeset)))))))


(defthm step1-nil-does-not-alter-marks
  (let ((marks-after (st-escapable-inv nil prev  graph marks nodeset)))
    (equal marks-after marks)))


(defthm dlf->algo-returns-t-from-invariants
  (implies (and (filled-graphp (neighbors->dests-length graph) graph)
                (valid-graph (nodes-length nodeset) graph nodeset)
                ;; The deadlock condition:
                (not (E-paths-that-satisfy-condition graph nodeset))
                ;; Invariants:
                (equal (st-filter-1marked-nodes (st-all-nodes nodeset) marks) nil)
                (invariant-unresolved (nodes-length nodeset) marks graph nodeset)
                (invariant-3marks (nodes-length nodeset) marks graph nodeset)
                (invariant-deps (nodes-length nodeset) marks graph nodeset)
                (invariant-escs-total (nodes-length nodeset) marks graph nodeset))
           (equal (mv-nth 0 (algorithm graph marks nodeset)) t))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (A-valid-nodes-show-nodeset)
                                  (esci depi update-marksi neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi st-escapable-inv E-paths-that-satisfy-condition
                                        st-A-subgraphs-E-escape process-escs-eff step2-preserves-st-filter-1marked-nodes=nil step2-preserves-invariant-deps spec-of-filter-3marked-nodes
                                        spec-of-filter-4marked-nodes))
                  :do-not '(eliminate-destructors generalize)
                  :use ((:instance dlf->not3
                         (node (car (filter-4marked-nodes (nodes-length nodeset)
                                                          (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                                                    (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                                            nil
                                                                            (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) graph nodeset)
                                                          nodeset))))
                        (:instance spec-of-filter-4marked-nodes
                         (i (car (filter-4marked-nodes (nodes-length nodeset)
                                                       (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                                                 (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                                         nil
                                                                         (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) graph nodeset)
                                                       nodeset)))
                         (marks (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                          (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                  nil
                                                  (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) graph nodeset))
                         (n (nodes-length nodeset)))
                        (:instance dlf->not3
                         (node (car (filter-3marked-nodes (nodes-length nodeset)
                                                          (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                                                    (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                                            nil
                                                                            (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) graph nodeset)
                                                          nodeset))))
                        (:instance spec-of-filter-3marked-nodes
                         (i (car (filter-3marked-nodes (nodes-length nodeset)
                                                       (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                                                 (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                                         nil
                                                                         (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) graph nodeset)
                                                       nodeset)))
                         (marks (process-escs-eff (append (filter-3marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset)
                                                          (filter-4marked-nodes (nodes-length nodeset) (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) nodeset))
                                                  nil
                                                  (st-A-nodes-escapable-inv (nodes-length nodeset) graph marks nodeset) graph nodeset))
                         (n (nodes-length nodeset)))))))

(defthm dlf->algo-returns-t
  (implies (and (filled-graphp (neighbors->dests-length graph) graph)
                (valid-graph (nodes-length nodeset) graph nodeset)
                ;; The deadlockfreedom condition
                (not (E-paths-that-satisfy-condition graph nodeset))
                ;; Initially:
                (A-clear (nodes-length nodeset) marks))
           (equal (mv-nth 0 (algorithm graph marks nodeset)) t))
  :hints (("Goal" :in-theory (e/d (A-valid-nodes-show-nodeset)
                                  (esci depi update-marksi neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi st-escapable-inv
                                        st-A-subgraphs-E-escape process-escs-eff step2-preserves-st-filter-1marked-nodes=nil step2-preserves-invariant-deps))
                  :use ((:instance dlf->algo-returns-t-from-invariants)
                        (:instance A-clear-implies-st-filter-1marked-nodes=nil
                         (nodes (st-all-nodes nodeset)))))))

(defthm temp15.0.1
  (implies (st-d-pathp path dest graph nodeset)
           (A-valid-nodes path nodeset)))
(defthm temp15.0
  (implies (paths-satisfy-condition paths dests subgraph graph nodeset)
           (A-valid-nodes (union-of paths) nodeset)))

;;---------------------------------
;;---------------------------------
;; 6.) FINAL THEOREM
;;---------------------------------
;;---------------------------------
;; If the algorithm is supplied a valid and filled graph stobj, and all markings are clear, then the algorithm returns t iff the condition holds
(defthm dlf<->algo-returns-t
  (implies (and (filled-graphp (neighbors->dests-length graph) graph)
                (valid-graph (nodes-length nodeset) graph nodeset)
                (A-clear (nodes-length nodeset) marks))
           (iff (equal (mv-nth 0 (algorithm graph marks nodeset)) t)
                (not (E-paths-that-satisfy-condition graph nodeset))))
  :otf-flg t
  :hints (("Goal" :in-theory (disable nodesi process-escs-eff)
                  :use ((:instance dlf->algo-returns-t)
                        (:instance dl->algo-returns-nil
                         (paths (car (E-paths-that-satisfy-condition-witness graph nodeset)))
                         (dests (mv-nth 1 (E-paths-that-satisfy-condition-witness graph nodeset))))))))#|ACL2s-ToDo-Line|#






