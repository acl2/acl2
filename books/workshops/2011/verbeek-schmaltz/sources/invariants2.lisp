#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#


(in-package "ACL2")
(include-book "invariants")
(include-book "perm")

;; BEGIN invariant-3marks
(defthm invariant-3marks-append-to-dep
  (equal (invariant-3marks n (append-to-dep i x marks) graph nodeset)
         (invariant-3marks n marks graph nodeset))
  :hints (("Goal" :in-theory (disable esci depi update-marksi update-esci update-depi neighborsi dests-of-edge neighbors->destsi update-esci marksi nodesi ))))
(defthm invariant-3marks-append-to-esc
  (equal (invariant-3marks n (append-to-esc i x marks) graph nodeset)
         (invariant-3marks n marks graph nodeset))
  :hints (("Goal" :in-theory (disable esci depi update-marksi update-esci update-depi neighborsi dests-of-edge neighbors->destsi update-esci marksi nodesi ))))
(defthm invariant-3marks-update-marksi-update-esci
  (equal (invariant-3marks n (update-marksi i x (update-esci j y marks)) graph nodeset)
         (invariant-3marks n (update-marksi i x marks) graph nodeset))
  :hints (("Goal" :in-theory (disable update-esci update-marksi marksi neighborsi))))
(defthm invariant-3marks-update-marksi-append-to-esc
  (equal (invariant-3marks n (update-marksi i x (append-to-esc j y marks)) graph nodeset)
         (invariant-3marks n (update-marksi i x marks) graph nodeset))
  :hints (("Goal" :in-theory (disable esci depi update-marksi neighborsi dests-of-edge neighbors->destsi update-esci marksi nodesi))))
(defthm invariant-3marks-update-marksi-append-to-dep
  (equal (invariant-3marks n (update-marksi i x (append-to-dep j y marks)) graph nodeset)
         (invariant-3marks n (update-marksi i x marks) graph nodeset))
  :hints (("Goal" :in-theory (disable esci depi update-marksi neighborsi dests-of-edge neighbors->destsi update-depi marksi nodesi))))
(defthm invariant-3marks-update-esci
  (let* ((marks-after (update-esci i x marks)))
    (equal (invariant-3marks n marks-after graph nodeset)
           (invariant-3marks n marks graph nodeset)))
  :hints (("Goal" :in-theory (disable update-esci))))
(defthm invariant-3marks-update-depi
  (let* ((marks-after (update-depi i x marks)))
    (equal (invariant-3marks n marks-after graph nodeset)
           (invariant-3marks n marks graph nodeset)))
  :hints (("Goal" :in-theory (disable update-depi))))

(defthm update-marksi-3-preserves-invariant-3marks
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (natp i)
                (< i (nodes-length nodeset))
                (<= n (nodes-length nodeset))
                (equal (nodesi i nodeset) 1)
                (consp (neighborsi i graph))
                (equal (st-filter-unmarked123-nodes (neighborsi i graph) marks) nil)
                (invariant-3marks n marks graph nodeset))
           (invariant-3marks n (update-marksi i 3 marks) graph nodeset))
  :hints (("Goal" :in-theory (disable esci depi update-marksi update-esci nodes-length update-depi neighborsi dests-of-edge neighbors->destsi update-esci marksi nodesi))))
(defthm update-marksi-2-preserves-invariant-3marks
  (let* ((marks-after (update-marksi i 2 marks)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (<= n (nodes-length nodeset))
                  (natp i)
                  (natp n)
                  (invariant-3marks n marks graph nodeset))
             (invariant-3marks n marks-after graph nodeset)))
  :hints (("Goal" :in-theory (disable marksi update-marksi neighborsi))))
(defthm update-marksi-4-preserves-invariant-3marks
  (let* ((marks-after (update-marksi i 4 marks)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (<= n (nodes-length nodeset))
                  (natp i)
                  (natp n)
                  (invariant-3marks n marks graph nodeset))
             (invariant-3marks n marks-after graph nodeset)))
  :hints (("Goal" :in-theory (disable marksi update-marksi neighborsi))))
(defthm update-marksi-1-preserves-invariant-3marks
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (<= n (nodes-length nodeset))
                (natp n)
                (natp i)
                (invariant-3marks n marks graph nodeset))
           (invariant-3marks n (update-marksi i 1 marks) graph nodeset))
  :hints (("Goal" :in-theory (disable esci depi update-marksi update-esci update-depi neighborsi dests-of-edge neighbors->destsi update-esci marksi nodesi))))
(defthm forced--st-filter-unmarked123-nodes-update-marksi-4;:TODO
  (implies (and (force (natp node))
                (force (A-valid-nodes nodes nodeset)))
           (equal (st-filter-unmarked123-nodes nodes (update-marksi node 4 marks))
                  (remove-equal node (st-filter-unmarked123-nodes nodes marks))))
    :hints (("Goal" :do-not '(eliminate-destructors generalize)
                    :in-theory (disable esci depi update-marksi marksi-update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi))))
(in-theory (disable member-show-nodeset member-show-all-nodes))
(defthm temp9.2
  (iff (member-equal node (show-nodeset n nodeset))
       (if (natp n)
         (and (natp node)
              (equal (nodesi node nodeset) 1)
              (< node n))
         nil)))
(defthm step1-marks-all-nodes-in-parameter-1
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (A-valid-nodes (st-all-nodes nodeset) nodeset)
                  (A-valid-nodes nodes nodeset)
                  (natp prev)
                  (< prev (nodes-length nodeset))
                  (<= n (nodes-length nodeset)))
             (equal (st-filter-unmarked123-nodes nodes marks-after)
                    nil)))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset)
                  :in-theory (disable esci depi update-marksi neighborsi nodes-length dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi))))
;; step 1 preserves invariant-3marks (inductive)
(defthm step1-preserves-invariant-3marks-inductive
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (natp prev)
                  (< prev (nodes-length nodeset))
                  (invariant-3marks (nodes-length nodeset) marks graph nodeset))
             (invariant-3marks (nodes-length nodeset) marks-after graph nodeset)))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset)
                  :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi))
          ("Subgoal *1/7" :use (:instance update-marksi-3-preserves-invariant-3marks
                                (i (car nodes))
                                (n (nodes-length nodeset))
                                (marks (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset))))))
;; step 1 preserves invariant-3marks
(defthm step1-preserves-invariant-3marks
  (let* ((marks-after (st-escapable-inv (list root) -1 graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (natp root)
                  (< root (nodes-length nodeset))
                  (invariant-3marks (nodes-length nodeset) marks graph nodeset))
             (invariant-3marks (nodes-length nodeset) marks-after graph nodeset)))
  :hints (("Goal" :in-theory (disable esci depi update-marksi neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi nodes-length)
                  :expand (st-escapable-inv (list root) -1 graph marks nodeset))
          ("Subgoal 4" :use (:instance update-marksi-3-preserves-invariant-3marks
                             (n (nodes-length nodeset))
                             (i root)
                             (marks (st-escapable-inv (neighborsi root graph) root graph (update-marksi root 1 marks) nodeset))))))
;; step 2 preserves invariant-3marks
(defthm step2-preserves-invariant-3marks
  (let* ((marks-after (process-escs-eff nodes stack marks graph nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (<= n (nodes-length nodeset))
                  (invariant-3marks n marks graph nodeset))
             (invariant-3marks n marks-after graph nodeset)))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :induct (process-escs-eff nodes stack marks graph nodeset)
                  :in-theory (disable marksi update-marksi neighborsi update-esci neighbors->destsi esci depi))
          ("Subgoal *1/8.3" :use (:instance update-marksi-2-preserves-invariant-3marks
                                  (i (car nodes))))
          ("Subgoal *1/4.3" :use (:instance update-marksi-2-preserves-invariant-3marks
                                  (i (car nodes))))
          ("Subgoal *1/3.3" :use (:instance update-marksi-4-preserves-invariant-3marks
                                  (i (car nodes))))))
;; the algorithm preserves invariant-3marks
(defthm algo-preserves-invariant-3marks
  (let* ((marks-after (st-A-nodes-escapable-inv n graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (invariant-3marks (nodes-length nodeset) marks graph nodeset))
             (invariant-3marks (nodes-length nodeset) marks-after graph nodeset)))
  :hints (("Subgoal *1/2" :use (:instance step1-preserves-invariant-3marks
                                (root (1- n))))))
;; the spec of invariant-3marks
(defthm spec-of-invariant-3marks-parents
  (implies (and (invariant-3marks n marks graph nodeset)
                (<= n (nodes-length nodeset)))
           (st-A-parents (filter-3marked-nodes n marks nodeset) graph)))
(defthm spec-of-invariant-3marks-valid-nodes
  (implies (and (invariant-3marks n marks graph nodeset)
                (natp n)
                (natp i)
                (equal (marksi i marks) 3)
                (< i n))
           (equal (nodesi i nodeset) 1)))
(defthm spec-of-invariant-3marks-parent
  (implies (and (invariant-3marks n marks graph nodeset)
                (natp n)
                (natp i)
                (< i n)
                (equal (marksi i marks) 3))
           (consp (neighborsi i graph))))
(defthm spec-of-invariant-3marks-no-unmarked-neighbors
  (implies (and (invariant-3marks n marks graph nodeset)
                (natp n)
                (natp i)
                (equal (marksi i marks) 3)
                (< i n))
           (equal (st-filter-unmarked123-nodes (neighborsi i graph) marks) nil)))
;; invariant-holds initially
(defthm A-clear-implies-invariant-3marks
  (implies (A-clear n marks)
           (invariant-3marks n marks graph nodeset)))
;; END invariant-3marks


;; BEGIN invariant-unresolved
(defthm update-marksi-124-preserves-invariant-unresolved
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (natp node)
                (<= n (nodes-length nodeset))
                (or (equal x 1) (equal x 2) (equal x 4))
                (invariant-unresolved n marks graph nodeset))
           (invariant-unresolved n (update-marksi node x marks) graph nodeset))
  :hints (("Goal" :in-theory (disable marksi update-marksi neighborsi))))
(defthm append-to-dep-preserves-invariant-unresolved
  (implies (and (natp i)
                (equal (marksi i marks) 1)
                (invariant-unresolved n marks graph nodeset))
           (invariant-unresolved n (append-to-dep i x marks) graph nodeset))
  :hints (("Goal" :in-theory (disable update-depi depi esci marksi))
          ("Subgoal *1/4" :use (:instance depi-update-depi-diff
                                (i (1- n))
                                (j i)
                                (x (append x (depi i marks)))))))
(defthm append-to-esc-1-preserves-invariant-unresolved
  (implies (and (natp i)
                (equal (marksi i marks) 1)
                (invariant-unresolved n marks graph nodeset))
           (invariant-unresolved n (append-to-esc i x marks) graph nodeset))
  :hints (("Goal" :in-theory (disable update-esci depi esci marksi))
          ("Subgoal *1/4" :use (:instance esci-update-esci-diff
                                (i (1- n))
                                (j i)
                                (x (append x (esci i marks)))))))
(defthm update-marksi-3-preserves-invariant-unresolved
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (natp node)
                (<= n (nodes-length nodeset))
                (unresolved node marks)
                (invariant-unresolved n marks graph nodeset))
           (invariant-unresolved n (update-marksi node 3 marks) graph nodeset))
  :hints (("Goal" :in-theory (disable update-marksi depi esci marksi neighborsi))))
;; step 1 preserves invariant-unresolved (inductive)
(defthm step1-preserves-invariant-unresolved-inductive
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (A-valid-nodes (st-all-nodes nodeset) nodeset)
                  (A-valid-nodes nodes nodeset)
                  (natp prev)
                  (< prev (nodes-length nodeset))
                  (<= n (nodes-length nodeset))
                  ;; Invariant
                  (natp prev)
                  (equal (marksi prev marks) 1)
                  (invariant-unresolved n marks graph nodeset))
             (invariant-unresolved n marks-after graph nodeset)))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset)
                  :in-theory (disable esci depi update-marksi neighborsi nodes-length dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi))
          ("Subgoal *1/6.1" :use ((:instance update-marksi-3-preserves-invariant-unresolved
                                   (node (car nodes))
                                   (marks (st-escapable-inv (neighborsi (car nodes) graph) (car nodes)  graph (update-marksi (car nodes) 1 marks) nodeset)))))))
;; step 1 preserves invariant-unresolved
(defthm step1-preserves-invariant-unresolved
  (let* ((marks-after (st-escapable-inv (list root) -1 graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (neighbors->dests-length graph) graph)
                  (natp root)
                  (< root (nodes-length nodeset))
                  (invariant-unresolved (nodes-length nodeset) marks graph nodeset))
             (invariant-unresolved (nodes-length nodeset) marks-after graph nodeset)))
  :hints (("Goal" :in-theory (disable esci depi update-marksi neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi)
                  :expand (st-escapable-inv (list root) -1 graph marks nodeset)
                  :use ((:instance update-marksi-3-preserves-invariant-unresolved
                         (n (nodes-length nodeset))
                         (node root)
                         (marks (st-escapable-inv (neighborsi root graph) root graph (update-marksi root 1 marks) nodeset)))
                        (:instance step1-marks-all-nodes-in-parameter-1
                         (n (nodes-length nodeset))
                         (nodes (neighborsi root graph))
                         (prev root)
                         (marks (update-marksi root 1 marks)))))))
;; step 2 preserves invariant-unresolved
(defthm append-to-esc-3-preserves-invariant-unresolved
  (implies (and (natp node)
                (not (equal (marksi node marks) 3))
                (invariant-unresolved n marks graph nodeset))
           (invariant-unresolved n (append-to-esc node x marks) graph nodeset))
  :hints (("Goal" :in-theory (disable marksi depi update-esci neighborsi esci))
          ("Subgoal *1/4" :use (:instance esci-update-esci-diff
                                (i (1- n))
                                (j node)
                                (x (append x (esci node marks)))))))
(defthm append-to-esc-2-preserves-invariant-unresolved
  (let* ((marks-after (update-marksi node 2 (append-to-esc node x marks))))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (natp node)
                  (<= n (nodes-length nodeset))
                  (invariant-unresolved n marks graph nodeset))
             (invariant-unresolved n marks-after graph nodeset)))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :in-theory (disable marksi update-marksi neighborsi update-esci neighbors->destsi esci depi))
          ("Subgoal *1/5" :use ((:instance esci-update-esci-diff
                                 (i (1- n))
                                 (j node)
                                 (x (append x (esci node marks))))
                                (:instance st-filter-unmarked123-nodes-update-marksi-unmarked
                                 (nodes (neighborsi (1- n) graph))
                                 (x 2))))))
(defthm append-to-esc-4-preserves-invariant-unresolved
  (let* ((marks-after (update-marksi node 4 (append-to-esc node x marks))))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (natp node)
                  (<= n (nodes-length nodeset))
                  (invariant-unresolved n marks graph nodeset))
             (invariant-unresolved n marks-after graph nodeset)))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :in-theory (disable marksi update-marksi neighborsi update-esci neighbors->destsi esci depi))
          ("Subgoal *1/5" :use ((:instance esci-update-esci-diff
                                 (i (1- n))
                                 (j node)
                                 (x (append x (esci node marks))))
                                (:instance st-filter-unmarked123-nodes-update-marksi-unmarked
                                 (nodes (neighborsi (1- n) graph))
                                 (x 4))))))
(defthm append-to-esc-preserves-invariant-unresolved
  (let* ((marks-after (append-to-esc node x marks)))
    (implies (and (natp node)
                  (unresolved node marks-after)
                  (invariant-unresolved n marks graph nodeset))
             (invariant-unresolved n marks-after graph nodeset)))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :in-theory (disable marksi update-marksi neighborsi neighbors->destsi esci depi update-esci))
          ("Subgoal *1/4" :use (:instance esci-update-esci-diff
                                (i (1- n))
                                (j node)
                                (x (append x (esci node marks)))))))
(defthm step2-preserves-invariant-unresolved
  (let* ((marks-after (process-escs-eff nodes stack marks graph nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (<= n (nodes-length nodeset))
                  (invariant-unresolved n marks graph nodeset))
             (invariant-unresolved n marks-after graph nodeset)))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :induct (process-escs-eff nodes stack marks graph nodeset)
                  :in-theory (disable marksi update-marksi neighborsi append-to-esc neighbors->destsi esci A-valid-nodes-neighbors depi))))
;; the algorithm preserves invariant-unresolved
(defthm algo-preserves-invariant-unresolved
  (let* ((marks-after (st-A-nodes-escapable-inv n graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  (invariant-unresolved (nodes-length nodeset) marks graph nodeset))
             (invariant-unresolved (nodes-length nodeset) marks-after graph nodeset)))
  :hints (("Subgoal *1/2" :use (:instance step1-preserves-invariant-unresolved
                                (root (1- n))))))
;; the spec of invariant-unresolved
(defthm spec-of-invariant-unresolved
  (implies (and (natp n)
                (natp node)
                (< node n)
                (equal (marksi node marks) 3)
                (invariant-unresolved n marks graph nodeset))
           (unresolved node marks)))
;; invariant-unresolved holds initially
(defthm A-clear-implies-invariant-unresolved
  (implies (A-clear n marks)
           (invariant-unresolved n marks graph nodeset)))
;; END invarant-unresolved

;; BEGIN invariant-deps
(defthm labels-edges-are-dests
  (implies (and (is-keys-of-alist neighbors neighbors->destsi)
                (no-duplicatesp-equal (keys (neighbors->destsi node graph)))
                (member-equal neighbor neighbors)
                (subsetp neighbors (neighborsi node graph))
                (subsetp neighbors->destsi (neighbors->destsi node graph)))
           (subsetp (dests-of-edge node neighbor graph nodeset)
                    (union-of (values-alist neighbors->destsi))))
  :hints (("Subgoal *1/2.1"  :use (:instance assoc-key-yeilds-field
                                   (key (car neighbors))
                                   (field (car neighbors->destsi))
                                   (alist (neighbors->destsi node graph))))))

(defthm temp24.1
  (implies (and (valid-graph n graph nodeset)
                (filled-graphp n graph)
                (natp n)
                (natp node)
                (< node n)
                (member-equal neighbor (neighborsi node graph)))
           (A-valid-nodes (cdr (assoc neighbor (neighbors->destsi node graph))) nodeset)))
(defthm append-to-dep-preserves-invariant-deps
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (filled-graphp (nodes-length nodeset) graph)
                (natp node)
                (< node (nodes-length nodeset))
                (member-equal neighbor (neighborsi node graph))
                (invariant-deps n marks graph nodeset))
           (invariant-deps n (append-to-dep node (dests-of-edge node neighbor graph nodeset) marks) graph nodeset))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :in-theory (disable esci depi update-marksi nodes-length neighborsi neighbors->destsi update-depi marksi nodesi))
          ("Subgoal *1/5" :use ((:instance depi-update-depi-diff
                                 (i (1- n))
                                 (j node)
                                 (x (append (dests-of-edge node neighbor graph nodeset) (depi node marks))))
                                (:instance labels-edges-are-dests
                                 (neighbors->destsi (neighbors->destsi (1- n) graph))
                                 (node (1- n))
                                 (neighbors (neighborsi (1- n) graph)))))))
(defthm invariant-deps-update-marksi
  (equal (invariant-deps n (update-marksi i x marks) graph nodeset)
         (invariant-deps n marks graph nodeset)))
(defthm invariant-deps-append-to-esc
  (equal (invariant-deps n (append-to-esc i x marks) graph nodeset)
         (invariant-deps n marks graph nodeset)))
;; step 1 preserves invariant-deps (inductive)
(defthm step1-preserves-invariant-deps-inductive
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  (subsetp nodes (neighborsi prev graph))
                  (invariant-deps n marks graph nodeset))
             (invariant-deps n marks-after graph nodeset)))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset)
                  :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi))))
;; step 1 preserves invariant-deps
(defthm step1-preserves-invariant-deps
  (let* ((marks-after (st-escapable-inv (list root) -1 graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (neighbors->dests-length graph) graph)
                  (natp root)
                  (< root (nodes-length nodeset))
                  (invariant-deps (nodes-length nodeset) marks graph nodeset))
             (invariant-deps (nodes-length nodeset) marks-after graph nodeset)))
  :hints (("Goal" :in-theory (disable esci depi update-marksi neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi)
                  :expand (st-escapable-inv (list root) -1 graph marks nodeset))))
(defthm step2-does-not-alter-deps
  (let ((marks-after (process-escs-eff nodes stack marks graph nodeset)))
    (equal (depi i marks-after)
           (depi i marks)))
  :hints (("Goal" :in-theory (disable depi esci update-esci update-marksi))))
;; step 2 preserves invariant-deps
(defthm step2-preserves-invariant-deps
  (let ((marks-after (process-escs-eff nodes stack marks graph nodeset)))
    (equal (invariant-deps n marks-after graph nodeset)
           (invariant-deps n marks graph nodeset))))
;; the algorithm preserves invariant-deps
(defthm algo-preserves-invariant-deps
  (let* ((marks-after (st-A-nodes-escapable-inv n graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  (invariant-deps (nodes-length nodeset) marks graph nodeset))
             (invariant-deps (nodes-length nodeset) marks-after graph nodeset)))
  :hints (("Subgoal *1/2" :use (:instance step1-preserves-invariant-deps
                                (root (1- n))))))
;; the spec of invariant-deps
(defthm A-valid-nodes-union-of-values
  (implies (A-valid-nodes-values alist nodeset)
           (A-valid-nodes (union-of (values-alist alist)) nodeset)))
(defthm not-member-nil-depi
  (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                (natp n)
                (natp i)
                (< i n)
                (< i (nodes-length nodeset))
                (invariant-deps n marks graph nodeset))
           (not (member-equal nil (depi i marks))))
  :hints (("Goal" :in-theory (disable neighbors->destsi depi A-valid-nodes-union-of-values))
          ("Subgoal *1/3" :use (:instance A-valid-nodes-union-of-values
                                (alist (neighbors->destsi (1- n) graph))))))
(defthm spec-of-invariant-deps
  (implies (and (natp n)
                (natp i)
                (< i n)
                (invariant-deps n marks graph nodeset))
           (subsetp (depi i marks) (union-of (values-alist (neighbors->destsi i graph))))))
;; invariant-deps holds initially
(defthm A-clear-implies-invariant-deps
  (implies (A-clear n marks)
           (invariant-deps n marks graph nodeset)))
;; END invariant-deps


;; BEGIN invariant-escs-total is preserved by steps 1 & 2
;; After termination of step 1, this invariant holds for all but some set of uncertain nodes. It is not necessary to know which nodes are uncertain, as we prove that even if
;; prior to step 2 all 3-marked ports are uncertain, step 2 still ensures that the invariant holds after step 2 (theorem step2-ensures-invariant-escs-total-inductive). That the invariant holds if all
;; 3-marked ports are considered uncertain, is trivial (theorem invariant-escs-total-holds-after-step2).
(defthm rewrite-A-invariant-escs-no-uncertain-nodes
  (implies (endp nodes)
           (equal (A-invariant-escs n nodes marks graph nodeset)
                  (invariant-escs-total n marks graph nodeset))))
(defthmd append-remove-l-and-r
  (equal (append (remove-equal a x) (remove-equal a y))
         (remove-equal a (append x y))))

(defthm temp0.0
  (subsetp x (append x y)))

(defthm A-invariant-escs-cons-uncertain-node
  (implies (A-invariant-escs n nodes marks graph nodeset)
           (A-invariant-escs n (cons node nodes) marks graph nodeset))
  :hints (("Goal" :in-theory (disable update-marksi update-depi esci depi marksi neighborsi))))


(defthm temp10.5
  (equal (remove-equal a (append x (cons a y)))
         (remove-equal a (append x y))))
(defthm temp10.13
  (subsetp (A-dests-of node (st-filter-2marked-nodes nodes (update-marksi i 4 marks)) graph nodeset)
           (A-dests-of node (st-filter-2marked-nodes nodes marks) graph nodeset)))
(defthm update-marksi-4-preserves-A-invariant-escs
  (let ((marks-after (update-marksi node 4 marks)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (A-natp nodes)
                  (natp node)
                  (<= n (nodes-length nodeset))
                  (A-invariant-escs n nodes marks graph nodeset))
             (A-invariant-escs n (remove-equal node nodes) marks-after graph nodeset)))
  :hints (("Goal" :in-theory (disable update-marksi append-to-esc esci depi marksi neighborsi nodesi temp10.13)
                  :induct (A-invariant-escs n (cons node nodes) marks graph nodeset))
          ("Subgoal *1/2" :use (:instance temp10.13
                                (node (1- n))
                                (nodes (neighborsi (1- n) graph))
                                (i node)))))
(defthm A-invariant-escs-append-uncertain-nodes
  (implies (A-invariant-escs n nodes marks graph nodeset)
           (A-invariant-escs n (append x nodes) marks graph nodeset))
  :hints (("Goal" :in-theory (disable update-marksi update-depi esci depi marksi neighborsi))))
(defthm append-to-esc-preserves-A-invariant-escs-2
  (let ((marks-after (append-to-esc i x marks)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (A-natp nodes)
                  (natp node)
                  (<= n (nodes-length nodeset))
                  (A-invariant-escs n nodes marks graph nodeset))
             (A-invariant-escs n nodes marks-after graph nodeset)))
  :hints (("Goal" :in-theory (disable update-marksi append-to-esc esci depi marksi neighborsi nodesi)
                  :induct (A-invariant-escs n (cons node nodes) marks graph nodeset))))
(defthm temp10.7
  (equal (A-valid-nodes (append x y) nodeset)
         (and (A-valid-nodes x nodeset)
              (A-valid-nodes y nodeset))))
(defthm temp10.8
  (implies (and (equal (marksi node marks) 4)
                (A-invariant-escs n nodes marks graph nodeset))
           (A-invariant-escs n (remove-equal node nodes) marks graph nodeset))
  :hints (("Goal" :in-theory (disable update-marksi append-to-esc esci depi marksi neighborsi nodesi))))

(defun st-filter-34marked-nodes (nodes st-marks)
  (declare (xargs :stobjs st-marks
                  :verify-guards nil))
  (cond ((endp nodes)
         nil)
        ((or (equal (marksi (car nodes) st-marks) 3)
             (equal (marksi (car nodes) st-marks) 4))
         (cons (car nodes) (st-filter-34marked-nodes (cdr nodes) st-marks)))
        (t
         (st-filter-34marked-nodes (cdr nodes) st-marks))))
(defthm temp10.0
  (implies (A-natp nodes)
           (A-natp (st-filter-34marked-nodes nodes marks))))

(defthm temp10.1
  (equal (st-filter-34marked-nodes (append x y) marks)
         (append (st-filter-34marked-nodes x marks)
                 (st-filter-34marked-nodes y marks))))
(defthm temp10.2
  (equal (st-filter-34marked-nodes (st-filter-3parents node n marks graph nodeset) marks)
         (st-filter-3parents node n marks graph nodeset)))
(defthm st-filter-34marked-nodes-update-marksi-2
  (let ((marks-after (update-marksi i 2 marks)))
    (implies (and (natp i)
                  (A-natp nodes))
             (equal (st-filter-34marked-nodes nodes marks-after)
                    (remove-equal i (st-filter-34marked-nodes nodes marks)))))
  :hints (("Goal" :in-theory (disable update-marksi marksi))))
(defthm st-filter-34marked-nodes-append-to-esc
  (equal (st-filter-34marked-nodes nodes (append-to-esc i x marks))
         (st-filter-34marked-nodes nodes marks)))
(defthm st-filter-34marked-nodes-remove
  (equal (st-filter-34marked-nodes (remove-equal node nodes) marks)
         (remove-equal node (st-filter-34marked-nodes nodes marks))))
(defthm temp10.3
  (implies (natp i)
           (equal (st-filter-3parents node n (update-marksi i 2 marks) graph nodeset)
                  (remove-equal i (st-filter-3parents node n marks graph nodeset)))))
(defthm st-filter-34marked-nodes-update-marksi-append-to-esc
  (equal (st-filter-34marked-nodes nodes (update-marksi j y (append-to-esc i x marks)))
         (st-filter-34marked-nodes nodes (update-marksi j y marks))))
(defthm temp10.4
  (A-natp (st-filter-3parents node n marks graph nodeset)))

(defthm st-filter-3parents-update-marksi-append-to-esc
  (equal (st-filter-3parents node n (update-marksi j y (append-to-esc i x marks)) graph nodeset)
         (st-filter-3parents node n (update-marksi j y marks) graph nodeset))
  :hints (("Goal" :in-theory (disable marksi update-esci update-marksi))))

(defthm temp10.6
  (implies (equal (marksi node marks) 3)
           (equal (st-filter-34marked-nodes nodes (update-marksi node 4 marks))
                  (st-filter-34marked-nodes nodes marks))))
(defthm temp24.3
  (implies (filled-graphp n graph)
           (equal (remove-equal node (st-filter-3parents node n marks graph nodeset))
                  (st-filter-3parents node n marks graph nodeset))))
(defthm temp24.4
  (equal (st-filter-34marked-nodes (upwards-4marked-reach n node marks graph nodeset) marks)
         (upwards-4marked-reach n node marks graph nodeset)))
(defthm upwards-4marked-reach-update-marksi-append-to-esc
  (equal (upwards-4marked-reach n node (update-marksi j y (append-to-esc i x marks)) graph nodeset)
         (upwards-4marked-reach n node (update-marksi j y marks) graph nodeset))
  :hints (("Goal" :in-theory (disable marksi update-esci update-marksi))))

(defthm upwards-4marked-reach-update-marksi-2
  (implies (natp node)
           (equal (upwards-4marked-reach n node (update-marksi node 2 marks) graph nodeset)
                  (upwards-4marked-reach n node marks graph nodeset)))
  :hints (("Goal" :in-theory (disable marksi update-esci update-marksi))))
(defthm upwards-4marked-reach-append-to-esc
  (equal (upwards-4marked-reach n node (append-to-esc i x marks) graph nodeset)
         (upwards-4marked-reach n node marks graph nodeset))
  :hints (("Goal" :in-theory (disable marksi update-esci update-marksi))))
(defthm temp24.5
  (implies (A-consp x)
           (A-consp (append-to-data i data x))))

(defthm update-marksi-2-append-to-esc-preserves-A-invariant-escs
  (let ((marks-after (update-marksi node 2 (append-to-esc node (A-dests-of node (st-filter-2marked-nodes (setminus (neighborsi node graph) stackedneighbors) marks) graph nodeset) marks))))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (A-natp nodes)
                  (natp node)
                  (<= n (nodes-length nodeset))
                  (A-invariant-escs n nodes marks graph nodeset))
             (A-invariant-escs n (append (st-filter-3parents node (nodes-length nodeset) marks graph nodeset)
                                         (upwards-4marked-reach (nodes-length nodeset) node marks graph nodeset)
                                         (remove-equal node nodes))
                               marks-after graph nodeset)))
  :hints (("Goal" :in-theory (disable update-marksi append-to-esc esci depi marksi neighborsi nodesi)
                  :induct (A-invariant-escs n nodes marks graph nodeset))))

(defun intersect (x y)
  (cond ((endp x)
         nil)
        ((member-equal (car x) y)
         (cons (car x) (intersect (cdr x) y)))
        (t
         (intersect (cdr x) y))))
(defthmd temp24.6.1
  (permp (st-filter-2marked-nodes nodes1 marks)
         (append (st-filter-2marked-nodes (setminus nodes1 nodes2) marks)
                 (st-filter-2marked-nodes (intersect nodes1 nodes2) marks))))

(defthm temp24.6.5
  (implies (permp (append x y) z)
           (permp (append x w y) (append w z))))
(defthm temp24.6.4
  (implies (and (natp node)
                (member-equal neighbor neighbors)
                (permp dests (A-dests-of node (del neighbor neighbors) graph nodeset)))
           (permp (append (dests-of-edge node neighbor graph nodeset) dests)
                  (A-dests-of node neighbors graph nodeset))))
(defthm temp24.6.6
  (implies (and (subsetp (del a x) y)
                (member-equal a y))
           (subsetp x y)))
(defthm temp24.6.7
  (implies (subsetp x y)
           (subsetp (del a x) y)))
(defcong permp iff (subsetp x y) 1)
(defcong permp permp (A-dests-of node neighbors graph nodeset) 2)
(in-theory (disable temp24.6.4 temp24.6.5 temp24.6.6 temp24.6.7))
(defthm temp24.6.2
  (equal (A-dests-of node (append x y) graph nodeset)
         (append (A-dests-of node x graph nodeset)
                 (A-dests-of node y graph nodeset))))
(defthmd temp24.6.8
  (implies (and (member-equal neighbor neighbors)
                (equal (marksi neighbor marks) 2))
           (subsetp (dests-of-edge node neighbor graph nodeset)
                    (A-dests-of node (st-filter-2marked-nodes neighbors marks) graph nodeset))))
(defthm temp24.6.3
  (subsetp (A-dests-of node (st-filter-2marked-nodes (intersect nodes1 nodes2) marks) graph nodeset)
           (A-dests-of node (st-filter-2marked-nodes nodes2 marks) graph nodeset))
  :hints (("Subgoal *1/2.2.1" :use (:instance temp24.6.8
                                    (neighbor (car nodes1))
                                    (neighbors nodes2)))))
(defthm temp24.6
  (implies (subsetp (A-dests-of node (st-filter-2marked-nodes nodes1 marks) graph nodeset) x)
           (subsetp (A-dests-of node (st-filter-2marked-nodes nodes2 marks) graph nodeset)
                    (append (A-dests-of node (st-filter-2marked-nodes (setminus nodes2 nodes1) marks) graph nodeset) x)))
  :hints (("Goal" :in-theory (disable  temp24.6.3)
                  :use ((:instance temp24.6.1
                         (nodes1 nodes2)
                         (nodes2 nodes1))
                        (:instance temp24.6.3
                         (nodes1 nodes2)
                         (nodes2 nodes1))))))
(defthm append-to-esc-preserves-A-invariant-escs
  (let ((marks-after (append-to-esc node (A-dests-of node (st-filter-2marked-nodes (setminus (neighborsi node graph) stackedneighbors) marks) graph nodeset) marks)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (A-natp nodes)
                  (natp node)
                  (equal (marksi node marks) 3)
                  (<= n (nodes-length nodeset))
                  (subsetp (A-dests-of node (st-filter-2marked-nodes stackedneighbors marks) graph nodeset) (esci node marks))
                  (A-invariant-escs n nodes marks graph nodeset))
             (A-invariant-escs n (append (upwards-4marked-reach (nodes-length nodeset) node marks graph nodeset)
                                         (remove-equal node nodes))
                               marks-after graph nodeset)))
  :hints (("Goal" :in-theory (disable update-marksi append-to-esc esci depi marksi neighborsi nodesi)
                  :induct (A-invariant-escs n (cons node nodes) marks graph nodeset))))
(defun-nx stack-contains-validated-edges (stack st-marks st-graph st-nodeset)
 ; (declare (xargs :non-executable t))
  (if (endp stack)
    t
    (and (subsetp (A-dests-of (caar stack) (cdar stack) st-graph st-nodeset) (esci (caar stack) st-marks))
         (stack-contains-validated-edges (cdr stack) st-marks st-graph st-nodeset))))
(defthm temp24.9
   (equal (stack-contains-validated-edges stack (update-marksi i x marks) graph nodeset)
          (stack-contains-validated-edges stack marks graph nodeset)))
(defthm temp24.10
   (implies (stack-contains-validated-edges stack marks graph nodeset)
            (stack-contains-validated-edges stack (append-to-esc node data marks) graph nodeset))
   :hints (("Goal" :in-theory (disable esci update-marksi append-to-esc))))

 (defthm temp24.11
   (implies (natp i)
            (equal (A-natp (keys (append-to-data i data alist)))
                   (A-natp (keys alist)))))
 (defthm temp24.8
   (implies (and (stack-contains-validated-edges stack marks graph nodeset)
                 (A-natp (keys stack)))
            (stack-contains-validated-edges (append-to-data node neighbors stack)
                                            (append-to-esc node (A-dests-of node neighbors graph nodeset) marks)
                                            graph nodeset))
   :hints (("Goal" :in-theory (disable marksi append-to-esc update-marksi esci))))


 (defthm temp24.12
   (implies (stack-contains-validated-edges stack marks graph nodeset)
            (subsetp (A-dests-of node (st-filter-2marked-nodes (cdr (assoc node stack)) marks) graph nodeset)
                     (esci node marks)))
   :hints (("Goal" :in-theory (disable marksi neighborsi neighbors->destsi esci))))
(defthm temp24.14
  (implies (and (endp (st-filter-2marked-nodes (setminus (neighborsi node graph) stackedneighbors) marks))
                (subsetp (A-dests-of node (st-filter-2marked-nodes stackedneighbors marks) graph nodeset) (esci node marks))
                (A-invariant-escs n nodes marks graph nodeset))
           (A-invariant-escs n (remove-equal node nodes) marks graph nodeset))
  :hints (("Goal" :in-theory (disable esci marksi))))
(defthm update-marksi-2-append-to-esc-preserves-A-invariant-escs-v2
  (let ((marks-after (update-marksi node 2 (append-to-esc node (A-dests-of node (st-filter-2marked-nodes (neighborsi node graph) marks) graph nodeset) marks))))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (A-natp nodes)
                  (natp node)
                  (<= n (nodes-length nodeset))
                  (A-invariant-escs n nodes marks graph nodeset))
             (A-invariant-escs n (append (st-filter-3parents node (nodes-length nodeset) marks graph nodeset)
                                         (remove-equal node nodes))
                               marks-after graph nodeset)))
  :hints (("Goal" :in-theory (disable update-marksi append-to-esc esci depi marksi neighborsi nodesi)
                  :induct (A-invariant-escs n nodes marks graph nodeset))))
(defthm temp24.15
  (implies (and (A-invariant-escs n nodes marks graph nodeset)
                (not (equal (marksi (car nodes) marks) 3))
                (not (equal (marksi (car nodes) marks) 4)))
           (A-invariant-escs n (cdr nodes) marks graph nodeset)))
(defthm step2-ensures-invariant-escs-total-inductive
  (let ((marks-after (process-escs-eff nodes stack marks graph nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  (A-valid-nodes nodes nodeset)
                  ;;Invariant
                  (A-consp stack)
                  (A-natp (keys stack))
                  (stack-contains-validated-edges stack marks graph nodeset)
                  (A-invariant-escs (nodes-length nodeset) nodes marks graph nodeset))
             (invariant-escs-total (nodes-length nodeset) marks-after graph nodeset)))
  :hints (("Goal" :in-theory (e/d (append-remove-l-and-r) (update-marksi append-to-esc esci depi marksi neighborsi remove-equal-append A-valid-nodes-append))
                  :do-not '(eliminate-destructors generalize)
                  :induct (process-escs-eff nodes stack marks graph nodeset))
          ("Subgoal *1/4" :use ((:instance update-marksi-2-append-to-esc-preserves-A-invariant-escs
                                 (node (car nodes))
                                 (stackedneighbors (cdr (assoc (car nodes) stack)))
                                 (n (nodes-length nodeset)))))
          ("Subgoal *1/5.2" :use ((:instance append-to-esc-preserves-A-invariant-escs
                                   (node (car nodes))
                                   (stackedneighbors (cdr (assoc (car nodes) stack)))
                                   (n (nodes-length nodeset)))))
          ("Subgoal *1/6" :use (:instance temp24.14
                                (n (nodes-length nodeset))
                                (node (car nodes))
                                (stackedneighbors (cdr (assoc (car nodes) stack)))))
          ("Subgoal *1/8.2" :use ((:instance update-marksi-2-append-to-esc-preserves-A-invariant-escs-v2
                                   (node (car nodes))
                                   (n (nodes-length nodeset)))))))

(defthm temp10.12
  (implies (A-invariant-escs n (append x y) marks graph nodeset)
           (A-invariant-escs n (append x (cons a y)) marks graph nodeset)))
(defthm invariant-escs-total-holds-after-step2
  (A-invariant-escs n (append (filter-3marked-nodes n marks nodeset)
                              (filter-4marked-nodes n marks nodeset))
                    marks graph nodeset)
  :hints (("Goal" :in-theory (disable update-marksi update-depi esci depi marksi neighborsi))))
(defthm temp10.9
  (implies (<= n (nodes-length nodeset))
           (A-valid-nodes (filter-4marked-nodes n marks nodeset) nodeset)))
(defthm temp10.10
  (equal (st-filter-34marked-nodes (filter-3marked-nodes n marks nodeset) marks)
         (filter-3marked-nodes n marks nodeset)))
(defthm temp10.11
  (equal (st-filter-34marked-nodes (filter-4marked-nodes n marks nodeset) marks)
         (filter-4marked-nodes n marks nodeset)))
(defthm step2-ensures-invariant-escs-total
  (let ((marks-after (process-escs-eff (append (filter-3marked-nodes (nodes-length st-nodeset) marks nodeset)
                                               (filter-4marked-nodes (nodes-length st-nodeset) marks nodeset))
                                       nil
                                       marks graph nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph))
             (invariant-escs-total (nodes-length nodeset) marks-after graph nodeset)))
  :hints (("Goal" :in-theory (disable update-marksi append-to-esc esci depi marksi neighborsi)
                  :use (:instance step2-ensures-invariant-escs-total-inductive
                        (stack nil)
                        (nodes (append (filter-3marked-nodes (nodes-length st-nodeset) marks nodeset)
                                               (filter-4marked-nodes (nodes-length st-nodeset) marks nodeset)))))))
;; the spec of invariant-escs-total
(defthm spec-of-invariant-escs-total
  (implies (and (invariant-escs-total n marks graph nodeset)
                (equal (marksi i marks) 3)
                (equal (nodesi i nodeset) 1)
                (natp n)
                (natp i)
                (< i n))
           (subsetp (A-dests-of i (st-filter-2marked-nodes (neighborsi i graph) marks) graph nodeset)
                    (esci i marks))))
;; invariant-escs-total holds initially
(defthm A-clear-implies-invariant-escs-total
  (implies (A-clear n marks)
           (invariant-escs-total n marks graph nodeset)))
;; END invariant-escs-total


;; BEGIN st-filter-1marked-nodes=nil
;; This is also an invariant: there are no 1-marked nodes. Nodes can only be marked 1 during step 1, but not before or after this step.
(defthm st-filter-1marked-nodes-subsetp
  (implies (and (st-filter-1marked-nodes nodes1 marks)
                (subsetp nodes1 nodes2))
           (st-filter-1marked-nodes nodes2 marks)))
(defthmd step1-leaves-no-1markings
  (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                (A-valid-nodes nodes nodeset)
                (natp prev)
                (natp node)
                (equal (marksi node (st-escapable-inv nodes prev  graph marks nodeset)) 1))
           (equal (marksi node marks) 1))
  :hints (("Goal" :in-theory (disable esci depi update-marksi neighborsi update-depi update-esci marksi dests-of-edge update-marksi valid-graph)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset)
                  :do-not '(eliminate-destructors generalize))))
;; step 1 preserves st-filter-1marked-nodes=nil
(defthm step1-makes-no-new-1markings
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                  (A-natp nodes2)
                  (natp prev))
             (subsetp (st-filter-1marked-nodes nodes2 marks-after)
                      (st-filter-1marked-nodes nodes2 marks))))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :in-theory (disable esci depi update-marksi neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi))
          ("Subgoal *1/5" :use (:instance step1-leaves-no-1markings
                                (node (car nodes2))))))
(defthm A-equal-subsetp
  (implies (and (A-equal y a)
                (subsetp x y))
           (A-equal x a)))
(defthm st-filter-1marked-nodes-update-marksi-4
  (implies (A-equal (st-filter-1marked-nodes nodes marks) node)
           (equal (st-filter-1marked-nodes nodes (update-marksi node 4 marks)) nil)))
(defthm st-filter-1marked-nodes-update-marksi-3
  (implies (A-equal (st-filter-1marked-nodes nodes marks) node)
           (equal (st-filter-1marked-nodes nodes (update-marksi node 3 marks)) nil)))
(defthm st-filter-1marked-nodes-update-marksi-2
  (implies (A-equal (st-filter-1marked-nodes nodes marks) node)
           (equal (st-filter-1marked-nodes nodes (update-marksi node 2 marks)) nil)))
(defthm st-filter-1marked-nodes-update-marksi-1
  (implies (and (natp node)
                (A-natp nodes)
                (not (st-filter-1marked-nodes nodes marks)))
           (A-equal (st-filter-1marked-nodes nodes (update-marksi node 1 marks)) node))
  :hints (("Goal" :in-theory (disable marksi update-marksi))))
(defthm rewite-subsetp->A-equal
  (implies (and (A-equal y a)
                (consp y))
           (iff (subsetp x y)
                (A-equal x a))))
(defthm remove-all-elts-yeilds-nil
  (implies (A-equal x a)
           (equal (remove-equal a x) nil)))
;; step 1 preserves st-filter-1marked-nodes=nil
(defthm step1-preserves-st-filter-1marked-nodes=nil
  (let* ((marks-after (st-escapable-inv (list root) -1 graph marks nodeset)))
    (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                  (A-natp nodes)
                  (natp root))
             (implies (st-filter-1marked-nodes nodes marks-after)
                      (st-filter-1marked-nodes nodes marks))))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :in-theory (disable esci depi update-marksi neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi)
                  :expand (st-escapable-inv (list root) -1 graph marks nodeset)
                  :use ((:instance step1-makes-no-new-1markings
                         (nodes2 nodes)
                         (nodes (neighborsi root graph))
                         (prev root)
                         (marks (update-marksi root 1 marks)))
                        (:instance A-equal-subsetp
                         (y (st-filter-1marked-nodes nodes (update-marksi root 1 marks)))
                         (x (st-filter-1marked-nodes nodes (st-escapable-inv (neighborsi root graph) root graph (update-marksi root 1 marks) nodeset)))
                         (a root))))))
;; step 2 preserves st-filter-1marked-nodes=nil
(defthm step2-does-not-mark-nodes-1
  (let* ((marks-after (process-escs-eff nodes stack marks graph nodeset)))
    (implies (and (natp i)
                  (equal (marksi i marks-after) 1))
             (equal (marksi i marks) 1)))
  :hints (("Goal" :in-theory (disable marksi update-marksi update-depi update-esci neighborsi nodesi st-filter-3parents-update-marksi-append-to-esc upwards-4marked-reach-update-marksi-append-to-esc
                                      UPWARDS-4MARKED-REACH-APPEND-TO-ESC))))
(defthm step2-preserves-st-filter-1marked-nodes=nil
  (let* ((marks-after (process-escs-eff nodes2 stack marks graph nodeset)))
    (implies (and (A-natp nodes)
                  (st-filter-1marked-nodes nodes marks-after))
             (st-filter-1marked-nodes nodes marks)))
  :hints (("Goal" :in-theory (disable marksi update-marksi))
          ("Subgoal *1/6" :use (:instance step2-does-not-mark-nodes-1
                                (i (car nodes))
                                (nodes nodes2)))))
;; the algorithm preserves st-filter-1marked-nodes
(defthm algo-preserves-st-filter-1marked-nodes=nil
  (let* ((marks-after (st-A-nodes-escapable-inv n graph marks nodeset)))
    (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                  (A-natp nodes))
             (implies (st-filter-1marked-nodes nodes marks-after)
                      (st-filter-1marked-nodes nodes marks))))
  :hints (("Subgoal *1/3" :use (:instance step1-preserves-st-filter-1marked-nodes=nil
                                (root (1- n))))))
;; st-filter-1marked-nodes holds initially
(defthm spec-of-A-clear
  (implies (and (A-clear n marks)
                (natp n)
                (natp i)
                (< i n))
           (equal (marksi i marks) 0)))
(defthm A-clear-implies-st-filter-1marked-nodes=nil
  (implies (and (A-clear (nodes-length nodeset) marks)
                (A-valid-nodes nodes nodeset))
           (not (st-filter-1marked-nodes nodes marks))))
;; END st-filter-1marked-nodes=nil


;; BEGIN legal-mark
;; This is also an invariant: marks are legal, i.e., either 0, 1, 2 or 3. We only need to prove this for step 1.
(defthmd step1-does-not-mark-nodes-1
  (let* ((marks-after (st-escapable-inv (list node) -1 graph marks nodeset)))
    (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                  (natp node)
                  (natp node2)
                  (equal (marksi node2 marks-after) 1))
           (equal (marksi node2 marks) 1)))
  :hints (("Goal" :in-theory (disable esci depi update-marksi neighborsi update-depi update-esci marksi dests-of-edge update-marksi valid-graph temp1.16)
                  :expand (st-escapable-inv (list node) -1 graph marks nodeset)
                  :use ((:instance step1-leaves-no-1markings
                         (node node2)
                         (nodes (neighborsi node graph))
                         (prev node)
                         (marks (update-marksi node 1 marks)))))))
(defthm step1-marks-node-123
  (let* ((marks-after (st-escapable-inv (list node) -1 graph marks nodeset)))
    (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                  (A-valid-nodes (st-all-nodes nodeset) nodeset)
                  (natp node)
                  (< node (nodes-length nodeset))
                  (equal (nodesi node nodeset) 1))
             (or (equal (marksi node marks-after) 1)
                 (equal (marksi node marks-after) 2)
                 (equal (marksi node marks-after) 3)
                 (equal (marksi node marks-after) 4))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable esci depi update-marksi neighborsi update-depi update-esci marksi dests-of-edge update-marksi valid-graph)
                  :expand (st-escapable-inv (list node) -1 graph marks nodeset))))
(defthmd step1-preserves-legal-mark-not0
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                  (A-valid-nodes nodes nodeset)
                  (natp prev)
                  (natp node)
                  (not (equal (marksi node marks) 0))
                  (legal-mark (marksi node marks)))
             (legal-mark (marksi node marks-after))))
  :hints (("Goal" :in-theory (disable esci depi update-marksi neighborsi update-depi update-esci marksi dests-of-edge update-marksi valid-graph st-escapable-inv)
                  :do-not '(eliminate-destructors generalize)
                  :use ((:instance algo-preserves-3marking)
                        (:instance algo-preserves-1marking)
                        (:instance algo-preserves-2marking)
                        (:instance algo-preserves-4marking)))))
(defthmd step1-gives-0marked-node-legal-mark
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                  (A-valid-nodes nodes nodeset)
                  (natp prev)
                  (natp node)
                  (< node (nodes-length nodeset))
                  (equal (marksi node marks) 0))
             (legal-mark (marksi node marks-after))))
  :hints (("Goal" :in-theory (disable esci depi update-marksi neighborsi update-depi update-esci marksi dests-of-edge update-marksi valid-graph legal-mark)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset)
                  :do-not '(eliminate-destructors generalize))
          ("Subgoal *1/7" :use ((:instance step1-preserves-legal-mark-not0
                                 (nodes (cdr nodes))
                                 (marks (update-marksi (car nodes) 2 (append-to-esc prev (dests-of-edge prev (car nodes) graph nodeset)
                                                                                    (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))
                                (:instance step1-preserves-legal-mark-not0
                                 (nodes (cdr nodes))
                                 (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 3
                                                                                                                          (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))
                                (:instance step1-preserves-legal-mark-not0
                                 (nodes (cdr nodes))
                                 (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 4
                                                                                                                          (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))))

          ("Subgoal *1/5" :use ((:instance algo-preserves-2marking
                                 (node (car nodes))
                                 (nodes (cdr nodes))
                                 (marks (update-marksi (car nodes) 2 (append-to-esc prev (dests-of-edge prev (car nodes) graph nodeset) marks))))))))
;; step 1 preserves legal-mark (inductive)
(defthm step1-preserves-legal-mark-inductive
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                  (A-valid-nodes nodes nodeset)
                  (natp prev)
                  (natp node)
                  (< node (nodes-length nodeset))
                  (legal-mark (marksi node marks)))
             (legal-mark (marksi node marks-after))))
  :hints (("Goal" :in-theory (disable esci depi update-marksi neighborsi update-depi update-esci marksi dests-of-edge update-marksi valid-graph st-escapable-inv)
                  :use ((:instance algo-preserves-2marking)
                        (:instance algo-preserves-3marking)
                        (:instance algo-preserves-4marking)
                        (:instance algo-preserves-1marking)
                        (:instance step1-gives-0marked-node-legal-mark)))))
(defthm legal-mark-update-marksi
  (implies (and (natp i)
                (natp j)
                (or (equal x 0) (equal x 1) (equal x 2) (equal x 3) (equal x 4))
                (legal-mark (marksi i marks)))
           (legal-mark (marksi i (update-marksi j x marks)))))
;; step 1 preserves legal-mark
(defthm step1-preserves-legal-mark
  (let* ((marks-after (st-escapable-inv (list node) -1 graph marks nodeset)))
    (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                  (natp node2)
                  (< node2 (nodes-length nodeset))
                  (legal-mark (marksi node2 marks)))
             (legal-mark (marksi node2 marks-after))))
  :otf-flg t
  :hints (("Goal" :in-theory (disable esci depi update-marksi neighborsi update-depi update-esci marksi dests-of-edge update-marksi valid-graph legal-mark)
                  :expand (st-escapable-inv (list node) -1 graph marks nodeset)
                  :use ((:instance step1-preserves-legal-mark-inductive
                         (node node2)
                         (nodes (neighborsi node graph))
                         (prev node)
                         (marks (update-marksi node 1 marks)))))))#|ACL2s-ToDo-Line|#

;;END legal-mark

