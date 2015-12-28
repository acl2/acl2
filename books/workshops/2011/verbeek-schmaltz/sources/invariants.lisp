#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#


(in-package "ACL2")
(include-book "algorithm")

;; This file contains the proof of correctness of the algorithm. Theorem dlf<->algo-returns-t formulates this correctness. It uses theorems dlf->algo-returns-t and dl->algo-returns-nil.
;;
;; For those who have read the ICPP'10 submission:
;; Lemma 1: this lemma is basically formalized in many different theorems here.
;; Lemma 2: this is theorem step2-ensures-invariant-escs-total
;; Lemma 3: this is theorem dlf->not3
;; Lemma 4: this is theorems step1-preserves-dl->not2 and step2-preserves-dl->not2
;; Collorary 1: dlf<->algo-returns-t
;; The proof as it has been written omits, for sake of readability, formal details on the formal proof. The structure that is described in Section 4C is however accurate:
;; Invariant 1: invariant-deps
;; Invariant 2: invariant-escs2
;; Invariant 3: invariant-comp
;; Invariant 4: invariant-unresolved
;; Invariant 5: invariant-3marks
;; Invariant 6: invariant-3marks
;;
;; Structure of this file
;;
;; FUNCTIONS
;;    Invariants
;;    other functions
;; THEOREMS
;; 1.) Bogus subgoal
;;     The assertion in st-escapable-inv creates a bogus subgoal (namely, what if the assertion does not hold?). We force ACL2 to use these specific theorems to prove that this cannot occur and
;;     thereby discharge this bogus subgoal automatically.
;; 2.) Theorems on functions
;;     Some standard theorems on some functions.
;; 3.) Correctness of invariants
;;     The main part of the file. We first prove that all invariants are preserved by the algorithm, i.e., that they are actual invariants. Then we prove that the invariants hold initially.
;;     More detailed, for each invariant x, we prove the following:
;;          step 1 preserves invariant-x (inductive)
;;             We prove that x is preserved by st-escapable-inv. First we prove this by induction, where 'prev' is some node (a parent of 'nodes').
;;          step 1 preserves invariant-x
;;             Then we prove that the actual call of st-escapable-inv, with 'prev' = -1 preserves x.
;;          step 2 preserves invariant-x
;;             We prove the process-escs-eff preserves x.
;;          the algorithm preserves invariant-x
;;             As a result of these proofs, we can prove that st-A-nodes-escapable-inv preserves x, i.e., x is an invariant to the whole algorithm.
;;          the spec of invariant-x
;;             Theorems stating the specification of x.
;;          invariant-x holds initially
;;             A proof that, if all marks are empty, x holds.
;; 4.) Deadlock -> algorithm returns nil
;;     Using the invariants as assumption we prove correctness of the algorithm wrt the condition
;; 5.) Algorithm returns nil --> deadlock
;;     Using the invariants as assumption we prove correctness of the algorithm wrt the condition
;; 6.) Final Theorem
;;     The final theorem, a collorary of 4.) and 5.).
;;
;; For questions mail f.verbeek@cs.ru.nl



;;FUNCTIONS
(defun st-escapep (node subgraph dests st-graph)
  (declare (xargs :stobjs st-graph
                  :verify-guards nil))
  (if (endp dests)
    t
    (and (not (subsetp (st-filter-neighbors-for-dest (neighbors->destsi node st-graph) (car dests)) subgraph))
         (st-escapep node subgraph (cdr dests) st-graph))))
(defun union-of (X)
  (if (endp X)
    nil
    (append (car X) (union-of (cdr X)))))
(defun values-alist (alist)
  (if (endp alist)
    nil
    (cons (cdar alist) (values-alist (cdr alist)))))
(defun st-find-escape (nodes subgraph st-graph)
  (declare (xargs :stobjs st-graph
                  :verify-guards nil))
  (cond ((endp nodes)
         nil)
        ((and (consp (neighborsi (car nodes) st-graph))
              (st-escapep (car nodes) subgraph (union-of (values-alist (neighbors->destsi (car nodes) st-graph))) st-graph))
         (car nodes))
        (t
         (st-find-escape (cdr nodes) subgraph st-graph))))
(defun st-A-parents (nodes st-graph)
  (declare (xargs :verify-guards nil
                  :stobjs st-graph))
  (if (endp nodes)
    t
    (and (consp (neighborsi (car nodes) st-graph))
         (st-A-parents (cdr nodes) st-graph))))
(defun-sk st-A-subgraphs-E-escape (graph nodeset)
  (forall (subgraph)
          (implies (and (consp subgraph)
                        (st-A-parents subgraph graph)
                        (A-valid-nodes subgraph nodeset))
                   (st-find-escape subgraph subgraph graph))))
;; Functions concerning valid dependency graphs
(defun is-keys-of-alist (x alist)
  (if (or (endp x) (endp alist))
    (and (endp x) (endp alist))
    (and (equal (caar alist) (car x))
         (is-keys-of-alist (cdr x) (cdr alist)))))
(defun keys (alist)
  (if (endp alist)
    nil
    (cons (caar alist) (keys (cdr alist)))))
(defun filled-graphp (n st-graph)
  (declare (xargs :stobjs (st-graph)
                  :verify-guards nil))
  (if (zp n)
    t
    (and (is-keys-of-alist (neighborsi (1- n) st-graph) (neighbors->destsi (1- n) st-graph))
         (no-duplicatesp-equal (keys (neighbors->destsi (1- n) st-graph)))
         (not (member-equal (1- n) (keys (neighbors->destsi (1- n) st-graph))))
         (filled-graphp (1- n) st-graph))))
;; Functions used in the proof
;; INVARIANT
;; invariant-escs2 states that all destinations added to the escs-array, lead to a 2-marked neighbor
(defun find-2node (nodes st-marks)
  (declare (xargs :stobjs st-marks
                  :verify-guards nil))
  (cond ((endp nodes)
         nil)
        ((equal (marksi (car nodes) st-marks) 2)
         (car nodes))
        (t
         (find-2node (cdr nodes) st-marks))))
(defun A-dests-E-2neighbor (node dests st-marks st-graph)
  (declare (xargs :verify-guards nil
                  :stobjs (st-marks st-graph)))
  (if (endp dests)
    t
    (and (find-2node (st-filter-neighbors-for-dest (neighbors->destsi node st-graph) (car dests)) st-marks)
         (A-dests-E-2neighbor node (cdr dests) st-marks st-graph))))
(defun invariant-escs2 (n st-marks st-graph)
  (declare (xargs :verify-guards nil
                  :stobjs (st-marks st-graph)))
  (if (zp n)
    t
    (and (A-dests-E-2neighbor (1- n) (esci (1- n) st-marks) st-marks st-graph)
         (invariant-escs2 (1- n) st-marks st-graph))))
;; INVARIANT
;; invariant-comp states that for all 2- and 3-marked nodes, all neighbors are in either deps are escs
(defun invariant-comp (n st-marks st-graph st-nodeset)
  (declare (xargs :stobjs (st-marks st-graph st-nodeset)
                  :verify-guards nil))
  (cond ((zp n)
         t)
        ((or (equal (marksi (1- n) st-marks) 2)
             (equal (marksi (1- n) st-marks) 3)
             (equal (marksi (1- n) st-marks) 4))
         (and (subsetp (A-dests-of (1- n) (neighborsi (1- n) st-graph) st-graph st-nodeset) (append (depi (1- n) st-marks) (esci (1- n) st-marks)))
              (invariant-comp (1- n) st-marks st-graph st-nodeset)))
        (t
         (invariant-comp (1- n) st-marks st-graph st-nodeset))))
;; INVARIANT
;; invariant-3marks states that all 3-marked nodes are valid nodes, are parents and have no unmarked neighbors.
(defun invariant-3marks (n st-marks st-graph st-nodeset)
  (declare (xargs :stobjs (st-marks st-graph st-nodeset)
                  :verify-guards nil))
  (cond ((zp n)
         t)
        ((equal (marksi (1- n) st-marks) 3)
         (and (equal (nodesi (1- n) st-nodeset) 1)
              (consp (neighborsi (1- n) st-graph))
              (equal (st-filter-unmarked123-nodes (neighborsi (1- n) st-graph) st-marks) nil)
              (invariant-3marks (1- n) st-marks st-graph st-nodeset)))
        (t
         (invariant-3marks (1- n) st-marks st-graph st-nodeset))))
;; INVARIANT
;; invariant-deps states that all objects in deps-arrays are valid destinations leading to neighbors
(defun invariant-deps (n st-marks st-graph st-nodeset)
  (declare (xargs :stobjs (st-marks st-graph st-nodeset)
                  :verify-guards nil))
  (if (zp n)
    t
    (and (subsetp (depi (1- n) st-marks) (union-of (values-alist (neighbors->destsi (1- n) st-graph))))
         (A-valid-nodes (depi (1- n) st-marks) st-nodeset)
         (invariant-deps (1- n) st-marks st-graph st-nodeset))))
;;INVARIANT
;; invariant-unresolved states that all 3-marked nodes are unresolved, i.e., there is at least one destination in deps that is not in escs.
(defun invariant-unresolved (n st-marks st-graph st-nodeset)
  (declare (xargs :stobjs (st-marks st-graph st-nodeset)
                  :verify-guards nil))
  (cond ((zp n)
         t)
        ((equal (marksi (1- n) st-marks) 3)
         (and (unresolved (1- n) st-marks)
              (invariant-unresolved (1- n) st-marks st-graph st-nodeset)))
        (t
         (invariant-unresolved (1- n) st-marks st-graph st-nodeset))))
;; INVARIANT
;; A-invariant-escs states that the esc-array  of any 3-marked node contains all destinations leading to all 2-marked neighbors.
;; Step 1 does not completely preserves this invariant, i.e., it may not hold for a set of uncertain nodes. Step 2 corrects this, after
;; step 2 the invariant holds totally.
(defun A-invariant-escs (n uncertain st-marks st-graph st-nodeset)
  (declare (xargs :stobjs (st-marks st-graph st-nodeset)
                  :verify-guards nil))
  (cond ((zp n)
         t)
        ((and (equal (marksi (1- n) st-marks) 3)
              (equal (nodesi (1- n) st-nodeset) 1)
              (not (member-equal (1- n) uncertain)))
         (and (subsetp (A-dests-of (1- n) (st-filter-2marked-nodes (neighborsi (1- n) st-graph) st-marks) st-graph st-nodeset)
                       (esci (1- n) st-marks))
              (A-invariant-escs (1- n) uncertain st-marks st-graph st-nodeset)))
        (t
         (A-invariant-escs (1- n) uncertain st-marks st-graph st-nodeset))))
(defun invariant-escs-total (n st-marks st-graph st-nodeset)
  (declare (xargs :stobjs (st-marks st-graph st-nodeset)
                  :verify-guards nil))
  (cond ((zp n)
         t)
        ((and (equal (marksi (1- n) st-marks) 3)
              (equal (nodesi (1- n) st-nodeset) 1))
         (and (subsetp (A-dests-of (1- n) (st-filter-2marked-nodes (neighborsi (1- n) st-graph) st-marks) st-graph st-nodeset)
                       (esci (1- n) st-marks))
              (invariant-escs-total (1- n) st-marks st-graph st-nodeset)))
        (t
         (invariant-escs-total (1- n) st-marks st-graph st-nodeset))))
;; Other functions
(defun A-clear (n st-marks)
  (declare (xargs :stobjs (st-marks)
                  :verify-guards nil))
  (if (zp n)
    t
    (and (equal (depi (1- n) st-marks) nil)
         (equal (esci (1- n) st-marks) nil)
         (equal (marksi (1- n) st-marks) 0)
         (A-clear (1- n) st-marks))))
(defun legal-mark (x)
  (or (equal x 0)
      (equal x 1)
      (equal x 2)
      (equal x 3)
      (equal x 4)))
(defun find-member-not-in (x y)
  (cond ((endp x)
         nil)
        ((not (member-equal (car x) y))
         (car x))
        (t
         (find-member-not-in (cdr x) y))))
(defun st-filter-1marked-nodes (nodes st-marks)
  (declare (xargs :stobjs (st-marks)
                  :verify-guards nil))
  (cond ((endp nodes)
         nil)
        ((equal (marksi (car nodes) st-marks) 1)
         (cons (car nodes) (st-filter-1marked-nodes (cdr nodes) st-marks)))
        (t
         (st-filter-1marked-nodes (cdr nodes) st-marks))))
(defun A-equal (x a)
  (if (endp x)
    t
    (and (equal (car x) a)
         (A-equal (cdr x) a))))



;; THEOREMS
;;
;;---------------------------------------
;;---------------------------------------
;; 1.) Bogus subgoal
;;---------------------------------------
;;---------------------------------------
;; The following theorems enable ACL2 to force its way through the bogus subgoal generate by the assertion.
(defthm forced--st-filter-unmarked123-nodes-update-marksi-2
  (implies (and (force (natp node))
; Matt K. mod for v7-2: Don't force assumption below with free variable.
                (A-valid-nodes nodes nodeset))
           (equal (st-filter-unmarked123-nodes nodes (update-marksi node 2 marks))
                  (remove-equal node (st-filter-unmarked123-nodes nodes marks))))
    :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi))))
(defthm forced--st-filter-unmarked123-nodes-update-marksi-3
  (implies (and (force (natp node))
; Matt K. mod for v7-2: Don't force assumption below with free variable.
                (A-valid-nodes nodes nodeset))
           (equal (st-filter-unmarked123-nodes nodes (update-marksi node 3 marks))
                  (remove-equal node (st-filter-unmarked123-nodes nodes marks))))
    :hints (("Goal" :do-not '(eliminate-destructors generalize)
                    :in-theory (disable esci depi update-marksi marksi-update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi))))
(defthmd spec-of-st-filter-unmarked123-nodes
  (implies (and (not (equal (marksi node marks) 1))
                (not (equal (marksi node marks) 2))
                (not (equal (marksi node marks) 3))
                (not (equal (marksi node marks) 4))
                (member-equal node nodes))
           (member-equal node (st-filter-unmarked123-nodes nodes marks))))
(defthm forced--number-of-unmarked-nodes-decreases-in-step-1
  (implies (and (force (valid-graph (nodes-length st-nodeset) graph nodeset))
                (force (A-valid-nodes (show-nodeset (nodes-length nodeset) nodeset) nodeset))
                (force (natp (car nodes)))
                (force (equal (nodesi (car nodes) nodeset) 1))
                (force (not (equal (marksi (car nodes) marks) 1)))
                (force (not (equal (marksi (car nodes) marks) 2)))
                (force (not (equal (marksi (car nodes) marks) 3)))
                (force (not (equal (marksi (car nodes) marks) 4)))
                (force (< (car nodes) (nodes-length nodeset))))
           (< (len (st-filter-unmarked123-nodes
                    (show-nodeset (nodes-length nodeset) nodeset)
                    (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))
              (len (st-filter-unmarked123-nodes (show-nodeset (nodes-length nodeset) nodeset) marks))))
  :rule-classes :linear
  :otf-flg t
  :hints (("Goal" :in-theory (disable marksi update-marksi neighborsi)
                  :use ((:instance algo-does-not-increase-number-of-unmarked-nodes
                         (nodes1 (show-nodeset (nodes-length nodeset) nodeset))
                         (nodes (neighborsi (car nodes) graph))
                         (prev (car nodes))
                         (marks (update-marksi (car nodes) 1 marks)))
                        (:instance spec-of-st-filter-unmarked123-nodes
                         (node (car nodes))
                         (nodes (show-nodeset (nodes-length nodeset) nodeset)))))))
(defthmd 3-marked-not-in-st-filter-unmarked123-nodes
  (implies (or (marked node marks)
               (equal (marksi node marks) 3))
           (not (member-equal node (st-filter-unmarked123-nodes nodes marks)))))
(defthm forced--node-unmarked-after-first-recursive-call
  (implies (and (force (valid-graph (nodes-length nodeset) graph nodeset))
                (force (natp node))
                (force (natp prev)))
           (equal (occurrences-equal node (st-filter-unmarked123-nodes nodes2 (st-escapable-inv nodes prev graph (update-marksi node 1 marks) nodeset)))
                  0))
  :otf-flg t
  :hints (("Goal" :in-theory (disable esci depi update-marksi neighborsi update-depi update-esci nodesi marksi)
                  :use ((:instance 3-marked-not-in-st-filter-unmarked123-nodes
                         (nodes nodes2)
                         (marks (st-escapable-inv nodes prev  graph (update-marksi node 1 marks) nodeset)))
                        (:instance algo-preserves-1marking
                         (marks (update-marksi node 1 marks)))))))

;;---------------------------------------
;;---------------------------------------
;; 2.) Theorems on functions
;;---------------------------------------
;;---------------------------------------





;;---------------------------------------
;;---------------------------------------
;; 3.) Correctness of invariants
;;---------------------------------------
;;---------------------------------------
;; BEGIN invariant-escs2
(defthm find-2node-update-depi
  (equal (find-2node nodes (update-depi i x marks))
         (find-2node nodes marks)))
(defthm A-dests-E-2neighbor-update-depi
  (equal (A-dests-E-2neighbor n dests (update-depi i x marks) graph)
         (A-dests-E-2neighbor n dests marks graph))
  :hints (("Goal" :in-theory (disable depi update-marksi update-depi))))
(defthm invariant-escs2-append-to-dep
  (equal (invariant-escs2 n (append-to-dep i x marks) graph)
         (invariant-escs2 n marks graph))
  :hints (("Goal" :in-theory (disable depi update-marksi update-depi))))

(defthm find-2node-update-marksi-1
  (implies (and (not (equal (marksi node marks) 2))
                (find-2node nodes marks))
           (find-2node nodes (update-marksi node 1 marks))))
(defthm A-dests-E-2neighbor-update-marksi-1
  (implies (and (not (equal (marksi node marks) 2))
                (A-dests-E-2neighbor n dests marks graph))
           (A-dests-E-2neighbor n dests (update-marksi node 1 marks) graph))
  :hints (("Goal" :in-theory (disable depi update-marksi update-depi))))
(defthm invariant-escs2-update-marksi-1
  (implies (and (not (equal (marksi node marks) 2))
                (invariant-escs2 n marks graph))
         (invariant-escs2 n (update-marksi node 1 marks) graph))
  :hints (("Goal" :in-theory (disable depi update-marksi update-depi))))

(defthm find-2node-update-marksi-3
  (implies (and (not (equal (marksi node marks) 2))
                (find-2node nodes marks))
           (find-2node nodes (update-marksi node 3 marks))))
(defthm A-dests-E-2neighbor-update-marksi-3
  (implies (and (not (equal (marksi node marks) 2))
                (A-dests-E-2neighbor n dests marks graph))
           (A-dests-E-2neighbor n dests (update-marksi node 3 marks) graph))
  :hints (("Goal" :in-theory (disable depi update-marksi update-depi))))
(defthm invariant-escs2-update-marksi-3
  (implies (and (not (equal (marksi node marks) 2))
                (invariant-escs2 n marks graph))
         (invariant-escs2 n (update-marksi node 3 marks) graph))
  :hints (("Goal" :in-theory (disable depi update-marksi update-depi))))

(defthm find-2node-update-marksi-4
  (implies (and (not (equal (marksi node marks) 2))
                (find-2node nodes marks))
           (find-2node nodes (update-marksi node 4 marks))))
(defthm A-dests-E-2neighbor-update-marksi-4
  (implies (and (not (equal (marksi node marks) 2))
                (A-dests-E-2neighbor n dests marks graph))
           (A-dests-E-2neighbor n dests (update-marksi node 4 marks) graph))
  :hints (("Goal" :in-theory (disable depi update-marksi update-depi))))
(defthm invariant-escs2-update-marksi-4
  (implies (and (not (equal (marksi node marks) 2))
                (invariant-escs2 n marks graph))
         (invariant-escs2 n (update-marksi node 4 marks) graph))
  :hints (("Goal" :in-theory (disable depi update-marksi update-depi))))

(defthm A-dests-E-2neighbor-append
  (equal (A-dests-E-2neighbor node (append x y) marks graph)
         (and (A-dests-E-2neighbor node x marks graph)
              (A-dests-E-2neighbor node y marks graph))))
(defthm find-2node-update-marksi-update-esci
  (equal (find-2node nodes (update-marksi i x (update-esci j y marks)))
         (find-2node nodes (update-marksi i x marks))))
(defthm find-2node-update-marksi-update-depi
  (equal (find-2node nodes (update-marksi i x (update-depi j y marks)))
         (find-2node nodes (update-marksi i x marks))))
(defthm find-2node-update-marksi-2
  (implies (and (A-natp nodes)
                (find-2node nodes marks))
           (find-2node nodes (update-marksi i 2 marks))))
(defthm A-natp-st-filter-neighbors-for-dest
  (implies (and (is-keys-of-alist neighbors neighbors->destsi)
                (A-natp neighbors))
           (A-natp (st-filter-neighbors-for-dest neighbors->destsi dest))))
(defthm neighbors-are-keys-of-neighbors->destsi
  (implies (and (< node n)
                (natp node)
                (natp n)
                (filled-graphp n graph))
           (is-keys-of-alist (neighborsi node graph) (neighbors->destsi node graph))))
(defthm A-dests-E-2neighbor-update-marksi-2-preserved
  (implies (and (filled-graphp (nodes-length nodeset) graph)
                (valid-graph (nodes-length nodeset) graph nodeset)
                (natp n)
                (< n (nodes-length nodeset))
                (A-dests-E-2neighbor n dests marks graph))
           (A-dests-E-2neighbor n dests (update-marksi neighbor 2 (append-to-esc node (dests-of-edge node neighbor graph nodeset) marks)) graph))
  :hints (("Goal" :in-theory (disable marksi esci update-marksi update-esci neighborsi neighbors->destsi))
          ("Subgoal *1/3" :use (:instance A-natp-st-filter-neighbors-for-dest
                                (dest (car dests))
                                (neighbors (neighborsi n graph))
                                (neighbors->destsi (neighbors->destsi n graph))))))
(defthm nodups-keys-neighbors->destsi
  (implies (and (< node n)
                (natp node)
                (natp n)
                (filled-graphp n graph))
           (no-duplicatesp-equal (keys (neighbors->destsi node graph)))))
(defthm rewrite-A-natp-keys
  (implies (is-keys-of-alist x alist)
           (iff (A-natp (keys alist))
                (A-natp x))))
(defthmd A-natp-keys-neighbors->destsi
  (implies (and (< node n)
                (natp node)
                (natp n)
                (filled-graphp n graph)
                (valid-graph n graph nodeset))
           (A-natp (keys (neighbors->destsi node graph)))))
(defthmd natp-key
  (implies (and (A-natp (keys alist))
                (member-equal field alist))
           (natp (car field))))
(defthm member-key-keys
  (implies (member-equal field alist)
           (member-equal (car field) (keys alist))))
(defthm assoc-key-yeilds-field
  (implies (and (equal key (car field))
                (member-equal field alist)
                (no-duplicatesp-equal (keys alist)))
           (equal (assoc key alist) field)))
(in-theory (disable member-key-keys assoc-key-yeilds-field));subsetp-append))
(defthm find-2node-in-neighbors-if-neighbors-is-marked-2
  (implies (and (filled-graphp (nodes-length nodeset) graph)
                (valid-graph (nodes-length nodeset) graph nodeset)
                (natp node)
                (< node (nodes-length nodeset))
                (natp neighbor)
                (subsetp neighbors->destsi (neighbors->destsi node graph))
                (member-equal dest (dests-of-edge node neighbor graph nodeset))
                (member-equal neighbor (keys neighbors->destsi)))
           (find-2node (st-filter-neighbors-for-dest neighbors->destsi dest) (update-marksi neighbor 2 marks)))
  :hints (("Goal" :in-theory (disable marksi esci update-marksi update-esci neighborsi neighbors->destsi A-natp-keys-neighbors->destsi))
          ("Subgoal *1/6" :use ((:instance assoc-key-yeilds-field
                                 (field (car neighbors->destsi))
                                 (key neighbor)
                                 (alist (neighbors->destsi node graph)))
                                (:instance nodups-keys-neighbors->destsi
                                 (n (nodes-length nodeset)))))
          ("Subgoal *1/4" :use ((:instance A-natp-keys-neighbors->destsi
                                 (n (nodes-length nodeset)))
                                (:instance natp-key
                                 (alist (neighbors->destsi node graph))
                                 (field (car neighbors->destsi)))))))
(defthm rewrite-member-keys
  (implies (is-keys-of-alist keys alist)
           (iff (member-equal key (keys alist))
                (member-equal key keys))))

(defthm A-dests-E-2neighbor-update-marksi-2
  (implies (and (filled-graphp (nodes-length nodeset) graph)
                (valid-graph (nodes-length nodeset) graph nodeset)
                (natp node)
                (< node (nodes-length nodeset))
                (natp neighbor)
                (member-equal neighbor (neighborsi node graph))
                (subsetp dests (dests-of-edge node neighbor graph nodeset)))
           (A-dests-E-2neighbor node dests (update-marksi neighbor 2 (append-to-esc node dests marks)) graph))
  :hints (("Goal" :in-theory (disable marksi esci update-marksi update-esci neighborsi neighbors->destsi))
          ("Subgoal *1/4" :use ((:instance find-2node-in-neighbors-if-neighbors-is-marked-2
                                 (neighbors->destsi (neighbors->destsi node graph))
                                 (dest (car dests)))
                                (:instance rewrite-member-keys
                                 (key neighbor)
                                 (keys (neighborsi node graph))
                                 (alist (neighbors->destsi node graph)))))))

(defthm update-marksi-2-append-escs-preserves-invariant-escs2
  (implies (and (filled-graphp (nodes-length nodeset) graph)
                (valid-graph (nodes-length nodeset) graph nodeset)
                (<= n (nodes-length nodeset))
                (natp node)
                (natp neighbor)
                (member-equal neighbor (neighborsi node graph))
                (invariant-escs2 n marks graph))
           (invariant-escs2 n (update-marksi neighbor 2 (append-to-esc node (dests-of-edge node neighbor graph nodeset) marks)) graph))
  :hints (("Goal" :in-theory (disable esci update-marksi update-esci dests-of-edge))
          ("Subgoal *1/3" :use ((:instance esci-update-esci-diff
                                   (i (1- n))
                                   (j node)
                                   (x (append (dests-of-edge node neighbor graph nodeset) (esci node marks))))
                                  (:instance A-dests-E-2neighbor-update-marksi-2-preserved
                                   (n (1- n))
                                   (dests (esci (1- n) marks)))
                                  (:instance A-dests-E-2neighbor-update-marksi-2
                                   (node (1- n))
                                   (dests (dests-of-edge node neighbor graph nodeset)))))))
;; step 1 preserves invariant-escs2 (inductive)
(defthm step1-preserves-invariant-escs2-inductive
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  (A-valid-nodes nodes nodeset)
                  (natp prev)
                  (subsetp nodes (neighborsi prev graph))
                  (invariant-escs2 (nodes-length nodeset) marks graph))
             (invariant-escs2 (nodes-length nodeset) marks-after graph)))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset)
                  :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi))))
(defthm update-marksi-2-preserves-A-dests-E-2neighbor
  (implies (and (filled-graphp (nodes-length nodeset) graph)
                (valid-graph (nodes-length nodeset) graph nodeset)
                (natp n)
                (< n (nodes-length nodeset))
                (A-dests-E-2neighbor n dests marks graph))
           (A-dests-E-2neighbor n dests (update-marksi node 2 marks) graph))
  :hints (("Goal" :in-theory (disable depi update-marksi update-depi neighborsi neighbors->destsi))
          ("Subgoal *1/4" :use (:instance A-natp-st-filter-neighbors-for-dest
                                (dest (car dests))
                                (neighbors (neighborsi n graph))
                                (neighbors->destsi (neighbors->destsi n graph))))))
(defthm update-marksi-2-preserves-invariant-escs2
  (implies (and (filled-graphp (nodes-length nodeset) graph)
                (valid-graph (nodes-length nodeset) graph nodeset)
                (invariant-escs2 n marks graph)
                (<= n (nodes-length nodeset)))
           (invariant-escs2 n (update-marksi node 2 marks) graph))
  :hints (("Goal" :in-theory (disable depi update-marksi update-depi))
          ("Subgoal *1/5" :use (:instance update-marksi-2-preserves-A-dests-E-2neighbor
                               (n (1- n))
                               (dests (esci (1- n) marks))))))
;; step 1 preserves invariant-escs2
(defthm step1-preserves-invariant-escs2
  (let* ((marks-after (st-escapable-inv (list node) -1 graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  (not (equal (marksi node marks) 2))
                  (not (equal (marksi node marks) 3))
                  (invariant-escs2 (nodes-length nodeset) marks graph))
             (invariant-escs2 (nodes-length nodeset) marks-after graph)))
  :otf-flg t
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :expand (st-escapable-inv (list node) -1 graph marks nodeset)
                  :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi ))))
(defthm find-2node-update-esci
  (equal (find-2node nodes (update-esci i x marks))
         (find-2node nodes marks)))
(defthm A-dests-E-2neighbor-update-esci
  (equal (A-dests-E-2neighbor node dests (update-esci i x marks) graph)
         (A-dests-E-2neighbor node dests marks graph))
  :hints (("Goal" :in-theory (disable update-esci update-marksi))))
(defthm find-2node-in-neighbors
  (implies (and (filled-graphp (nodes-length nodeset) graph)
                (valid-graph (nodes-length nodeset) graph nodeset)
                (natp node)
                (< node (nodes-length nodeset))
                (natp neighbor)
                (equal (marksi neighbor marks) 2)
                (subsetp neighbors->destsi (neighbors->destsi node graph))
                (member-equal dest (dests-of-edge node neighbor graph nodeset))
                (member-equal neighbor (keys neighbors->destsi)))
           (find-2node (st-filter-neighbors-for-dest neighbors->destsi dest) marks))
  :hints (("Goal" :in-theory (disable marksi esci update-marksi update-esci neighborsi neighbors->destsi A-natp-keys-neighbors->destsi))
          ("Subgoal *1/6" :use ((:instance assoc-key-yeilds-field
                                 (field (car neighbors->destsi))
                                 (key neighbor)
                                 (alist (neighbors->destsi node graph)))
                                (:instance nodups-keys-neighbors->destsi
                                 (n (nodes-length nodeset)))))
          ("Subgoal *1/4" :use ((:instance A-natp-keys-neighbors->destsi
                                 (n (nodes-length nodeset)))
                                (:instance natp-key
                                 (alist (neighbors->destsi node graph))
                                 (field (car neighbors->destsi)))))))
(defthm 2marked-neighbor-implies-A-dests-E-2neighbor
  (implies (and (filled-graphp (nodes-length nodeset) graph)
                (valid-graph (nodes-length nodeset) graph nodeset)
                (natp node)
                (< node (nodes-length nodeset))
                (natp neighbor)
                (member-equal neighbor (neighborsi node graph))
                (equal (marksi neighbor marks) 2)
                (subsetp dests (dests-of-edge node neighbor graph nodeset)))
           (A-dests-E-2neighbor node dests marks graph))
  :hints (("Goal" :in-theory (disable marksi esci update-marksi update-esci neighborsi neighbors->destsi))
          ("Subgoal *1/4" :use ((:instance find-2node-in-neighbors
                                 (neighbors->destsi (neighbors->destsi node graph))
                                 (dest (car dests)))
                                (:instance rewrite-member-keys
                                 (key neighbor)
                                 (keys (neighborsi node graph))
                                 (alist (neighbors->destsi node graph)))))))
(defthm A-dests-E-2neighbor-holds-for-all-dests-leading-to-2neighbors
  (implies (and (filled-graphp (nodes-length nodeset) graph)
                (valid-graph (nodes-length nodeset) graph nodeset)
                (subsetp nodes (st-filter-2marked-nodes neighbors marks))
                (subsetp nodes (neighborsi node graph))
                (A-natp nodes)
                (natp node)
                (< node (nodes-length nodeset)))
           (A-dests-E-2neighbor node (A-dests-of node nodes graph nodeset) marks graph))
  :hints (("Goal" :in-theory (disable marksi dests-of-edge neighborsi))
          ("Subgoal *1/5" :use ((:instance 2marked-neighbor-implies-A-dests-E-2neighbor
                                 (neighbor (car nodes))
                                 (dests (dests-of-edge node (car nodes) graph nodeset)))))))
(defthm temp24.0
  (implies (A-natp x)
           (A-natp (setminus x y))))
(defthm append-escs-leading-to-2neighbors-preserve-invariant-escs2-setminus
  (implies (and (filled-graphp (nodes-length nodeset) graph)
                (valid-graph (nodes-length nodeset) graph nodeset)
                (natp node)
                (<= n (nodes-length nodeset))
                (invariant-escs2 n marks graph))
           (invariant-escs2 n (append-to-esc node (A-dests-of node (st-filter-2marked-nodes (setminus (neighborsi node graph) x) marks) graph nodeset) marks) graph))
  :hints (("Goal" :in-theory (disable update-esci marksi neighborsi esci))
          ("Subgoal *1/5" :use ((:instance esci-update-esci-diff
                                 (i (1- n))
                                 (j node)
                                 (x (append (A-dests-of node (st-filter-2marked-nodes (setminus (neighborsi node graph) x) marks) graph nodeset) (esci node marks))))
                                (:instance A-dests-E-2neighbor-holds-for-all-dests-leading-to-2neighbors
                                 (node (1- n))
                                 (nodes (st-filter-2marked-nodes (setminus (neighborsi (1- n) graph) x) marks))
                                 (neighbors (setminus (neighborsi (1- n) graph) x)))
                                (:instance A-natp-st-filter-2marked-nodes
                                 (nodes (setminus (neighborsi (1- n) graph) x)))
                                (:instance A-valid-nodes-neighbors
                                 (n (nodes-length nodeset))
                                 (i (1- n)))))))
(defthm append-escs-leading-to-2neighbors-preserve-invariant-escs2
  (implies (and (filled-graphp (nodes-length nodeset) graph)
                (valid-graph (nodes-length nodeset) graph nodeset)
                (natp node)
                (<= n (nodes-length nodeset))
                (invariant-escs2 n marks graph))
           (invariant-escs2 n (append-to-esc node (A-dests-of node (st-filter-2marked-nodes (neighborsi node graph) marks) graph nodeset) marks) graph))
  :hints (("Goal" :in-theory (disable update-esci marksi neighborsi esci))
          ("Subgoal *1/5" :use ((:instance esci-update-esci-diff
                                 (i (1- n))
                                 (j node)
                                 (x (append (A-dests-of node (st-filter-2marked-nodes (neighborsi node graph) marks) graph nodeset) (esci node marks))))
                                (:instance A-dests-E-2neighbor-holds-for-all-dests-leading-to-2neighbors
                                 (node (1- n))
                                 (nodes (st-filter-2marked-nodes (neighborsi (1- n) graph) marks))
                                 (neighbors (neighborsi (1- n) graph)))
                                (:instance A-natp-st-filter-2marked-nodes
                                 (nodes (neighborsi (1- n) graph)))
                                (:instance A-valid-nodes-neighbors
                                 (n (nodes-length nodeset))
                                 (i (1- n)))))))
;; step 2 preserves invariant-escs2
(defthm temp19.0
  (equal (update-marksi i x (update-marksi i y marks))
         (update-marksi i x marks)))
(defthm step2-preserves-invariant-escs2
  (let* ((marks-after (process-escs-eff nodes stack marks graph nodeset)))
    (implies (and (filled-graphp (nodes-length nodeset) graph)
                  (valid-graph (nodes-length nodeset) graph nodeset)
                  (<= n (nodes-length nodeset))
                  (invariant-escs2 (nodes-length nodeset) marks graph))
             (invariant-escs2 (nodes-length nodeset) marks-after graph)))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :induct (process-escs-eff nodes stack marks graph nodeset)
                  :in-theory (disable marksi update-marksi neighborsi update-esci neighbors->destsi esci append-to-esc depi))
          ("Subgoal *1/8.4" :use (:instance update-marksi-2-preserves-invariant-escs2
                                  (node (car nodes))
                                  (n (nodes-length nodeset))
                                  (marks (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (neighborsi (car nodes) graph) marks) graph nodeset)
                                                        marks))))
          ("Subgoal *1/4.3" :use (:instance update-marksi-2-preserves-invariant-escs2
                                  (node (car nodes))
                                  (n (nodes-length nodeset))
                                  (marks (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (setminus (neighborsi (car nodes) graph) (cdr (assoc (car nodes) stack))) marks) graph nodeset)
                                                        marks))))
          ("Subgoal *1/3.4" :use (:instance update-marksi-2-preserves-invariant-escs2
                                  (node (car nodes))
                                  (n (nodes-length nodeset))
                                  (marks (append-to-esc (car nodes) (A-dests-of (car nodes) (st-filter-2marked-nodes (neighborsi (car nodes) graph) marks) graph nodeset)
                                                        marks))))))
;; the algorithm preserves invariant-escs2
(defthm algo-preserves-invariant-escs2
  (let* ((marks-after (st-A-nodes-escapable-inv n graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  (invariant-escs2 (nodes-length nodeset) marks graph))
             (invariant-escs2 (nodes-length nodeset) marks-after graph)))
  :hints (("Subgoal *1/2" :use (:instance step1-preserves-invariant-escs2
                                (node (1- n))))))
;; the spec of invariant-escs2
(defthm spec-of-invariant-escs2
  (implies (and (natp n)
                (natp i)
                (< i n)
                (invariant-escs2 n marks graph))
           (A-dests-E-2neighbor i (esci i marks) marks graph)))
;; invariant-escs2 holds initially
(defthm A-clear-implies-invariant-escs2
  (implies (A-clear n marks)
           (invariant-escs2 n marks graph)))
;; END invariant-escs2


;; BEGIN invariant-comp
(defthm append-to-esc-preserves-invariant-comp
  (implies (invariant-comp n marks graph nodeset)
           (invariant-comp n (append-to-esc i x marks) graph nodeset))
  :hints (("Goal" :in-theory (disable esci update-esci marksi append-to-esc))))
(defthm update-marksi-2-preserves-invariant-comp
  (implies (and (invariant-comp n marks graph nodeset)
                (natp i)
                (equal (marksi i marks) 3))
           (invariant-comp n (update-marksi i 2 marks) graph nodeset))
    :hints (("Goal" :in-theory (disable esci update-esci marksi append-to-esc marksi update-marksi))))


(defthm subsetp-depi-after-step1
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (natp node))
             (subsetp (depi node marks) (depi node marks-after))))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset)
                  :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi))))
(defthm member-valid-nodes->nodesi=1
  (implies (and (A-valid-nodes nodes nodeset)
                (member-equal node nodes))
           (equal (nodesi node nodeset) 1)))
(defthm depi-append-to-dep-update-marksi
  (equal (depi i (append-to-dep j x (update-marksi k y marks)))
         (depi i (append-to-dep j x marks)))
  :otf-flg t)
(defthm depi-append-to-esc-update-marksi
  (equal (depi i (append-to-esc j x (update-marksi k y marks)))
         (depi i (append-to-esc j x marks))))

(defthm subsetp-esci-after-step1
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (natp node))
             (subsetp (esci node marks) (esci node marks-after))))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset)
                  :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi subsetp-append-to-esc))))
(defthm step1-puts-dest-to-neighbor-in-esc-or-dep
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (A-valid-nodes (st-all-nodes nodeset) nodeset)
                  (natp prev)
                  (< prev (nodes-length nodeset))
                  (A-valid-nodes nodes nodeset)
                  (subsetp nodes (neighborsi prev graph))
                  (member-equal dest (A-dests-of prev nodes graph nodeset)))
             (or (member-equal dest (depi prev marks-after))
                 (member-equal dest (esci prev marks-after)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset)
                  :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi subsetp-depi-after-step1 subsetp-esci-after-step1))
          ("Subgoal *1/7" :use ((:instance subsetp-esci-after-step1
                                    (node prev)
                                    (nodes (cdr nodes))
                                    (marks (update-marksi (car nodes) 2 (append-to-esc prev (dests-of-edge prev (car nodes) graph nodeset)
                                            (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))
                                (:instance subsetp-depi-after-step1
                                   (node prev)
                                   (nodes (cdr nodes))
                                   (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 3
                                         (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))
                                (:instance subsetp-depi-after-step1
                                   (node prev)
                                   (nodes (cdr nodes))
                                   (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 4
                                         (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))))
          ("Subgoal *1/5" :use (:instance subsetp-esci-after-step1
                                  (node prev)
                                  (nodes (cdr nodes))
                                  (marks (update-marksi (car nodes) 2 (append-to-esc prev (dests-of-edge prev (car nodes) graph nodeset) marks)))))
          ("Subgoal *1/4" :use (:instance subsetp-depi-after-step1
                                (node prev)
                                (nodes (cdr nodes))
                                (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) marks))))
          ("Subgoal *1/3" :use (:instance subsetp-depi-after-step1
                                (node prev)
                                (nodes (cdr nodes))
                                (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) marks))))))
(defthm step1-puts-all-dests-in-dep-or-esc
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (A-valid-nodes (st-all-nodes nodeset) nodeset)
                  (natp prev)
                  (< prev (nodes-length nodeset))
                  (A-valid-nodes nodes nodeset)
                  (subsetp nodes (neighborsi prev graph))
                  (subsetp dests (A-dests-of prev nodes graph nodeset)))
             (subsetp dests (append (depi prev marks-after) (esci prev marks-after)))))
  :hints (("Goal" :induct (subsetp dests (append (depi prev (st-escapable-inv nodes prev  graph marks nodeset))
                                                 (esci prev (st-escapable-inv nodes prev  graph marks nodeset))))
                  :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi st-escapable-inv))
          ("Subgoal *1/3" :use (:instance step1-puts-dest-to-neighbor-in-esc-or-dep
                                (dest (car dests))))))

(defthm step1-does-not-alter-deps-3marked-nodes
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (equal (marksi node marks) 3)
                  (natp node)
                  ;;Invariant:
                  (or (equal prev -1)
                      (and (natp prev)
                           (equal (marksi prev marks) 1))))
             (equal (depi node marks-after) (depi node marks))))
  :hints (("Goal" :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi)
                  :do-not '(eliminate-destructors generalize)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset))))
(defthm step1-does-not-alter-deps-4marked-nodes
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (equal (marksi node marks) 4)
                  (natp node)
                  ;;Invariant:
                  (or (equal prev -1)
                      (and (natp prev)
                           (equal (marksi prev marks) 1))))
             (equal (depi node marks-after) (depi node marks))))
  :hints (("Goal" :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi)
                  :do-not '(eliminate-destructors generalize)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset))))
(defthm step1-does-not-alter-deps-2marked-nodes
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (equal (marksi node marks) 2)
                  (natp node)
                  ;;Invariant:
                  (or (equal prev -1)
                      (and (natp prev)
                           (equal (marksi prev marks) 1))))
             (equal (depi node marks-after) (depi node marks))))
  :hints (("Goal" :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi)
                  :do-not '(eliminate-destructors generalize)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset))))
(defthm step1-does-not-alter-escs-3marked-nodes
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (equal (marksi node marks) 3)
                  (natp node)
                  ;;Invariant:
                  (or (equal prev -1)
                      (and (natp prev)
                           (equal (marksi prev marks) 1))))
             (equal (esci node marks-after) (esci node marks))))
  :hints (("Goal" :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi)
                  :do-not '(eliminate-destructors generalize)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset))))
(defthm step1-does-not-alter-escs-4marked-nodes
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (equal (marksi node marks) 4)
                  (natp node)
                  ;;Invariant:
                  (or (equal prev -1)
                      (and (natp prev)
                           (equal (marksi prev marks) 1))))
             (equal (esci node marks-after) (esci node marks))))
  :hints (("Goal" :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi)
                  :do-not '(eliminate-destructors generalize)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset))))
(defthm step1-does-not-alter-escs-2marked-nodes
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (equal (marksi node marks) 2)
                  (natp node)
                  ;;Invariant:
                  (or (equal prev -1)
                      (and (natp prev)
                           (equal (marksi prev marks) 1))))
             (equal (esci node marks-after) (esci node marks))))
  :hints (("Goal" :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi nodesi)
                  :do-not '(eliminate-destructors generalize)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset))))


(defthm step1-puts-all-neighbors-3marked-node-in-deps-or-esc
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (A-valid-nodes (st-all-nodes nodeset) nodeset)
                  (natp prev)
                  (< prev (nodes-length nodeset))
                  (A-valid-nodes nodes nodeset)
                  (subsetp nodes (neighborsi prev graph))
                  (natp node)
                  (not (equal (marksi node marks) 3))
                  (equal (marksi node marks-after) 3)
                  ;;Invariant:
                  (equal (marksi prev marks) 1))
             (subsetp (A-dests-of node (neighborsi node graph) graph nodeset)
                      (append (depi node marks-after) (esci node marks-after)))))
  :hints (("Goal" :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi step1-puts-all-dests-in-dep-or-esc)
                  :do-not '(eliminate-destructors generalize)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset))
          ("Subgoal *1/7" :use ((:instance step1-puts-all-dests-in-dep-or-esc
                                 (dests (A-dests-of (car nodes) (neighborsi (car nodes) graph) graph nodeset))
                                 (nodes (neighborsi (car nodes) graph))
                                 (prev (car nodes))
                                 (marks (update-marksi (car nodes) 1 marks)))))
          ("Subgoal *1/7.47" :use ((:instance step1-does-not-alter-deps-3marked-nodes
                                  (nodes (cdr nodes))
                                  (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 3
                                                                                                                           (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))
                                 (:instance step1-does-not-alter-escs-3marked-nodes
                                  (nodes (cdr nodes))
                                  (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 3
                                                                                                                          (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))))
         ("Subgoal *1/7.32" :use ((:instance step1-does-not-alter-deps-3marked-nodes
                                  (nodes (cdr nodes))
                                  (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 3
                                                                                                                           (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))
                                 (:instance step1-does-not-alter-escs-3marked-nodes
                                  (nodes (cdr nodes))
                                  (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 3
                                                                                                                          (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))))
         ("Subgoal *1/7.22" :use ((:instance step1-does-not-alter-deps-3marked-nodes
                                  (nodes (cdr nodes))
                                  (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 3
                                                                                                                           (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))
                                 (:instance step1-does-not-alter-escs-3marked-nodes
                                  (nodes (cdr nodes))
                                  (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 3
                                                                                                                          (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))))
         ("Subgoal *1/7.12" :use ((:instance step1-does-not-alter-deps-3marked-nodes
                                  (nodes (cdr nodes))
                                  (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 4
                                                                                                                           (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))
                                 (:instance step1-does-not-alter-escs-3marked-nodes
                                  (nodes (cdr nodes))
                                  (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 4
                                                                                                                          (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))))
         ("Subgoal *1/7.2" :use ((:instance step1-does-not-alter-deps-3marked-nodes
                                  (nodes (cdr nodes))
                                  (marks (update-marksi (car nodes) 2 (append-to-esc prev (dests-of-edge prev (car nodes) graph nodeset)
                                                                                     (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))
                                 (:instance step1-does-not-alter-escs-3marked-nodes
                                  (nodes (cdr nodes))
                                  (marks (update-marksi (car nodes) 2 (append-to-esc prev (dests-of-edge prev (car nodes) graph nodeset)
                                                                                     (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))))))
(defthm step1-puts-all-neighbors-4marked-node-in-deps-or-esc
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (A-valid-nodes (st-all-nodes nodeset) nodeset)
                  (natp prev)
                  (< prev (nodes-length nodeset))
                  (A-valid-nodes nodes nodeset)
                  (subsetp nodes (neighborsi prev graph))
                  (natp node)
                  (not (equal (marksi node marks) 4))
                  (equal (marksi node marks-after) 4)
                  ;;Invariant:
                  (equal (marksi prev marks) 1))
             (subsetp (A-dests-of node (neighborsi node graph) graph nodeset)
                      (append (depi node marks-after) (esci node marks-after)))))
  :hints (("Goal" :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi  step1-puts-all-dests-in-dep-or-esc)
                  :do-not '(eliminate-destructors generalize)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset))
          ("Subgoal *1/7" :use ((:instance step1-puts-all-dests-in-dep-or-esc
                                 (dests (A-dests-of (car nodes) (neighborsi (car nodes) graph) graph nodeset))
                                 (nodes (neighborsi (car nodes) graph))
                                 (prev (car nodes))
                                 (marks (update-marksi (car nodes) 1 marks)))))
          ("Subgoal *1/7.42" :use ((:instance step1-does-not-alter-deps-4marked-nodes
                                    (nodes (cdr nodes))
                                    (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 3
                                                                                                                             (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))
                                   (:instance step1-does-not-alter-escs-4marked-nodes
                                    (nodes (cdr nodes))
                                    (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 3
                                                                                                                             (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))))
          ("Subgoal *1/7.35" :use ((:instance step1-does-not-alter-deps-4marked-nodes
                                    (nodes (cdr nodes))
                                    (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 4
                                                                                                                             (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))
                                   (:instance step1-does-not-alter-escs-4marked-nodes
                                    (nodes (cdr nodes))
                                    (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 4
                                                                                                                             (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))))
          ("Subgoal *1/7.20" :use ((:instance step1-does-not-alter-deps-4marked-nodes
                                    (nodes (cdr nodes))
                                    (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 4
                                                                                                                             (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))
                                   (:instance step1-does-not-alter-escs-4marked-nodes
                                    (nodes (cdr nodes))
                                    (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 4
                                                                                                                             (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))))
          ("Subgoal *1/7.12" :use ((:instance step1-does-not-alter-deps-4marked-nodes
                                    (nodes (cdr nodes))
                                    (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 4
                                                                                                                             (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))
                                   (:instance step1-does-not-alter-escs-4marked-nodes
                                    (nodes (cdr nodes))
                                    (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 4
                                                                                                                             (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))))
          ("Subgoal *1/7.2" :use ((:instance step1-does-not-alter-deps-4marked-nodes
                                   (nodes (cdr nodes))
                                   (marks (update-marksi (car nodes) 2 (append-to-esc prev (dests-of-edge prev (car nodes) graph nodeset)
                                                                                      (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))
                                  (:instance step1-does-not-alter-escs-4marked-nodes
                                   (nodes (cdr nodes))
                                   (marks (update-marksi (car nodes) 2 (append-to-esc prev (dests-of-edge prev (car nodes) graph nodeset)
                                                                                      (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))))))
(defthm step1-puts-all-neighbors-2marked-node-in-deps-or-esc
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (A-valid-nodes (st-all-nodes nodeset) nodeset)
                  (natp prev)
                  (< prev (nodes-length nodeset))
                  (A-valid-nodes nodes nodeset)
                  (subsetp nodes (neighborsi prev graph))
                  (natp node)
                  (not (equal (marksi node marks) 2))
                  (equal (marksi node marks-after) 2)
                  ;;Invariant:
                  (equal (marksi prev marks) 1))
             (subsetp (A-dests-of node (neighborsi node graph) graph nodeset)
                      (append (depi node marks-after) (esci node marks-after)))))
  :hints (("Goal" :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi)
                  :do-not '(eliminate-destructors generalize)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset))
          ("Subgoal *1/7" :use (:instance step1-puts-all-dests-in-dep-or-esc
                                   (dests (A-dests-of (car nodes) (neighborsi (car nodes) graph) graph nodeset))
                                   (nodes (neighborsi (car nodes) graph))
                                   (prev (car nodes))
                                   (marks (update-marksi (car nodes) 1 marks))))
          ("Subgoal *1/7.44" :use ((:instance step1-does-not-alter-deps-2marked-nodes
                                  (nodes (cdr nodes))
                                  (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 3
                                                                                                                           (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))
                                 (:instance step1-does-not-alter-escs-2marked-nodes
                                  (nodes (cdr nodes))
                                  (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 3
                                                                                                                          (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))))
          ("Subgoal *1/7.34" :use ((:instance step1-does-not-alter-deps-2marked-nodes
                                    (nodes (cdr nodes))
                                    (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 4
                                                                                                                             (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))
                                   (:instance step1-does-not-alter-escs-2marked-nodes
                                    (nodes (cdr nodes))
                                  (marks (append-to-dep prev (dests-of-edge prev (car nodes) graph nodeset) (update-marksi (car nodes) 4
                                                                                                                          (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))))

          ("Subgoal *1/7.27" :use ((:instance step1-does-not-alter-deps-2marked-nodes
                                   (nodes (cdr nodes))
                                   (marks (update-marksi (car nodes) 2 (append-to-esc prev (dests-of-edge prev (car nodes) graph nodeset)
                                                                                      (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))
                                  (:instance step1-does-not-alter-escs-2marked-nodes
                                   (nodes (cdr nodes))
                                   (marks (update-marksi (car nodes) 2 (append-to-esc prev (dests-of-edge prev (car nodes) graph nodeset)
                                                                                      (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))))
          ("Subgoal *1/7.11" :use ((:instance step1-does-not-alter-deps-2marked-nodes
                                   (nodes (cdr nodes))
                                   (marks (update-marksi (car nodes) 2 (append-to-esc prev (dests-of-edge prev (car nodes) graph nodeset)
                                                                                      (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))
                                  (:instance step1-does-not-alter-escs-2marked-nodes
                                   (nodes (cdr nodes))
                                   (marks (update-marksi (car nodes) 2 (append-to-esc prev (dests-of-edge prev (car nodes) graph nodeset)
                                                                                      (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))))
          ("Subgoal *1/7.2" :use ((:instance step1-does-not-alter-deps-2marked-nodes
                                   (nodes (cdr nodes))
                                   (marks (update-marksi (car nodes) 2 (append-to-esc prev (dests-of-edge prev (car nodes) graph nodeset)
                                                                                      (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))
                                  (:instance step1-does-not-alter-escs-2marked-nodes
                                   (nodes (cdr nodes))
                                   (marks (update-marksi (car nodes) 2 (append-to-esc prev (dests-of-edge prev (car nodes) graph nodeset)
                                                                                      (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset)))))))))


(defthm temp1.16
  (equal (marksi i (update-marksi j x marks))
         (cond ((and (natp i) (natp j) (equal i j))
                x)
               ((and (zp i) (zp j))
                x)
               (t
                (marksi i marks)))))
(defthm temp2.0
  (implies (invariant-comp n marks graph nodeset)
           (invariant-comp n (update-marksi i 1 marks) graph nodeset))
  :hints (("Goal" :in-theory (disable depi esci marksi update-marksi neighborsi))))
(defthm spec-of-invariant-comp2
  (implies (and (invariant-comp n marks graph nodeset)
                (equal (marksi i marks) 2)
                (natp i)
                (natp n)
                (< i n))
           (subsetp (A-dests-of i (neighborsi i graph) graph nodeset) (append (depi i marks) (esci i marks)))))
(defthm temp1.15
  (implies (invariant-comp n marks graph nodeset)
           (invariant-comp n (append-to-dep i x marks) graph nodeset))
  :hints (("Goal" :in-theory (disable depi update-depi marksi append-to-dep))))
(defthm update-marksi-2-preserves-invariant-comp-sink
  (implies (and (invariant-comp n marks graph nodeset)
                (natp i)
                (not (neighborsi i graph)))
           (invariant-comp n (update-marksi i 2 marks) graph nodeset)))
(defthm update-marksi-2-preserves-invariant-comp-already-2
  (implies (equal (marksi i marks) 2)
           (equal (invariant-comp n (update-marksi i 2 marks) graph nodeset)
                  (invariant-comp n marks graph nodeset))))
(defthmd temp1.19.1
  (subsetp (append y z)
           (append y (cons a z))))
(defthm temp1.19
  (subsetp (append x y) (append x w y))
  :hints (("Subgoal *1/2" :use (:instance temp1.19.1
                                (y x)
                                (a (car w))
                                (z (append (cdr w) y))))))
(defthm temp1.18
  (implies (and (natp j)
                (invariant-comp n (update-marksi i 2 marks) graph nodeset))
           (invariant-comp n (update-marksi i 2 (append-to-esc j x marks)) graph nodeset))
  :hints (("Goal" :in-theory (disable update-marksi depi esci marksi update-esci neighborsi))))
(defthm update-marksi-2-preserves-invariant-comp-visited
  (implies (and (invariant-comp n marks graph nodeset)
                (natp i)
                (subsetp (A-dests-of i (neighborsi i graph) graph nodeset)
                         (append (depi i marks) (esci i marks))))
           (invariant-comp n (update-marksi i 2 marks) graph nodeset))
  :hints (("Goal" :in-theory (disable update-marksi depi esci neighborsi marksi))))
(defthm update-marksi-3-preserves-invariant-comp-visited
  (implies (and (invariant-comp n marks graph nodeset)
                (natp i)
                (subsetp (A-dests-of i (neighborsi i graph) graph nodeset)
                         (append (depi i marks) (esci i marks))))
           (invariant-comp n (update-marksi i 3 marks) graph nodeset))
  :hints (("Goal" :in-theory (disable update-marksi depi esci neighborsi marksi))))
(defthm update-marksi-4-preserves-invariant-comp-visited
  (implies (and (invariant-comp n marks graph nodeset)
                (natp i)
                (subsetp (A-dests-of i (neighborsi i graph) graph nodeset)
                         (append (depi i marks) (esci i marks))))
           (invariant-comp n (update-marksi i 4 marks) graph nodeset))
  :hints (("Goal" :in-theory (disable update-marksi depi esci neighborsi marksi))))
;; step1 preserves invariant-comp (inductive)
(defthm step1-preserves-invariant-comp-inductive
  (let* ((marks-after (st-escapable-inv nodes prev graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  (A-valid-nodes nodes nodeset)
                  (natp prev)
                  (invariant-comp (nodes-length nodeset) marks graph nodeset))
             (invariant-comp (nodes-length nodeset) marks-after graph nodeset)))
  :hints (("Goal" :induct (st-escapable-inv nodes prev graph marks nodeset)
                  :do-not '(eliminate-destructors generalize)
                  :in-theory (disable esci depi marksi neighborsi update-marksi marksi-update-marksi
                                      append-to-esc append-to-dep))))
;; step 1 preserves invariant-comp
(defthm step1-preserves-invariant-comp
  (let* ((marks-after (st-escapable-inv (list node) -1 graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (natp node)
                  (< node (nodes-length nodeset))
                  (equal (nodesi node nodeset) 1)
                  (invariant-comp n marks graph nodeset))
             (invariant-comp n marks-after graph nodeset)))
  :hints (("Goal" :induct (invariant-comp n marks graph nodeset)
                  :do-not '(eliminate-destructors generalize)
                  :in-theory (disable esci depi marksi neighborsi update-marksi marksi-update-marksi temp1.16))
          ("Subgoal *1/4" :expand (st-escapable-inv (list node) -1 graph marks nodeset)
                          :use ((:instance marksi-update-marksi
                                 (i (1- n))
                                 (j node)
                                 (x 2))
                                (:instance marksi-update-marksi
                                 (i (1- n))
                                 (j node)
                                 (x 4)
                                 (marks (st-escapable-inv (neighborsi node graph) node  graph (update-marksi node 1 marks) nodeset)))
                                (:instance marksi-update-marksi
                                 (i (1- n))
                                 (j node)
                                 (x 3)
                                 (marks (st-escapable-inv (neighborsi node graph) node  graph (update-marksi node 1 marks) nodeset)))
                                (:instance marksi-update-marksi
                                 (i (1- n))
                                 (j node)
                                 (x 2)
                                 (marks (st-escapable-inv (neighborsi node graph) node  graph (update-marksi node 1 marks) nodeset)))
                                (:instance marksi-update-marksi
                                 (i (1- n))
                                 (j node)
                                 (x 1))))))

;; the algorithm preserves invariant-comp
(defthm algo-preserves-invariant-comp
  (let* ((marks-after (st-A-nodes-escapable-inv n graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (invariant-comp (nodes-length nodeset) marks graph nodeset))
             (invariant-comp (nodes-length nodeset) marks-after graph nodeset)))
  :hints (("Subgoal *1/2" :use (:instance step1-preserves-invariant-comp
                                (node (1- n))
                                (n (nodes-length nodeset))))))
;; the spec of invariant-comp
(defthm spec-of-invariant-comp4
  (implies (and (invariant-comp n marks graph nodeset)
                (equal (marksi i marks) 4)
                (natp i)
                (natp n)
                (< i n))
           (subsetp (A-dests-of i (neighborsi i graph) graph nodeset) (append (depi i marks) (esci i marks)))))
(defthm spec-of-invariant-comp
  (implies (and (invariant-comp n marks graph nodeset)
                (equal (marksi i marks) 3)
                (natp i)
                (natp n)
                (< i n))
           (subsetp (A-dests-of i (neighborsi i graph) graph nodeset) (append (depi i marks) (esci i marks)))))
;; invariant-holds initially
(defthm A-clear-implies-invariant-comp
  (implies (A-clear n marks)
           (invariant-comp n marks graph nodeset)))#|ACL2s-ToDo-Line|#

;; END invariant-comp
