#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#


(in-package "ACL2")
(include-book "invariants2")


;; BEGIN invariant-2marks
(defun invariant-2marks (n st-marks st-graph)
  (declare (xargs :stobjs (st-marks st-graph)
                  :verify-guards nil))
  (cond ((zp n)
         t)
        ((and (equal (marksi (1- n) st-marks) 2)
              (consp (neighborsi (1- n) st-graph)))
         (and (subsetp (depi (1- n) st-marks) (esci (1- n) st-marks))
              (invariant-2marks (1- n) st-marks st-graph)))
        (t
         (invariant-2marks (1- n) st-marks st-graph))))
(defthm update-marksi-1-preserves-invariant-2marks
  (implies (and (invariant-2marks n marks graph)
                (natp x))
           (invariant-2marks n (update-marksi x 1 marks) graph)))
(defthm update-marksi-4-preserves-invariant-2marks
  (implies (and (invariant-2marks n marks graph)
                (natp x))
           (invariant-2marks n (update-marksi x 4 marks) graph)))
(defthm update-marksi-3-preserves-invariant-2marks
  (implies (and (invariant-2marks n marks graph)
                (natp x))
           (invariant-2marks n (update-marksi x 3 marks) graph)))
(defthm append-to-esc-preserves-invariant-2marks
  (implies (and (natp i)
                (invariant-2marks n marks graph))
           (invariant-2marks n (append-to-esc i x marks) graph)))
(defthm append-to-dep-preserves-invariant-2marks
  (implies (equal (marksi node marks) 1)
           (equal (invariant-2marks n (append-to-dep node x marks) graph)
                  (invariant-2marks n marks graph))))
(defthm update-marksi-2-preserves-invariant-2marks
  (implies (and (natp node)
                (subsetp (depi node marks) (esci node marks))
                (invariant-2marks n marks graph))
           (invariant-2marks n (update-marksi node 2 marks) graph))
  :hints (("Goal" :in-theory (disable update-marksi esci depi marksi))))
(defthm update-marksi-2-preserves-invariant-2marks-no-parents
  (implies (and (natp node)
                (not (neighborsi node graph))
                (invariant-2marks n marks graph))
           (invariant-2marks n (update-marksi node 2 marks) graph))
  :hints (("Goal" :in-theory (disable update-marksi esci depi marksi))))
(defthm update-marksi-3-preserves-invariant-2marks-already-2
  (implies (equal (marksi node marks) 2)
           (equal (invariant-2marks n (update-marksi node 2 marks) graph)
                  (invariant-2marks n marks graph))))
 (defthm update-marksi-2-append-to-esc-preserves-invariant-2marks
   (implies (and (natp i)
                 (natp j)
                 (subsetp (depi i marks) (esci i marks))
                 (invariant-2marks n marks graph))
            (invariant-2marks n (update-marksi i 2 (append-to-esc j x marks)) graph))
   :hints (("Goal" :in-theory (disable update-marksi esci update-esci depi neighborsi marksi))))
 ;; step 1 preserves invariant-2marks (inductive)
(defthm step1-preserves-invariant-2marks-inductive
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  (A-valid-nodes nodes nodeset)
                  (equal (marksi prev marks) 1)
                  (natp prev)
                  (invariant-2marks n marks graph))
             (invariant-2marks n marks-after graph)))
  :hints (("Goal" :induct (st-escapable-inv nodes prev  graph marks nodeset)
                  :do-not '(eliminate-destructors generalize)
                  :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi E-d-path-to-013-marked-node))))
;; step 1 preserves invariant-2marks
(defthm step2-preserves-invariant-2marks
  (let* ((marks-after (st-escapable-inv (list node) -1  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  (invariant-2marks n marks graph))
             (invariant-2marks n marks-after graph)))
  :hints (("Goal" :expand (st-escapable-inv (list node) -1  graph marks nodeset)
                  :do-not '(eliminate-destructors generalize)
                  :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi))))
;; the algorithm preserves invariant-2marks
(defthm algo-preserves-invariant-2marks
  (let* ((marks-after (st-A-nodes-escapable-inv n graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  (invariant-2marks (nodes-length nodeset) marks graph))
             (invariant-2marks (nodes-length nodeset) marks-after graph))))
;; the spec of invariant-3marks
(defthm spec-of-invariant-2marks
  (implies (and (invariant-2marks n marks graph)
                (equal (marksi i marks) 2)
                (consp (neighborsi i graph))
                (natp i)
                (natp n)
                (< i n))
           (subsetp (depi i marks) (esci i marks))))
;; invariant-2marks holds initially
(defthm A-clear-implies-invariant-2marks
  (implies (A-clear n marks)
           (invariant-2marks n marks graph)))
;; END invariant-2marks




;; BEGIN invariant-4marks
(defun invariant-4marks (n st-marks)
  (declare (xargs :stobjs (st-marks)
                  :verify-guards nil))
  (cond ((zp n)
         t)
        ((equal (marksi (1- n) st-marks) 4)
         (and (subsetp (depi (1- n) st-marks) (esci (1- n) st-marks))
              (invariant-4marks (1- n) st-marks)))
        (t
         (invariant-4marks (1- n) st-marks))))
(defthm temp1.1
  (implies (invariant-4marks n marks)
           (invariant-4marks n (update-marksi x 1 marks))))
(defthm temp1.2
  (implies (invariant-4marks n marks)
           (invariant-4marks n (update-marksi x 2 marks))))
(defthm temp1.3
  (implies (invariant-4marks n marks)
           (invariant-4marks n (update-marksi x 3 marks))))
(defthm temp1.4
  (implies (and (natp i)
                (invariant-4marks n marks))
           (invariant-4marks n (append-to-esc i x marks))))
(defthm temp1.7
  (implies (equal (marksi node marks) 1)
           (equal (invariant-4marks n (append-to-dep node x marks))
                  (invariant-4marks n marks))))
(defthm temp1.8
  (implies (and (natp node)
                (subsetp (depi node marks) (esci node marks))
                (invariant-4marks n marks))
           (invariant-4marks n (update-marksi node 4 marks)))
  :hints (("Goal" :in-theory (disable update-marksi esci depi marksi))))
;; step 1 preserves invariant-4marks (inductive)
(defthm temp1.0
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  (A-valid-nodes nodes nodeset)
                  (equal (marksi prev marks) 1)
                  (natp prev)
                  (invariant-4marks n marks))
             (invariant-4marks n marks-after)))
  :hints (("Goal" :induct (st-escapable-inv nodes prev  graph marks nodeset)
                  :do-not '(eliminate-destructors generalize)
                  :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi))))
;; step 1 preserves invariant-4marks
(defthm temp1.00
  (let* ((marks-after (st-escapable-inv (list node) -1  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  (invariant-4marks n marks))
             (invariant-4marks n marks-after)))
  :hints (("Goal" :expand (st-escapable-inv (list node) -1  graph marks nodeset)
                  :do-not '(eliminate-destructors generalize)
                  :in-theory (disable esci depi update-marksi nodes-length neighborsi dests-of-edge neighbors->destsi append-to-esc append-to-dep marksi))))
;; the algorithm preserves invariant-4marks
(defthm algo-preserves-invariant-4marks
  (let* ((marks-after (st-A-nodes-escapable-inv n graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (filled-graphp (nodes-length nodeset) graph)
                  (invariant-4marks (nodes-length nodeset) marks))
             (invariant-4marks (nodes-length nodeset) marks-after))))
;; the spec of invariant-4marks
(defthm spec-of-invariant-4marks
  (implies (and (invariant-4marks n marks)
                (equal (marksi i marks) 4)
                (natp i)
                (natp n)
                (< i n))
           (subsetp (depi i marks) (esci i marks))))
;; invariant-4marks holds initially
(defthm A-clear-implies-invariant-4marks
  (implies (A-clear n marks)
           (invariant-4marks n marks)))
;; END invariant-4marks




;; BEGIN invariant-legal
(defun invariant-legal (n st-marks)
  (declare (xargs :stobjs st-marks
                  :verify-guards nil))
  (if (zp n)
    t
    (and (legal-mark (marksi (1- n) st-marks))
         (invariant-legal (1- n) st-marks))))

(defthm temp8.0
  (implies (and (invariant-legal n marks)
                (or (equal x 1) (equal x 2) (equal x 3) (equal x 4)))
           (invariant-legal n (update-marksi i x marks)))
  :hints (("Goal" :in-theory (disable marksi update-marksi))))
(defthm temp8.1
  (equal (invariant-legal n (append-to-dep i x marks))
         (invariant-legal n marks)))
(defthm temp8.2
  (equal (invariant-legal n (append-to-esc i x marks))
         (invariant-legal n marks)))
(defthm temp8.3
  (implies (and (invariant-legal n marks)
                (natp i)
                (natp n)
                (< i n))
           (legal-mark (marksi i marks))))
;; step 1 preserves invariant-legal
(defthm step1-preserves-invariant-legal
  (let* ((marks-after (st-escapable-inv nodes prev  graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (A-valid-nodes nodes nodeset)
                  ;;Invariant
                  (invariant-legal (nodes-length nodeset) marks))
             (invariant-legal (nodes-length nodeset) marks-after)))
  :hints (("Goal" :in-theory (disable legal-mark append-to-dep append-to-esc depi esci marksi neighborsi update-marksi))))
;; the algorithm preserves invariant-legal
(defthm algo-preserves-invariant-legal
  (let* ((marks-after (st-A-nodes-escapable-inv n graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (invariant-legal (nodes-length nodeset) marks))
             (invariant-legal (nodes-length nodeset) marks-after)))
  :hints (("Subgoal *1/2" :use (:instance step1-preserves-invariant-legal
                                (nodes (list (1- n)))
                                (prev -1)))))
;; invariant-legal holds initially
(defthm A-clear-implies-invariant-legal
  (implies (A-clear n marks)
           (invariant-legal n marks)))#|ACL2s-ToDo-Line|#

;; END invariant-legal


