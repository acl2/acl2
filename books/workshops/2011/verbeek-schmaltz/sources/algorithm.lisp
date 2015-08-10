#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#


(in-package "ACL2")

(include-book "definitions")

;;-------------------
;; The algorithm
;;-------------------




;; First we define function E-d-path-to-013-marked-node, which returns t iff there exists a d-path to a node that is marked 0, 1 or 3.
(defthm diff-size-cons-<
  (implies (and (member-equal a y)
                (not (member-equal a x)))
           (< (diff-size (cons a x) y)
              (diff-size x y)))
  :rule-classes :linear)
(defun st-filter-neighbors-for-dest (neighbors->dests dest)
  (cond ((endp neighbors->dests)
         nil)
        ((member-equal dest (cdar neighbors->dests))
         (cons (caar neighbors->dests) (st-filter-neighbors-for-dest (cdr neighbors->dests) dest)))
        (t
         (st-filter-neighbors-for-dest (cdr neighbors->dests) dest))))
(defun st-find-next-d-step (from to stack dest st-graph st-nodeset)
  (declare (xargs :measure  (list (diff-size stack (show-nodeset (nodes-length st-nodeset) st-nodeset)) (len from))
                  :stobjs (st-graph st-nodeset)
                  :well-founded-relation l<
                  :verify-guards nil))
  (cond
   ((endp from)
    'failure)
   ((not (st-valid-node (car from) st-nodeset))
    'failure)
   ((equal (car from) to)
    (rev (cons to stack)))
   ((member-equal (car from) stack)
    (st-find-next-d-step (cdr from) to stack dest st-graph st-nodeset))
   (t (let ((path (st-find-next-d-step (st-filter-neighbors-for-dest (neighbors->destsi (car from) st-graph) dest) to (cons (car from) stack) dest st-graph st-nodeset)))
        (if (equal path 'failure)
          (st-find-next-d-step (cdr from) to stack dest st-graph st-nodeset)
          path)))))
(defun st-find-d-path (a b dest st-graph st-nodeset)
  (declare (xargs :stobjs (st-graph st-nodeset)
                  :verify-guards nil))
  (cond ((equal a b) (list a))
        (t
         (st-find-next-d-step (st-filter-neighbors-for-dest (neighbors->destsi a st-graph) dest) b (list a) dest st-graph st-nodeset))))#|ACL2s-ToDo-Line|#

(defun E-013-marked-E-d-path (n from dest st-marks st-graph st-nodeset)
  (declare (xargs :stobjs (st-marks st-graph st-nodeset)
                  :verify-guards nil))
  (cond ((zp n)
         nil)
        ((and (equal (nodesi (1- n) st-nodeset) 1)
              (or (equal (marksi (1- n) st-marks) 0)
                  (equal (marksi (1- n) st-marks) 1)
                  (and (equal (marksi (1- n) st-marks) 3)
                       (member-equal dest (depi (1- n) st-marks))
                       (not (member-equal dest (esci (1- n) st-marks)))))
              (not (equal (st-find-d-path from (1- n) dest st-graph st-nodeset) 'failure)))
         t)
        (t
         (E-013-marked-E-d-path (1- n) from dest st-marks st-graph st-nodeset))))
(defun E-d-E-d-path-to-013-marked-node (n from st-marks st-graph st-nodeset)
  (declare (xargs :stobjs (st-marks st-graph st-nodeset)
                  :verify-guards nil))
  (cond ((zp n)
         nil)
        ((and (equal (nodesi (1- n) st-nodeset) 1)
              (E-013-marked-E-d-path (nodes-length st-nodeset) from (1- n) st-marks st-graph st-nodeset))
         t)
        (t
         (E-d-E-d-path-to-013-marked-node (1- n) from st-marks st-graph st-nodeset))))
(defun E-d-path-to-013-marked-node (from st-marks st-graph st-nodeset)
  (declare (xargs :stobjs (st-marks st-graph st-nodeset)
                  :verify-guards nil))
  (E-d-E-d-path-to-013-marked-node (nodes-length st-nodeset) from st-marks st-graph st-nodeset))





;; STEP 1 OF THE ALGORITHM
;;
;; Two versions are here: one ugly version, on which we prove things, and one executable version. The executable version has the cleanest code to look at.
(defun st-escapable-inv (nodes prev st-graph st-marks st-nodeset)
  (declare (xargs :measure (list (len (st-filter-unmarked123-nodes (show-nodeset (nodes-length st-nodeset) st-nodeset) st-marks)) (len nodes))
                  :well-founded-relation l<
                  :stobjs (st-graph st-marks st-nodeset)
                  :hints (("Goal" :in-theory (disable nodes-length update-esci neighbors->destsi update-marksi marksi esci marksi depi update-depi neighborsi)))
                  :verify-guards nil
                  :guard (and (true-listp nodes)
                              (A-valid-nodes nodes st-nodeset)
                              (A-valid-nodes (show-nodeset (nodes-length st-nodeset) st-nodeset) st-nodeset)
                              (or (equal prev -1)
                                  (and (natp prev)
                                       (< prev (nodes-length st-nodeset))))
                              (valid-graph (nodes-length st-nodeset) st-graph st-nodeset)
                              (A-true-listp-escs (nodes-length st-nodeset) st-marks)
                              (A-true-listp-deps (nodes-length st-nodeset) st-marks)
                              (A-natp-escs (nodes-length st-nodeset) st-marks)
                              (A-natp-deps (nodes-length st-nodeset) st-marks))))
  (mbe
   :logic
   (cond
    ((or (not (A-natp nodes))
         (not (A-valid-nodes nodes st-nodeset))
         (not (or (equal prev -1)
                  (and (natp prev)
                       (< prev (nodes-length st-nodeset)))))
         (not (A-valid-nodes (show-nodeset (nodes-length st-nodeset) st-nodeset) st-nodeset)))
     st-marks)
    ((endp nodes)
     st-marks)
    (t
     (let ((node (car nodes))
           (dests (dests-of-edge prev (car nodes) st-graph st-nodeset))
           (assertion (len (st-filter-unmarked123-nodes (show-nodeset (nodes-length st-nodeset) st-nodeset) st-marks))))
       (cond ((or (equal (marksi node st-marks) 3)
                  (equal (marksi node st-marks) 4))
              (let ((st-marks (if (not (equal prev -1))
                                (append-to-dep prev dests st-marks)
                                st-marks)))
                (st-escapable-inv (cdr nodes) prev st-graph st-marks st-nodeset)))
             ((equal (marksi node st-marks) 1)
              (let ((st-marks (if (not (equal prev -1))
                                (append-to-dep prev dests st-marks)
                                st-marks)))
                (st-escapable-inv (cdr nodes) prev st-graph st-marks st-nodeset)))
             ((or (equal (marksi node st-marks) 2)
                  (endp (neighborsi node st-graph)))
              (let ((st-marks (if (equal prev -1)
                                st-marks
                                (append-to-esc prev dests st-marks))))
                (let ((st-marks (update-marksi node 2 st-marks)))
                  (st-escapable-inv (cdr nodes) prev st-graph st-marks st-nodeset))))

             (t
              (seq st-marks
                   (update-marksi node 1 st-marks)
                   (st-escapable-inv (neighborsi node st-graph) node st-graph st-marks st-nodeset)
                   (if (not (equal prev -1))
                     (cond ((not (subsetp (depi node st-marks) (esci node st-marks)))
                            (seq st-marks
                                 (update-marksi node 3 st-marks)
                                 (append-to-dep prev dests st-marks)))
                           ((E-d-path-to-013-marked-node node st-marks st-graph st-nodeset)
                            (seq st-marks
                                 (update-marksi node 4 st-marks)
                                 (append-to-dep prev dests st-marks)))
                           (t
                            (seq st-marks
                                 (append-to-esc prev dests st-marks)
                                 (update-marksi node 2 st-marks))))
                     (cond ((not (subsetp (depi node st-marks) (esci node st-marks)))
                            (update-marksi node 3 st-marks))
                           ((E-d-path-to-013-marked-node node st-marks st-graph st-nodeset)
                            (update-marksi node 4 st-marks))
                           (t
                            (update-marksi node 2 st-marks))))
                   (if (<= assertion (len (st-filter-unmarked123-nodes (show-nodeset (nodes-length st-nodeset) st-nodeset) st-marks)))
                     st-marks
                     (st-escapable-inv (cdr nodes) prev st-graph st-marks st-nodeset))))))))
   :exec
   (cond
    ((endp nodes)
     st-marks)
    (t
     (let (;; The port currently under investigation
           (node (car nodes))
           ;; The destination leading from the previous port to the current one
           (dests (dests-of-edge prev (car nodes) st-graph st-nodeset)))
       (cond (;; If the node has been visited/marked as deadlock-sensitive/marked as leading to a deadlock-sensitive node:
              ;; Add the dests leading to this node to dep (backwards propagation)
              (or (equal (marksi node st-marks) 1)
                  (equal (marksi node st-marks) 3)
                  (equal (marksi node st-marks) 4))
              (seq st-marks
                   (if (not (equal prev -1))
                     (append-to-dep prev dests st-marks)
                     st-marks)
                   (st-escapable-inv (cdr nodes) prev st-graph st-marks st-nodeset)))
             (;; If the node is a sink/marked as deadlock-immune:
              ;; Add the dests leading to this node to esc (backwards propagation)
              (or (equal (marksi node st-marks) 2)
                  (endp (neighborsi node st-graph)))
              (seq st-marks
                   (if (equal prev -1)
                     st-marks
                     (append-to-esc prev dests st-marks))
                   (update-marksi node 2 st-marks)
                   (st-escapable-inv (cdr nodes) prev st-graph st-marks st-nodeset)))
             (t
              ;; Otherwise:
              ;; Mark the port as 1 (visited). Explore the neighbors and propagate the obtained information back.
              (seq st-marks
                   (update-marksi node 1 st-marks)
                   (st-escapable-inv (neighborsi node st-graph) node st-graph st-marks st-nodeset)
                   (cond ((not (subsetp (depi node st-marks) (esci node st-marks)))
                          ;; If the node is now deadlock-sensitive:
                          (seq st-marks
                               (update-marksi node 3 st-marks)
                               (if (not (equal prev -1)) (append-to-dep prev dests st-marks) st-marks)))
                         ((E-d-path-to-013-marked-node node st-marks st-graph st-nodeset)
                          ;; If there exists a path to a deadlock-sensitive node:
                          (seq st-marks
                               (update-marksi node 4 st-marks)
                               (append-to-dep prev dests st-marks)))
                         (t
                          ;; Otherwise:
                          (seq st-marks
                               (if (not (equal prev -1))
                                 (append-to-esc prev dests st-marks) st-marks)
                               (update-marksi node 2 st-marks))))
                   (st-escapable-inv (cdr nodes) prev st-graph st-marks st-nodeset)))))))))




;; We now define function upwards-4marked-reach which returns all 4marked nodes from which a node is reachable., i.e., all indirect 4marked parents.
(defun st-find-next-step (from to stack st-graph st-nodeset)
  (declare (xargs :measure  (list (diff-size stack (show-nodeset (nodes-length st-nodeset) st-nodeset)) (len from))
                  :stobjs (st-graph st-nodeset)
                  :well-founded-relation l<
                  :verify-guards nil))
  (cond
   ((endp from)
    'failure)
   ((not (st-valid-node (car from) st-nodeset))
    'failure)
   ((equal (car from) to)
    (rev (cons to stack)))
   ((member-equal (car from) stack)
    (st-find-next-step (cdr from) to stack st-graph st-nodeset))
   (t (let ((path (st-find-next-step (neighborsi (car from) st-graph) to (cons (car from) stack) st-graph st-nodeset)))
        (if (equal path 'failure)
          (st-find-next-step (cdr from) to stack st-graph st-nodeset)
          path)))))
(defun st-find-path (a b st-graph st-nodeset)
  (declare (xargs :stobjs (st-graph st-nodeset)
                  :verify-guards nil))
  (cond ((equal a b) (list a))
        (t
         (st-find-next-step (neighborsi a st-graph) b (list a) st-graph st-nodeset))))
(defun upwards-4marked-reach (n node st-marks st-graph st-nodeset)
  (declare (xargs :stobjs (st-marks st-graph st-nodeset)
                  :verify-guards nil))
  (cond ((zp n)
         nil)
        ((and (st-find-path (1- n) node st-graph st-nodeset)
              (equal (nodesi (1- n) st-nodeset) 1)
              (equal (marksi (1- n) st-marks) 4)
              (not (equal (1- n) node)))
         (cons (1- n) (upwards-4marked-reach (1- n) node st-marks st-graph st-nodeset)))
        (t
         (upwards-4marked-reach (1- n) node st-marks st-graph st-nodeset))))



;; We prove a termination measure
(defthm diff-size-append1
  (<= (diff-size (append x y) z)
      (diff-size x z))
  :rule-classes :linear)
(defthm diff-size-nil
  (equal (diff-size nil x) (len x)))
(defthm diff-size-subsetp
  (implies (subsetp x1 x2)
           (<= (diff-size x2 y)
               (diff-size x1 y)))
  :rule-classes :linear)
(defthm append-to-data-does-not-increase-diff-size
  (implies (A-consp alist)
           (<= (diff-size (cdr (assoc key1 (append-to-data key2 data alist))) y)
               (diff-size (cdr (assoc key1 alist)) y)))
  :rule-classes :linear)
(defthm append-to-data-does-not-increase-num-of-edges-not-in-stack
  (implies (A-consp stack)
           (<= (num-of-edges-not-in-stack n (append-to-data node neighbors stack) graph)
               (num-of-edges-not-in-stack n stack graph)))
  :rule-classes :linear)
(defthm car-append
  (equal (car (append x y))
         (if (consp x)
           (car x)
           (car y))))
(defthm diff-size-cons
  (implies (and (subsetp x y)
                (consp x))
           (< (diff-size (cons a x) y) (len y)))
  :rule-classes :linear
  :hints (("Subgoal *1/4" :use (:instance diff-size-subsetp
                                (x1 (cons a (cdr x)))
                                (x2 (cons a x))))))
(defthm diff-size-endp
  (implies (endp x)
           (equal (diff-size x y) (len y))))
(defthm diff-size-is-maximally-len
  (<= (diff-size x y) (len y))
  :rule-classes :linear)
(defthm diff-size-is-less-than-len
  (implies (and (consp x)
                (subsetp x y))
           (< (diff-size x y)
              (len y)))
  :hints (("Goal" :induct (diff-size x y))))
(defthm diff-size-cons-not-member
  (implies (not (member-equal a y))
           (equal (diff-size (cons a x) y)
                  (diff-size x y))))
(defthm not-subsetp-cdr-->member-car
  (implies (and (subsetp x y)
                (not (subsetp x (cdr y))))
           (member-equal (car y) x)))
(defthm diff-size-append-disjoint
  (implies (and (consp y)
                (subsetp y z)
                (not-in x y))
           (< (diff-size (append x y) z)
              (diff-size x z)))
  :hints (("Goal" :induct (diff-size x z))))
(defthm rewrite-not-in
  (equal (not-in y x) (not-in x y)))
(defthm append-to-data-decreases-diff-size
  (implies (and key
                (consp data)
                (subsetp data y)
                (not-in data (cdr (assoc key alist))))
           (< (diff-size (cdr (assoc key (append-to-data key data alist))) y)
              (diff-size (cdr (assoc key alist)) y)))
  :hints (("Subgoal *1/2" :use (:instance diff-size-append-disjoint
                                (x (car alist))
                                (y data)
                                (z y)))))
(defthm append-to-data-decreases-num-of-edges-not-in-stack
  (implies (and (A-consp stack)
                (consp neighbors)
                (subsetp neighbors (neighborsi node graph))
                (not-in neighbors (cdr (assoc node stack)))
                (< node n)
                (natp node)
                (natp n))
           (< (num-of-edges-not-in-stack n (append-to-data node neighbors stack) graph)
              (num-of-edges-not-in-stack n stack graph))))


(in-theory (disable not-subsetp-cdr-->member-car rewrite-not-in))




;; STEP 2 OF THE ALGORITHM
;; Post-processing

;; The goal of this step is to ensure that for all 3marked nodes, all 2marked neighbors are included in escs. The difficulty is that validating a port, i.e. adding its 2 neighbors to escs,
;; can cause the port to get marked 2, thus invalidating all parents of the port.
;; Parameter nodes contains all ports that can possibly be invalidated. Initially, this parameter is just all 3 marked ports. Once a port gets marked 2, all its 3parents are added.

;; Possible efficiency improvements:
;; 1.) Instead of using `append' use an efficient data-structure (i.e. a sorted queue structure)
;; 2.) Instead of adding destinations to all 2 marked neighbors, only those that have not been added already: let step 1 keep track of those destinations that are uncertain. This saves filtering neighbors.
;; 3.) Store parent ports in st-graph, instead of filtering them
;; 4.) Remove second cond-clause using mbe
;; 5.) Verify guards
;; 6.) Initialy, give it only real unvalidated ports.
(defun process-escs-eff (nodes stack st-marks st-graph st-nodeset)
  (declare (xargs :stobjs (st-marks st-graph st-nodeset)
                  :measure (list (num-of-edges-not-in-stack (nodes-length st-nodeset) stack st-graph)
                                 (len (filter-4marked-nodes (nodes-length st-nodeset) st-marks st-nodeset))
                                 (len nodes))
                  :well-founded-relation l<
                  :hints (("Goal" :in-theory (disable neighborsi marksi update-marksi esci depi update-esci append-to-esc)))
                  :verify-guards nil
                  :guard (and (true-listp nodes)
                              (A-valid-nodes nodes st-nodeset)
                              (A-true-listp-escs (nodes-length st-nodeset) st-marks)
                              (A-true-listp-deps (nodes-length st-nodeset) st-marks)
                              (A-natp-deps (nodes-length st-nodeset) st-marks)
                              (valid-graph (nodes-length st-nodeset) st-graph st-nodeset))))
  (cond ((endp nodes)
         st-marks)
        ((or (not (natp (car nodes)))
             (not (< (car nodes) (nodes-length st-nodeset)))
             (not (equal (nodesi (car nodes) st-nodeset) 1))
             (not (A-consp stack)))
         (process-escs-eff (cdr nodes) stack st-marks st-graph st-nodeset))
        ((equal (marksi (car nodes) st-marks) 3)
         (let ((2neighbors (st-filter-2marked-nodes (setminus (neighborsi (car nodes) st-graph) (cdr (assoc (car nodes) stack))) st-marks)))
           (if (consp 2neighbors)
             ;; Validate the port:
             (seq st-marks
                 (append-to-esc (car nodes) (A-dests-of (car nodes) 2neighbors st-graph st-nodeset) st-marks)
                 (if (not (unresolved (car nodes) st-marks))
                   ;; If the deps are now included in the escs:
                   (seq st-marks
                        (update-marksi (car nodes) 4 st-marks)
                        (if (E-d-path-to-013-marked-node (car nodes) st-marks st-graph st-nodeset)
                          ;; Add all parents to ports under investigation
                          (process-escs-eff (append (upwards-4marked-reach (nodes-length st-nodeset) (car nodes) st-marks st-graph st-nodeset)
                                                    (remove-equal (car nodes) nodes))
                                            (append-to-data (car nodes) 2neighbors stack)
                                            st-marks st-graph st-nodeset)
                          ;; Change marking to 2 and add all parents to ports under investigation
                          (seq st-marks
                               (update-marksi (car nodes) 2 st-marks)
                               (process-escs-eff (append (st-filter-3parents (car nodes) (nodes-length st-nodeset) st-marks st-graph st-nodeset)
                                                         (upwards-4marked-reach (nodes-length st-nodeset) (car nodes) st-marks st-graph st-nodeset)
                                                         (remove-equal (car nodes) nodes))
                                                 (append-to-data (car nodes) 2neighbors stack)
                                                 st-marks st-graph st-nodeset))))
                   ;; The marking remains 3 but with new escs, thus add all todo.
                   (process-escs-eff (append (upwards-4marked-reach (nodes-length st-nodeset) (car nodes) st-marks st-graph st-nodeset)
                                             (remove-equal (car nodes) nodes))
                                     (append-to-data (car nodes) 2neighbors stack)
                                     st-marks st-graph st-nodeset)))
             ;; The marking remains 3 and no escs are added, so just continue.
             (process-escs-eff (remove-equal (car nodes) nodes) stack st-marks st-graph st-nodeset))))
        ((equal (marksi (car nodes) st-marks) 4)
         (if (E-d-path-to-013-marked-node (car nodes) st-marks st-graph st-nodeset)
           (process-escs-eff (remove-equal (car nodes) nodes) stack st-marks st-graph st-nodeset)
           (let ((2neighbors (st-filter-2marked-nodes (neighborsi (car nodes) st-graph) st-marks)))
             ;; Change marking to 2 and add all parents to ports under investigation
             (seq st-marks
                  (append-to-esc (car nodes) (A-dests-of (car nodes) 2neighbors st-graph st-nodeset) st-marks)
                  (update-marksi (car nodes) 2 st-marks)
                  (process-escs-eff (append (st-filter-3parents (car nodes) (nodes-length st-nodeset) st-marks st-graph st-nodeset)
                                            (remove-equal (car nodes) nodes))
                                    (append-to-data (car nodes) 2neighbors stack)
                                    st-marks st-graph st-nodeset)))))
        (t
         ;; Otherwise: just skip the port
         (process-escs-eff (cdr nodes) stack st-marks st-graph st-nodeset))))



;; MAIN
(defun st-A-nodes-escapable-inv (n st-graph st-marks st-nodeset)
  (declare (xargs :stobjs (st-graph st-marks st-nodeset)
                  :verify-guards nil
                  :guard (and (natp n)
                              (<= n (nodes-length st-nodeset))
                              (A-valid-nodes (show-nodeset (nodes-length st-nodeset) st-nodeset) st-nodeset)
                              (valid-graph (nodes-length st-nodeset) st-graph st-nodeset)
                              (A-true-listp-escs (nodes-length st-nodeset) st-marks)
                              (A-true-listp-deps (nodes-length st-nodeset) st-marks)
                              (A-natp-escs (nodes-length st-nodeset) st-marks)
                              (A-natp-deps (nodes-length st-nodeset) st-marks))))
  (cond ((zp n)
         st-marks)
        ;; If the port is unmarked, perform step 1
        ((and (equal (marksi (1- n) st-marks) 0)
              (equal (nodesi (1- n) st-nodeset) 1))
         (seq st-marks
              (st-escapable-inv (list (1- n)) -1 st-graph st-marks st-nodeset)
                (st-A-nodes-escapable-inv (1- n) st-graph st-marks st-nodeset)))
        (t
         ;; Otherwise: the port is marked and thus continue
         (st-A-nodes-escapable-inv (1- n) st-graph st-marks st-nodeset))))


(defun algorithm (st-graph st-marks st-nodeset)
  (declare (xargs :stobjs (st-graph st-marks st-nodeset)
                  :verify-guards nil
                  :guard (and (valid-graph (nodes-length st-nodeset) st-graph st-nodeset)
                              (A-true-listp-escs (nodes-length st-nodeset) st-marks)
                              (A-true-listp-deps (nodes-length st-nodeset) st-marks)
                              (A-natp-escs (nodes-length st-nodeset) st-marks)
                              (A-natp-deps (nodes-length st-nodeset) st-marks))))
  (seq st-marks
       (st-A-nodes-escapable-inv (nodes-length st-nodeset) st-graph st-marks st-nodeset)
       (process-escs-eff (append (filter-3marked-nodes (nodes-length st-nodeset) st-marks st-nodeset)
                                 (filter-4marked-nodes (nodes-length st-nodeset) st-marks st-nodeset))
                         nil
                         st-marks st-graph st-nodeset)
       (mv (if (consp (append (filter-3marked-nodes (nodes-length st-nodeset) st-marks st-nodeset) (filter-4marked-nodes (nodes-length st-nodeset) st-marks st-nodeset))) nil t)
           st-marks)))


;;----------------------------
;; Verification of the guards
;;----------------------------
;; Not many interesting theorems here, mostly proving that everything is truelistp, natp, etc...
;; Interesting is theorem algo-does-not-increase-number-of-unmarked-nodes, which states that the assertion -- that the number of unmarked nodes does not increase -- always holds.
;; This enables us to prove the mbe construct: the executable algorithm without this assertion is equal to the algorithm with the
;; assertion and thus the executable version terminates as well.

(defthm esci-update-marksi
  (equal (esci node (update-marksi node2 x marks))
         (esci node marks)))
(defthm marksi-append-to-esc
  (equal (marksi node (append-to-esc node2 dests marks))
         (marksi node marks)))
(defthm subsetp-append-->and-subsetp
  (equal (subsetp (append x y) z)
         (and (subsetp x z)
              (subsetp y z))))
(defthm subsetp-cons
  (implies (subsetp x y)
           (subsetp x (cons e y))))
(defthm subsetp-x-x
  (subsetp x x))
(defthm member-subsetp
  (implies (and (subsetp x y)
                (member-equal a x))
           (member-equal a y)))
(defthm subsetp-append-r-r
  (subsetp x (append y x)))
(defthm subsetp-append-to-esc
  (subsetp (esci node marks)
           (esci node (append-to-esc node2 x marks))))
(defthm esci-append-to-dep
  (equal (esci n (append-to-dep node x marks))
         (esci n marks)))
(defthm show-marks-append-to-dep
  (equal (show-marks n (append-to-dep node x marks))
         (show-marks n marks)))
(defthm show-marks-append-to-esc
  (equal (show-marks n (append-to-esc node x marks))
         (show-marks n marks)))
(defthm marksi-append-to-dep
  (equal (marksi node (append-to-dep node2 x marks))
         (marksi node marks)))
(defthm esci-update-depi
  (equal (esci i (update-depi j x marks))
         (esci i marks)))
(defthm depi-append-to-dep
  (equal (depi i (append-to-dep i x marks))
         (append x (depi i marks))))
(defthm esci-append-to-esc
  (equal (esci i (append-to-esc i x marks))
         (append x (esci i marks))))
(defthm depi-update-marksi
  (equal (depi i (update-marksi j x marks))
         (depi i marks)))
(defthm depi-append-to-esc
  (equal (depi i (append-to-esc j x marks))
         (depi i marks)))
(defthm depi-append-to-dep-diff
  (implies (and (not (equal node1 node2))
                (natp node1)
                (natp node2))
           (equal (depi node1 (append-to-dep node2 x marks))
                  (depi node1 marks))))
(defthm A-natp-append
  (iff (A-natp (append x y))
       (and (A-natp x)
            (A-natp y))))
(defthm A-valid-nodes-cdr-assoc
  (implies (A-valid-nodes-values alist nodeset)
           (A-valid-nodes (cdr (assoc x alist)) nodeset)))
(defthm A-valid-nodes-values-neighbors->destsi
  (implies (and (valid-graph n graph nodeset)
                (< node n)
                (natp n)
                (natp node))
           (A-valid-nodes-values (neighbors->destsi node graph) nodeset)))

(defthm A-valid-nodes-neighbors
  (implies (and (valid-graph n graph nodeset)
                (< i n)
                (natp i)
                (natp n))
           (A-valid-nodes (neighborsi i graph) nodeset)))

(defthm A-natp-depi-algo
  (implies (and (A-natp (depi node marks))
                (natp node)
                (natp prev)
                (< node (nodes-length nodeset))
                (A-valid-nodes nodes nodeset)
                (valid-graph (nodes-length nodeset) graph nodeset))
           (A-natp (depi node (st-escapable-inv nodes prev graph marks nodeset))))
  :hints (("Goal" :in-theory (disable update-esci neighbors->destsi update-marksi marksi esci marksi depi update-depi neighborsi append-to-dep append-to-esc A-valid-nodes-cdr-assoc)
                  :induct (st-escapable-inv nodes prev graph marks nodeset)
                  :do-not '(eliminate-destructors generalize))
          ("Subgoal *1/7" :use ((:instance depi-append-to-dep-diff
                                 (node1 node)
                                 (node2 prev)
                                 (x (dests-of-edge prev (car nodes) graph nodeset))
                                 (marks (update-marksi (car nodes) 3 (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset))))
                                (:instance depi-append-to-dep-diff
                                 (node1 node)
                                 (node2 prev)
                                 (x (dests-of-edge prev (car nodes) graph nodeset))
                                 (marks (update-marksi (car nodes) 4 (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset))))
                                (:instance A-valid-nodes-cdr-assoc
                                 (x (car nodes))
                                 (alist (neighbors->destsi node graph)))))
          ("Subgoal *1/6" :use ((:instance depi-append-to-dep-diff
                                 (node1 node)
                                 (node2 prev)
                                 (x (dests-of-edge prev (car nodes) graph nodeset))
                                 (marks (update-marksi (car nodes) 3 (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset))))
                                (:instance depi-append-to-dep-diff
                                 (node1 node)
                                 (node2 prev)
                                 (x (dests-of-edge prev (car nodes) graph nodeset))
                                 (marks (update-marksi (car nodes) 4 (st-escapable-inv (neighborsi (car nodes) graph) (car nodes) graph (update-marksi (car nodes) 1 marks) nodeset))))
                                (:instance A-valid-nodes-cdr-assoc
                                 (x (car nodes))
                                 (alist (neighbors->destsi node graph)))))
          ("Subgoal *1/4" :use ((:instance depi-append-to-dep-diff
                                 (node1 node)
                                 (node2 prev)
                                 (x (dests-of-edge prev (car nodes) graph nodeset)))
                                (:instance A-valid-nodes-cdr-assoc
                                 (x (car nodes))
                                 (alist (neighbors->destsi node graph)))))
          ("Subgoal *1/3" :use ((:instance depi-append-to-dep-diff
                                 (node1 node)
                                 (node2 prev)
                                 (x (dests-of-edge prev (car nodes) graph nodeset)))
                                (:instance A-valid-nodes-cdr-assoc
                                 (x (car nodes))
                                 (alist (neighbors->destsi node graph)))))))

(defthm A-natp-deps-algo
  (implies (and (A-valid-nodes nodes nodeset)
                (valid-graph (nodes-length nodeset) graph nodeset)
                (A-natp-deps n marks)
                (natp n)
                (< n (nodes-length nodeset))
                (natp prev))
           (A-natp-deps n (st-escapable-inv nodes prev graph marks nodeset)))
  :hints (("Subgoal *1/6" :use (:instance A-natp-depi-algo
                                (node (1- n))))))

(defthm A-natp-neighbors
  (implies (and (valid-graph n  graph nodeset)
                (natp n)
                (natp node)
                (< node n))
           (A-natp (neighborsi node graph))))

(defthm st-filter-unmarked123-nodes-update-marksi-append-to-esc
  (equal (st-filter-unmarked123-nodes nodes (update-marksi i x (append-to-esc j y marks)))
         (st-filter-unmarked123-nodes nodes (update-marksi i x marks))))
(defthm st-filter-unmarked123-nodes-update-marksi-append-to-dep
  (equal (st-filter-unmarked123-nodes nodes (update-marksi i x (append-to-dep j y marks)))
         (st-filter-unmarked123-nodes nodes (update-marksi i x marks))))
(defthm st-filter-unmarked123-nodes-update-marksi-update-esci
  (equal (st-filter-unmarked123-nodes nodes (update-marksi i x (update-esci j y marks)))
         (st-filter-unmarked123-nodes nodes (update-marksi i x marks))))
(defthm st-filter-unmarked123-nodes-update-marksi-update-depi
  (equal (st-filter-unmarked123-nodes nodes (update-marksi i x (update-depi j y marks)))
         (st-filter-unmarked123-nodes nodes (update-marksi i x marks))))


(defthm algo-preserves-2marking
  (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                (A-valid-nodes nodes nodeset)
                (natp node)
                (equal (marksi node marks) 2))
           (equal (marksi node (st-escapable-inv nodes prev graph marks nodeset)) 2))
  :hints (("Goal" :in-theory (disable esci depi update-marksi neighborsi update-depi update-esci marksi dests-of-edge update-marksi valid-graph)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset)
                  :do-not '(eliminate-destructors generalize))))
(defthm algo-preserves-3marking
  (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                (A-valid-nodes nodes nodeset)
                (natp node)
                (equal (marksi node marks) 3))
           (equal (marksi node (st-escapable-inv nodes prev  graph marks nodeset)) 3))
  :hints (("Goal" :in-theory (disable esci depi update-marksi neighborsi update-depi update-esci marksi dests-of-edge update-marksi valid-graph)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset)
                  :do-not '(eliminate-destructors generalize))))
(defthm algo-preserves-4marking
  (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                (A-valid-nodes nodes nodeset)
                (natp node)
                (equal (marksi node marks) 4))
           (equal (marksi node (st-escapable-inv nodes prev  graph marks nodeset)) 4))
  :hints (("Goal" :in-theory (disable esci depi update-marksi neighborsi update-depi update-esci marksi dests-of-edge update-marksi valid-graph)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset)
                  :do-not '(eliminate-destructors generalize))))
(defthm algo-preserves-1marking
  (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                (A-valid-nodes nodes nodeset)
                (natp node)
                (equal (marksi node marks) 1))
           (equal (marksi node (st-escapable-inv nodes prev graph marks nodeset)) 1))
  :hints (("Goal" :in-theory (disable esci depi update-marksi neighborsi update-depi update-esci marksi dests-of-edge update-marksi valid-graph)
                  :induct (st-escapable-inv nodes prev  graph marks nodeset)
                  :do-not '(eliminate-destructors generalize))))
(defthm algo-preserves-marked
  (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                (marked node marks)
                (natp node)
                (A-valid-nodes nodes nodeset))
           (marked node (st-escapable-inv nodes prev graph marks nodeset)))
  :rule-classes nil
  :otf-flg t
  :hints (("Goal" :use ((:instance algo-preserves-4marking)
                        (:instance algo-preserves-3marking)
                        (:instance algo-preserves-1marking)
                        (:instance algo-preserves-2marking)))))
(defthm algo-does-not-increase-number-of-unmarked-nodes
  (implies (and (valid-graph (nodes-length st-nodeset) graph nodeset)
                (A-valid-nodes nodes nodeset)
                (A-valid-nodes nodes1 nodeset)
                (natp prev))
           (<= (len (st-filter-unmarked123-nodes nodes1 (st-escapable-inv nodes prev  graph marks nodeset)))
               (len (st-filter-unmarked123-nodes nodes1 marks))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable update-esci neighbors->destsi update-marksi marksi esci marksi depi update-depi neighborsi
                                      append-to-dep append-to-esc)
                  :do-not '(eliminate-destructors generalize))
          ("Subgoal *1/3" :use (:instance algo-preserves-marked
                                (node (car nodes1))))))

(defthm st-filter-unmarked123-nodes-update-marksi-2
  (implies (and (natp node)
                (A-natp nodes))
           (equal (st-filter-unmarked123-nodes nodes (update-marksi node 2 marks))
                  (remove-equal node (st-filter-unmarked123-nodes nodes marks))))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :in-theory (disable esci depi update-marksi append-to-esc append-to-dep neighborsi neighbors->destsi marksi))))
(defthm st-filter-unmarked123-nodes-update-marksi-3
  (implies (and (natp node)
                (A-natp nodes))
           (equal (st-filter-unmarked123-nodes nodes (update-marksi node 3 marks))
                  (remove-equal node (st-filter-unmarked123-nodes nodes marks))))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :in-theory (disable esci depi update-marksi append-to-esc append-to-dep neighborsi neighbors->destsi marksi))))
(defthm st-filter-unmarked123-nodes-update-marksi-4
  (implies (and (natp node)
                (A-natp nodes))
           (equal (st-filter-unmarked123-nodes nodes (update-marksi node 4 marks))
                  (remove-equal node (st-filter-unmarked123-nodes nodes marks))))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :in-theory (disable esci depi update-marksi append-to-esc append-to-dep neighborsi neighbors->destsi marksi))))
(defthmd ocurrences-equal-cons
  (implies (not (equal a b))
           (equal (occurrences-equal a (cons b x))
                  (occurrences-equal a x)))
  :hints (("Goal" :in-theory (enable occurrences-equal))))
(defthm st-filter-unmarked123-nodes-has-no-marked-nodes
  (implies (marked node marks)
           (equal (occurrences-equal node (st-filter-unmarked123-nodes nodes marks)) 0))
  :hints (("Subgoal *1/2" :use (:instance ocurrences-equal-cons
                                (a node)
                                (b (car nodes))
                                (x (st-filter-unmarked123-nodes (cdr nodes) marks))))))

(defthm A-true-listp-escs-append-to-dep
  (equal (A-true-listp-escs n (append-to-dep i x marks))
         (A-true-listp-escs n marks)))
(defthm A-true-listp-deps-append-to-esc
  (equal (A-true-listp-deps n (append-to-esc i x marks))
         (A-true-listp-deps n marks)))
(defthm A-true-listp-escs-update-marksi
  (equal (A-true-listp-escs n (update-marksi i x marks))
         (A-true-listp-escs n marks)))
(defthm A-true-listp-deps-append-to-dep
  (implies (and (A-true-listp-deps n marks)
                (true-listp x))
           (A-true-listp-deps n (append-to-dep i x marks))))
(defthm A-true-listp-escs-append-to-esc
  (implies (and (A-true-listp-escs n marks)
                (true-listp x))
           (A-true-listp-escs n (append-to-esc i x marks))))
(defthm rewrite-esci-append-to-esc-unconditional
  (equal (esci node1 (append-to-esc node2 x marks))
         (cond ((and (natp node1)
                     (natp node2))
                (if (equal node1 node2)
                  (append x (esci node1 marks))
                  (esci node1 marks)))
               ((and (zp node1)
                     (zp node2))
                (append x (esci node1 marks)))
               (t
                (esci node1 marks)))))
(defthm algo-preserves-true-listp-esci
  (implies (true-listp (esci i marks))
           (true-listp (esci i (st-escapable-inv nodes prev graph marks nodeset))))
  :hints (("Goal" :in-theory (disable esci update-marksi append-to-dep append-to-esc marksi depi nodesi neighborsi))))
(defthm algo-preserves-true-listp-escs
  (implies (A-true-listp-escs n marks)
           (A-true-listp-escs n (st-escapable-inv nodes prev graph marks nodeset)))
  :hints (("Goal" :in-theory (disable esci update-marksi append-to-dep append-to-esc marksi depi))))
(defthm rewrite-depi-append-to-dep-unconditional
  (equal (depi node1 (append-to-dep node2 x marks))
         (cond ((and (natp node1)
                     (natp node2))
                (if (equal node1 node2)
                  (append x (depi node1 marks))
                  (depi node1 marks)))
               ((and (zp node1)
                     (zp node2))
                (append x (depi node1 marks)))
               (t
                (depi node1 marks)))))
(in-theory (disable depi-append-to-dep-diff))
(defthm algo-preserves-true-listp-depi
  (implies (true-listp (depi i marks))
           (true-listp (depi i (st-escapable-inv nodes prev graph marks nodeset))))
    :hints (("Goal" :in-theory (disable esci update-marksi append-to-dep append-to-esc marksi depi nodesi neighborsi))))
(defthm algo-preserves-true-listp-deps
  (implies (A-true-listp-deps n marks)
           (A-true-listp-deps n (st-escapable-inv nodes prev graph marks nodeset)))
  :hints (("Goal" :in-theory (disable depi update-marksi))))


(defthm depi-update-depi
  (equal (depi n (update-depi n x marks)) x))
(defthm esci-update-esci
  (equal (esci n (update-esci n x marks)) x))
(defthm depi-update-esci
  (equal (depi i (update-esci j x marks))
         (depi i marks)))
(defthm esci-update-depi
  (equal (esci i (update-depi j x marks))
         (esci i marks)))
(defthm depi-update-depi-diff
  (implies (and (natp i)
                (natp j))
           (equal (depi i (update-depi j x marks))
                  (if (equal i j)
                    x
                    (depi i marks)))))
(defthm A-natp-cdr-assoc
  (implies (A-valid-nodes-values alist nodeset)
           (A-natp (cdr (assoc x alist)))))
(defthm algo-preserves-A-natp-depi
  (implies (and (valid-graph n graph nodeset)
                (A-natp (depi i marks))
                (natp i)
                (natp n)
                (< i n))
           (A-natp (depi i (st-escapable-inv nodes prev graph marks nodeset))))
  :hints (("Goal" :in-theory (disable depi update-marksi append-to-esc append-to-dep neighbors->destsi neighborsi nodesi esci A-valid-nodes-values-neighbors->destsi)
                  :do-not '(eliminate-destructors generalize))
          ("Subgoal *1/12" :use (:instance A-valid-nodes-values-neighbors->destsi
                                 (node i)))
          ("Subgoal *1/10" :use (:instance A-valid-nodes-values-neighbors->destsi
                                 (node i)))
          ("Subgoal *1/5.2" :use (:instance A-valid-nodes-values-neighbors->destsi
                                    (node i)))
          ("Subgoal *1/3" :use (:instance A-valid-nodes-values-neighbors->destsi
                                  (node i)))))
(defthm algo-preserves-A-natp-deps
  (implies (and (valid-graph m graph nodeset)
                (A-natp-deps n marks)
                (natp n)
                (natp m)
                (<= n m))
           (A-natp-deps n (st-escapable-inv nodes prev graph marks nodeset)))
  :hints (("Goal" :in-theory (disable depi update-marksi))))
(defthm esci-update-depi
  (equal (esci i (update-depi j x marks))
         (esci i marks)))
(defthm esci-update-esci-diff
  (implies (and (natp i)
                (natp j))
           (equal (esci i (update-esci j x marks))
                  (if (equal i j)
                    x
                    (esci i marks)))))



(defthm A-natp-escs-update-marksi
  (equal (A-natp-escs n (update-marksi i x marks))
         (A-natp-escs n marks)))
(defthm A-natp-deps-update-marksi
  (equal (A-natp-deps n (update-marksi i x marks))
         (A-natp-deps n marks)))
(defthm A-natp-and-true-listp-->eqlable-listp
  (implies (and (A-natp x)
                (true-listp x))
           (eqlable-listp x)))
(defthm eqlable-listp-esci
  (implies (and (A-natp-escs n marks)
                (A-true-listp-escs n marks)
                (natp n)
                (natp i)
                (< i n))
           (eqlable-listp (esci i marks))))
(defthm eqlable-listp-depi
  (implies (and (A-natp-deps n marks)
                (A-true-listp-deps n marks)
                (natp n)
                (natp i)
                (< i n))
           (eqlable-listp (depi i marks))))
(defthm A-true-listp-escs-update-marksi
  (equal (A-true-listp-escs n (update-marksi i x marks))
         (A-true-listp-escs n marks)))
(defthm A-true-listp-deps-update-marksi
  (equal (A-true-listp-deps n (update-marksi i x marks))
         (A-true-listp-deps n marks)))
(defthm A-natp-deps-append-to-esc
  (equal (A-natp-deps n (append-to-esc i x marks))
         (A-natp-deps n marks)))
(defthm A-natp-escs-append-to-dep
  (equal (A-natp-escs n (append-to-dep i x marks))
         (A-natp-escs n marks)))
(defthm A-natp-escs-append-to-esc
  (implies (and (A-natp-escs n marks)
                (A-natp x))
           (A-natp-escs n (append-to-esc i x marks))))
(defthm A-natp-deps-append-to-dep
  (implies (and (A-natp-deps n marks)
                (A-natp x))
           (A-natp-deps n (append-to-dep i x marks))))
(defthm true-listp-esc
  (implies (and (A-true-listp-escs n marks)
                (natp n)
                (natp i)
                (< i n))
           (true-listp (esci i marks))))
(defthm true-listp-dep
  (implies (and (A-true-listp-deps n marks)
                (natp n)
                (natp i)
                (< i n))
           (true-listp (depi i marks))))
(defthm true-listp-neighbors
  (implies (and (valid-graph n graph nodeset)
                (< i n)
                (natp i)
                (natp n))
           (true-listp (neighborsi i graph))))
(defthm consp-neighbors<->neighbors
  (implies (and (valid-graph n graph nodeset)
                (< i n)
                (natp i)
                (natp n))
           (iff (consp (neighborsi i graph))
                (neighborsi i graph))))
(defthmd remove-double-update
  (implies (nth i x)
           (equal (update-nth i (nth i x) x) x)))
(defthmd rewrite-update-marksi
  (implies (and (natp i)
                x
                (equal (marksi i marks) x))
           (equal (update-marksi i x marks) marks))
  :hints (("Goal" :use (:instance remove-double-update
                        (x (car marks))))))




(defthm len-st-filter-unmarked-123-nodes-update-marksi-1
  (<= (len (st-filter-unmarked123-nodes nodes (update-marksi node 1 marks)))
      (len (st-filter-unmarked123-nodes nodes marks)))
  :rule-classes :linear)
(defthm st-filter-unmarked123-nodes-append-to-dep
  (equal (st-filter-unmarked123-nodes nodes (append-to-dep i x marks))
         (st-filter-unmarked123-nodes nodes marks)))
(defthm st-filter-unmarked123-nodes-append-to-esc
  (equal (st-filter-unmarked123-nodes nodes (append-to-esc i x marks))
         (st-filter-unmarked123-nodes nodes marks)))

(defthm A-<-show-nodeset-inductive
  (implies (<= n m)
           (A-<_guarded (show-nodeset n nodeset) m)))
(defthm A-<-show-nodeset
  (A-<_guarded (show-nodeset n nodeset) n))
(in-theory (disable A-<-show-nodeset-inductive))

(defthm A-true-list-escs-update-depi
  (equal (A-true-listp-escs n (update-depi i x marks))
         (A-true-listp-escs n marks)))
(defthm A-true-list-deps-update-esci
  (equal (A-true-listp-deps n (update-esci i x marks))
         (A-true-listp-deps n marks)))
(defthm A-true-list-escs-update-esci-nil
  (implies (A-true-listp-escs n marks)
           (A-true-listp-escs n (update-esci m nil marks))))
(defthm A-true-list-deps-update-depi-nil
  (implies (A-true-listp-deps n marks)
           (A-true-listp-deps n (update-depi m nil marks))))
(defthm A-natp-escs-update-depi
  (equal (A-natp-escs n (update-depi i x marks))
         (A-natp-escs n marks)))
(defthm A-natp-deps-update-esci
  (equal (A-natp-deps n (update-esci i x marks))
         (A-natp-deps n marks)))
(defthm A-natp-escs-update-esci-nil
  (implies (A-natp-escs n marks)
           (A-natp-escs n (update-esci m nil marks))))
(defthm A-natp-deps-update-depi-nil
  (implies (A-natp-deps n marks)
           (A-natp-deps n (update-depi m nil marks))))
(defthm A-valid-nodes-upwards-reach
  (implies (<= n (nodes-length nodeset))
           (A-valid-nodes (upwards-4marked-reach n stack marks graph nodeset) nodeset)))

;(defthm algo-preserves-A-natp-escs
;  (implies (and (valid-graph m graph nodeset)
;                (A-natp-escs n marks)
;                (natp n)
;                (natp m)
;                (<= n m))
;           (A-natp-escs n (st-escapable-inv nodes prev graph marks nodeset)))
;  :hints (("Goal" :in-theory (disable depi update-marksi append-to-esc append-to-dep neighbors->destsi neighborsi nodesi esci A-valid-nodes-values-neighbors->destsi)
;                  :induct (st-escapable-inv nodes prev graph marks nodeset))))





(defthm A-<-valid-nodes
  (implies (A-valid-nodes nodes nodeset)
           (A-<_guarded nodes (marks-length marks))))
(defthm eqlable-listp-append
  (implies (true-listp x)
           (equal (eqlable-listp (append x y))
                  (and (eqlable-listp x)
                       (eqlable-listp y)))))
(defthm A-valid-nodes-append
  (equal (A-valid-nodes (append x y) nodeset)
         (and (A-valid-nodes x nodeset)
              (A-valid-nodes y nodeset))))
(defthm A-valid-nodes-st-filter-3parents
  (implies (<= n (nodes-length nodeset))
           (A-valid-nodes (st-filter-3parents node n marks graph nodeset) nodeset)))
(defthm A-valid-nodes-remove-equal
  (implies (A-valid-nodes nodes nodeset)
           (A-valid-nodes (remove-equal node nodes) nodeset)))




(defthm A-natp-A-dests-of
  (implies (and (valid-graph n graph nodeset)
                (natp n)
                (natp node)
                (< node n))
           (A-natp (A-dests-of node neighbors graph nodeset)))
  :hints (("Goal" :induct (A-dests-of node neighbors graph nodeset))))
(defthm pp-preserves-A-natp-escs
  (let ((marks-after (process-escs-eff nodes stack marks graph nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (A-valid-nodes nodes nodeset)
                  (A-natp-escs (nodes-length nodeset) marks))
             (A-natp-escs (nodes-length nodeset) marks-after)))
  :hints (("Goal" :in-theory (disable depi esci append-to-esc marksi update-marksi))))
(defthm A-valid-nodes-filter-3marked-nodes
  (implies (<= n (nodes-length nodeset))
           (A-valid-nodes (filter-3marked-nodes n marks nodeset) nodeset)))
(defthm pp-preserves-A-true-listp-deps
  (let ((marks-after (process-escs-eff nodes stack marks graph nodeset)))
    (equal (A-true-listp-deps n marks-after)
           (A-true-listp-deps n marks)))
  :hints (("Goal" :in-theory (disable depi update-marksi update-esci)
                  :induct (process-escs-eff nodes stack marks graph nodeset))))
(defthm pp-preserves-A-natp-deps
  (let ((marks-after (process-escs-eff nodes stack marks graph nodeset)))
    (equal (A-natp-deps n marks-after)
           (A-natp-deps n marks)))
  :hints (("Goal" :in-theory (disable depi update-marksi update-esci)
                  :induct (process-escs-eff nodes stack marks graph nodeset))))
(defthm pp-preserves-A-true-listp-escs
  (let ((marks-after (process-escs-eff nodes stack marks graph nodeset)))
    (implies (A-true-listp-escs (nodes-length nodeset) marks)
             (A-true-listp-escs (nodes-length nodeset) marks-after)))
  :hints (("Goal" :in-theory (disable depi esci append-to-esc marksi update-marksi))))

(defthmd A-valid-nodes-show-nodeset
  (implies (<= n (nodes-length nodeset))
           (A-valid-nodes (show-nodeset n nodeset) nodeset)))


(defthm algorep-preserves-A-true-listp-escs
  (let ((marks-after (st-A-nodes-escapable-inv n graph marks nodeset)))
    (implies (A-true-listp-escs (nodes-length nodeset) marks)
             (A-true-listp-escs (nodes-length nodeset) marks-after)))
  :hints (("Goal" :in-theory (disable nodesi marksi))))
(defthm algorep-preserves-A-true-listp-deps
  (let ((marks-after (st-A-nodes-escapable-inv n graph marks nodeset)))
    (implies (A-true-listp-deps (nodes-length nodeset) marks)
             (A-true-listp-deps (nodes-length nodeset) marks-after)))
  :hints (("Goal" :in-theory (disable nodesi marksi))))
(defthm algorep-preserves-A-natp-deps
  (let ((marks-after (st-A-nodes-escapable-inv n graph marks nodeset)))
    (implies (and (valid-graph (nodes-length nodeset) graph nodeset)
                  (A-natp-deps (nodes-length nodeset) marks))
             (A-natp-deps (nodes-length nodeset) marks-after)))
  :hints (("Goal" :in-theory (disable nodesi marksi))
          ("Subgoal *1/2" :use (:instance algo-preserves-A-natp-deps
                                (n (nodes-length nodeset))
                                (m (nodes-length nodeset))
                                (nodes (list (1- n)))
                                (prev -1)))))

;;--------------------
;; Verify the guards!
;;--------------------
#|
(verify-guards st-escapable-inv
               :otf-flg t
               :hints (("Goal" :in-theory (disable update-esci neighbors->destsi update-marksi marksi esci marksi depi update-depi neighborsi
                                                   append-to-dep append-to-esc algo-preserves-true-listp-escs algo-preserves-A-natp-escs algo-preserves-A-natp-deps algo-preserves-true-listp-deps)
                               :do-not '(eliminate-destructors generalize)
                               :use ((:instance algo-preserves-true-listp-escs
                                           (n (nodes-length st-nodeset))
                                           (nodes (neighborsi (car nodes) st-graph))
                                           (prev (car nodes))
                                           (marks (update-marksi (car nodes) 1 st-marks))
                                           (graph st-graph)
                                           (nodeset st-nodeset))
                                          (:instance algo-preserves-true-listp-deps
                                           (n (nodes-length st-nodeset))
                                           (nodes (neighborsi (car nodes) st-graph))
                                           (prev (car nodes))
                                           (marks (update-marksi (car nodes) 1 st-marks))
                                           (graph st-graph)
                                           (nodeset st-nodeset))
                                          (:instance algo-preserves-A-natp-escs
                                           (n (nodes-length st-nodeset))
                                           (m (nodes-length st-nodeset))
                                           (nodes (neighborsi (car nodes) st-graph))
                                           (prev (car nodes))
                                           (marks (update-marksi (car nodes) 1 st-marks))
                                           (graph st-graph)
                                           (nodeset st-nodeset))
                                          (:instance algo-preserves-A-natp-deps
                                           (n (nodes-length st-nodeset))
                                           (m (nodes-length st-nodeset))
                                           (nodes (neighborsi (car nodes) st-graph))
                                           (prev (car nodes))
                                           (marks (update-marksi (car nodes) 1 st-marks))
                                           (graph st-graph)
                                           (nodeset st-nodeset))
                                          (:instance algo-does-not-increase-number-of-unmarked-nodes
                                           (nodes1 (show-nodeset (nodes-length st-nodeset) st-nodeset))
                                           (nodes (neighborsi (car nodes) st-graph))
                                           (prev (car nodes))
                                           (marks (update-marksi (car nodes) 1 st-marks))
                                           (graph st-graph)
                                           (nodeset st-nodeset))
                                          (:instance rewrite-update-marksi
                                           (i (car nodes))
                                           (x 2)
                                           (marks st-marks))))))
(verify-guards process-escs-eff
               :otf-flg t
               :hints (("Goal" :in-theory (disable depi esci update-marksi append-to-esc)
                               :use ((:instance A-valid-nodes-neighbors
                                      (i (car nodes))
                                      (n (nodes-length st-nodeset))
                                      (graph st-graph)
                                      (nodeset st-nodeset))
                                     (:instance A-<-valid-nodes
                                      (nodes (neighborsi (car nodes) st-graph))
                                      (marks st-marks)
                                      (nodeset st-nodeset))))))
(verify-guards st-A-nodes-escapable-inv
               :otf-flg t
               :hints (("Goal" :do-not '(eliminate-destructors generalize)
                                        :in-theory (disable marksi nodesi esci depi)
                                        :use ((:instance pp-preserves-A-true-listp-escs
                                               (nodes (filter-34marked-nodes (nodes-length st-nodeset) (st-escapable-inv (list (+ -1 n)) -1 st-graph st-marks st-nodeset) st-nodeset))
                                               (marks (st-escapable-inv (list (+ -1 n)) -1 st-graph st-marks st-nodeset))
                                               (graph st-graph)
                                               (nodeset st-nodeset))
                                              (:instance pp-preserves-A-natp-escs
                                               (nodes (filter-34marked-nodes (nodes-length st-nodeset) (st-escapable-inv (list (+ -1 n)) -1 st-graph st-marks st-nodeset) st-nodeset))
                                               (marks (st-escapable-inv (list (+ -1 n)) -1 st-graph st-marks st-nodeset))
                                               (graph st-graph)
                                               (nodeset st-nodeset))))))
(verify-guards algorithm
               :otf-flg t
               :hints (("Goal" :in-theory (enable A-valid-nodes-show-nodeset))
                       ("Subgoal 1" :use ((:instance algorep-preserves-A-natp-deps
                                            (n (nodes-length st-nodeset))
                                            (marks st-marks)
                                            (graph st-graph)
                                            (nodeset st-nodeset))
                                          (:instance algorep-preserves-A-true-listp-deps
                                            (n (nodes-length st-nodeset))
                                            (marks st-marks)
                                            (graph st-graph)
                                            (nodeset st-nodeset))
                                          (:instance algorep-preserves-A-true-listp-escs
                                            (n (nodes-length st-nodeset))
                                            (marks st-marks)
                                            (graph st-graph)
                                            (nodeset st-nodeset))))))
|#
