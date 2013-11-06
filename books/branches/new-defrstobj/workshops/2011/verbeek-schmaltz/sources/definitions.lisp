#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#


(in-package "ACL2")

(include-book "ordinals/lexicographic-ordering" :dir :system)
(include-book "GeNoC-misc")
(include-book "data-structures/list-defuns"  :dir :system)
(include-book "data-structures/list-defthms"  :dir :system)

;;------------------
;; Data structures
;;------------------

;; Because we need to declare the size of the stobjs statically, we must define the number of ports.
(defconst *dimension* (list 20 20))
(defconst *params* (list (list *dimension* nil)))

(defstobj st-marks
  (marks :type (array (integer 0 4) (4000)) :initially 0)
  (esc   :type (array list (4000)) :initially nil)
  (dep   :type (array list (4000)) :initially nil)
  :inline t)

(defstobj st-graph
  (neighbors        :type (array list (4000)) :initially nil)
  (neighbors->dests :type (array list (4000)) :initially nil)
  :inline t)
(defstobj st-nodeset
  (nodes :type (array (integer 0 1) (4000)) :initially 0)
  :inline t)

;;-----------
;; Macro's:
;;-----------
(defmacro marked (node marks)
  `(or (equal (marksi ,node ,marks) 1)
       (equal (marksi ,node ,marks) 2)
       (equal (marksi ,node ,marks) 3)
       (equal (marksi ,node ,marks) 4)))
(defmacro seq (stobj &rest rst)
  (cond ((endp rst) stobj)
        ((endp (cdr rst)) (car rst))
        (t `(let ((,stobj ,(car rst)))
             (seq ,stobj ,@(cdr rst))))))
(defmacro to-trace (x p)
  `(let ((temp (trace-this ,x)))
     (declare (ignore temp))
     ,p))
(defmacro unresolved (node marks)
  `(not (subsetp (depi ,node ,marks) (esci ,node ,marks))))
(defmacro dests-of (node params/)
  `(filter-reachable-dests ,node (dep-all-vertices ,params/) ,params/))
(defmacro st-valid-node (node nodeset)
  `(and (natp ,node)
        (< ,node (nodes-length ,nodeset))
        (equal (nodesi ,node ,nodeset) 1)))
(defmacro st-all-nodes (nodeset)
  `(show-nodeset (nodes-length ,nodeset) ,nodeset))



;;-----------
;; Functions:
;;-----------

;; Used for debugging:
(defun trace-this (x)
  (declare (ignore x)
           (xargs :guard t))
  nil)
(defun show-marks (n st-marks)
  (declare (xargs :stobjs st-marks
                  :guard (and (natp n)
                              (<= n (marks-length st-marks)))))
  (cond ((zp n)
         nil)
        ((marked (1- n) st-marks)
         (cons (1- n) (show-marks (1- n) st-marks)))
        (t
         (show-marks (1- n) st-marks))))

;; Functions used in guards
(defun A-valid-nodes (x st-nodeset)
  (declare (xargs :stobjs st-nodeset
                  :guard (true-listp x)))
  (if (endp x)
    t
    (and (natp (car x))
         (< (car x) (nodes-length st-nodeset))
         (equal (nodesi (car x) st-nodeset) 1)
         (A-valid-nodes (cdr x) st-nodeset))))
(defun A-true-listp-escs (n st-marks)
  (declare (xargs :stobjs st-marks
                  :guard (and (natp n)
                              (<= n (esc-length st-marks)))))
  (if (zp n)
    t
    (and (true-listp (esci (1- n) st-marks))
         (A-true-listp-escs (1- n) st-marks))))
(defun A-true-listp-deps (n st-marks)
  (declare (xargs :stobjs st-marks
                  :guard (and (natp n)
                              (<= n (dep-length st-marks)))))
  (if (zp n)
    t
    (and (true-listp (depi (1- n) st-marks))
         (A-true-listp-deps (1- n) st-marks))))
(defun true-listp-values (alist)
  (declare (xargs :guard (alistp alist)))
  (if (endp alist)
    t
    (and (true-listp (cdar alist))
         (true-listp-values (cdr alist)))))
(defun A-natp (x)
  (declare (xargs :guard (true-listp x)))
  (if (endp x)
    t
    (and (natp (car x))
         (A-natp (cdr x)))))
(defun A-valid-nodes-values (alist st-nodeset)
  (declare (xargs :stobjs st-nodeset
                  :guard (and (alistp alist)
                              (true-listp-values alist))))
  (if (endp alist)
    t
    (and (A-valid-nodes (cdar alist) st-nodeset)
         (A-valid-nodes-values (cdr alist) st-nodeset))))
(defun valid-graph (n st-graph st-nodeset)
  (declare (xargs :stobjs (st-graph st-nodeset)
                  :guard (and (natp n)
                              (<= n (neighbors->dests-length st-graph)))))
  (if (zp n)
    t
    (and (alistp (neighbors->destsi (1- n) st-graph))
         (true-listp-values (neighbors->destsi (1- n) st-graph))
         (A-valid-nodes-values (neighbors->destsi (1- n) st-graph) st-nodeset)
         (true-listp (neighborsi (1- n) st-graph))
         (A-valid-nodes (neighborsi (1- n) st-graph) st-nodeset)
         (valid-graph (1- n) st-graph st-nodeset))))
(defun show-nodeset (n st-nodeset)
  (declare (xargs :stobjs st-nodeset
                  :guard (and (natp n)
                              (<= n (nodes-length st-nodeset)))))
  (cond ((zp n)
         nil)
         ((equal (nodesi (1- n) st-nodeset) 1)
          (cons (1- n) (show-nodeset (1- n) st-nodeset)))
         (t
          (show-nodeset (1- n) st-nodeset))))
(defun A-natp-deps (n st-marks)
  (declare (xargs :stobjs st-marks
                  :guard (and (natp n)
                              (<= n (dep-length st-marks))
                              (A-true-listp-deps n st-marks))))
  (if (zp n)
    t
    (and (A-natp (depi (1- n) st-marks))
         (A-natp-deps (1- n) st-marks))))
(defun A-natp-escs (n st-marks)
  (declare (xargs :stobjs st-marks
                  :guard (and (natp n)
                              (<= n (esc-length st-marks))
                              (A-true-listp-escs n st-marks))))
  (if (zp n)
    t
    (and (A-natp (esci (1- n) st-marks))
         (A-natp-escs (1- n) st-marks))))
(defun A-<_guarded (x n)
  (declare (xargs :guard (and (natp n)
                              (true-listp x)
                              (A-natp x))))
  (if (endp x)
    t
    (and (< (car x) n)
         (A-<_guarded (cdr x) n))))


;; Guarded functions for the algorithm
;; First the theorems needed to prove these guards
(defthm consp-esci-->esci
  (implies (and (A-true-listp-escs n marks)
               (< i n)
               (natp i)
               (natp n))
          (iff (consp (nth i (nth *esci* marks)))
               (nth i (nth *esci* marks)))))
(defthm consp-depi-->depi
  (implies (and (A-true-listp-deps n marks)
               (< i n)
               (natp i)
               (natp n))
          (iff (consp (nth i (nth *depi* marks)))
               (nth i (nth *depi* marks)))))
(defthm alistp-neighbors->destsi
  (implies (and (valid-graph n graph nodeset)
                (< i n)
                (natp i)
                (natp n))
           (alistp (nth i (nth *neighbors->destsi* graph)))))
(defthm consp-assoc-neighbors->destsi-->assoc-neighbors->destsi
  (implies (and (valid-graph n graph nodeset)
                (< i n)
                (natp i)
                (natp n))
           (iff (consp (assoc j (nth i (nth *neighbors->destsi* graph))))
                (assoc j (nth i (nth *neighbors->destsi* graph))))))
(defthm true-listp-neighborsi
  (implies (and (valid-graph n graph nodeset)
                (< i n)
                (natp i)
                (natp n))
           (true-listp (nth i (car graph)))))
(defthm true-listp-cdr-assoc
  (implies (true-listp-values alist)
           (true-listp (cdr (assoc x alist)))))
(defthm true-listp-values-neighbors->destsi
  (implies (and (valid-graph n graph nodeset)
                (< node n)
                (natp n)
                (natp node))
           (true-listp-values (neighbors->destsi node graph))))

;; The functions used in the algorithm
(defun append-to-esc (node escs st-marks)
  (declare (xargs :stobjs (st-marks)
                  :guard (and (natp node)
                              (< node (esc-length st-marks))
                              (true-listp escs)
                              (A-true-listp-escs (esc-length st-marks) st-marks))))
  (update-esci node (append escs (esci node st-marks)) st-marks))
(defun append-to-dep (node deps st-marks)
  (declare (xargs :stobjs (st-marks)
                  :guard (and (natp node)
                              (< node (dep-length st-marks))
                              (true-listp deps)
                              (A-true-listp-deps (dep-length st-marks) st-marks))))
  (update-depi node (append deps (depi node st-marks)) st-marks))#|ACL2s-ToDo-Line|#

(defun dests-of-edge (node neighbor st-graph st-nodeset)
  (declare (xargs :stobjs (st-graph st-nodeset)
                  :guard (and (or (equal node -1)
                                  (and (natp node)
                                       (< node (neighbors->dests-length st-graph))))
                              (natp neighbor)
                              (valid-graph (neighbors->dests-length st-graph) st-graph st-nodeset)))
           (ignore st-nodeset))
  (if (equal node -1)
    nil
    (cdr (assoc neighbor (neighbors->destsi node st-graph)))))
(defun append-to-data (key data alist)
  (cond ((endp alist)
         (acons key data nil))
        ((equal (caar alist) key)
         (cons (append (car alist) data) (cdr alist)))
        (t
         (cons (car alist) (append-to-data key data (cdr alist))))))



;; Functions used in the proofs
(defun st-filter-2marked-nodes (nodes st-marks)
  (declare (xargs :stobjs (st-marks)
                  :guard (and (true-listp nodes)
                              (A-natp nodes)
                              (A-<_guarded nodes (marks-length st-marks)))))
  (cond ((endp nodes)
         nil)
        ((equal (marksi (car nodes) st-marks) 2)
         (cons (car nodes) (st-filter-2marked-nodes (cdr nodes) st-marks)))
        (t
         (st-filter-2marked-nodes (cdr nodes) st-marks))))
(defun st-filter-unmarked123-nodes (nodes st-marks)
  (declare (xargs :stobjs (st-marks)
                  :guard (and (true-listp nodes)
                              (A-natp nodes)
                              (A-<_guarded nodes (marks-length st-marks)))))
  (cond ((endp nodes)
         nil)
        ((not (marked (car nodes) st-marks))
         (cons (car nodes) (st-filter-unmarked123-nodes (cdr nodes) st-marks)))
        (t
         (st-filter-unmarked123-nodes (cdr nodes) st-marks))))
(defun st-filter-parents (n node st-graph st-nodeset)
  (declare (xargs :stobjs (st-graph st-nodeset)
                  :verify-guards nil))
  (cond ((zp n)
         nil)
        ((and (member-equal node (neighborsi (1- n) st-graph))
              (st-valid-node (1- n) st-nodeset))
         (cons (1- n) (st-filter-parents (1- n) node st-graph st-nodeset)))
        (t
         (st-filter-parents (1- n) node st-graph st-nodeset))))
(defun st-filter-3marked-nodes (nodes st-marks)
  (declare (xargs :stobjs (st-marks)
                  :verify-guards nil))
  (cond ((endp nodes)
         nil)
        ((equal (marksi (car nodes) st-marks) 3)
         (cons (car nodes) (st-filter-3marked-nodes (cdr nodes) st-marks)))
        (t
         (st-filter-3marked-nodes (cdr nodes) st-marks))))
(defun filter-3marked-nodes (n st-marks st-nodeset)
  (declare (xargs :stobjs (st-marks st-nodeset)
                  :guard (and (natp n)
                              (<= n (marks-length st-marks)))))
  (cond ((zp n)
         nil)
        ((and (equal (marksi (1- n) st-marks) 3)
              (equal (nodesi (1- n) st-nodeset) 1))
         (cons (1- n) (filter-3marked-nodes (1- n) st-marks st-nodeset)))
        (t
         (filter-3marked-nodes (1- n) st-marks st-nodeset))))
(defun filter-4marked-nodes (n st-marks st-nodeset)
  (declare (xargs :stobjs (st-marks st-nodeset)
                  :guard (and (natp n)
                              (<= n (marks-length st-marks)))))
  (cond ((zp n)
         nil)
        ((and (equal (marksi (1- n) st-marks) 4)
              (equal (nodesi (1- n) st-nodeset) 1))
         (cons (1- n) (filter-4marked-nodes (1- n) st-marks st-nodeset)))
        (t
         (filter-4marked-nodes (1- n) st-marks st-nodeset))))
(defun st-filter-3parents (node n st-marks st-graph st-nodeset)
  (declare (xargs :stobjs (st-marks st-graph st-nodeset)
                  :guard (and (valid-graph (nodes-length st-nodeset) st-graph st-nodeset)
                              (natp n)
                              (<= n (nodes-length st-nodeset)))))
  (cond ((zp n)
         nil)
        ((and (member-equal node (neighborsi (1- n) st-graph))
              (or (equal (marksi (1- n) st-marks) 3)
                  (equal (marksi (1- n) st-marks) 4))
              (equal (nodesi (1- n) st-nodeset) 1))
         (cons (1- n) (st-filter-3parents node (1- n) st-marks st-graph st-nodeset)))
        (t
         (st-filter-3parents node (1- n) st-marks st-graph st-nodeset))))
(defun A-dests-of (node neighbors st-graph st-nodeset)
  (declare (xargs :stobjs (st-graph st-nodeset)
                  :guard-hints (("Goal" :in-theory (disable neighbors->destsi)))
                  :guard (and (natp node)
                              (< node (nodes-length st-nodeset))
                              (true-listp neighbors)
                              (A-valid-nodes neighbors st-nodeset)
                              (valid-graph (nodes-length st-nodeset) st-graph st-nodeset))))
  (cond ((endp neighbors)
         nil)
        (t
         (append (dests-of-edge node (car neighbors) st-graph st-nodeset)
                 (A-dests-of node (cdr neighbors) st-graph st-nodeset)))))


;; Functions used in measures:
;; computes x\y, i.e., all elements of x not in y
(defun setminus (x y)
  (if (endp x)
    x
    (if (member-equal (car x) y)
      (setminus (cdr x) y)
      (cons (car x) (setminus (cdr x) y)))))
;; returns the number of elements in y that are not in x
(defun diff-size (x y)
  (if (endp y)
    0
    (let ((recur (diff-size x (cdr y))))
      (if (member-equal (car y) x)
        recur
        (nfix (1+ recur))))))
(defun num-of-edges-not-in-stack (n stack st-graph)
  (declare (xargs :stobjs st-graph
                  :verify-guards nil))
  (if (zp n)
    0
    (+ (diff-size (cdr (assoc (1- n) stack)) (neighborsi (1- n) st-graph))
       (num-of-edges-not-in-stack (1- n) stack st-graph))))
(defun A-consp (X)
  (if (endp X)
    t
    (and (consp (car X))
         (A-consp (cdr X)))))






;; BEGIN st-filter-unmarked123-nodes
(defthm st-filter-unmarked123-nodes-update-marksi
  (implies (and (marked node marks)
                (or (equal x 1) (equal x 2) (equal x 3) (equal x 4)))
           (equal (st-filter-unmarked123-nodes nodes (update-marksi node x marks))
                  (st-filter-unmarked123-nodes nodes marks))))
(defthm subsetp-st-filter-unmarked123-nodes
  (subsetp (st-filter-unmarked123-nodes nodes marks) nodes))
(defthm member-st-filter-unmarked123-nodes
  (implies (and (not (marked node marks))
                (member-equal node nodes))
           (member-equal node (st-filter-unmarked123-nodes nodes marks))))
(defthm st-filter-unmarked123-nodes-udpate-esci
  (equal (st-filter-unmarked123-nodes nodes (update-esci i x marks))
         (st-filter-unmarked123-nodes nodes marks)))
(defthm st-filter-unmarked123-nodes-update-depi
  (equal (st-filter-unmarked123-nodes nodes (update-depi i x marks))
         (st-filter-unmarked123-nodes nodes marks)))
(defthm A-valid-nodes-neighborsi
  (implies (and (valid-graph n graph nodeset)
                (< i n)
                (natp i)
                (natp n))
           (A-valid-nodes (nth i (car graph)) nodeset)))
(defthm consp-neighborsi->neighborsi
  (implies (and (valid-graph n graph nodeset)
                (< i n)
                (natp i)
                (natp n))
           (iff (consp (nth i (car graph)))
                (nth i (car graph)))))
(defthm true-listp-esci
  (implies (and (A-true-listp-escs n marks)
               (< i n)
               (natp i)
               (natp n))
          (true-listp (nth i (nth *esci* marks)))))
(defthm marksi-update-marksi-equal
  (equal (marksi n (update-marksi n x marks)) x))
(defthm marksi-update-marksi
  (implies (and (natp i)
                (natp j))
           (equal (marksi i (update-marksi j x marks))
                  (if (equal i j)
                    x
                    (marksi i marks)))))
(defthm st-filter-unmarked-123-nodes-update-marksi
  (implies (and (natp node)
                (A-natp nodes)
                (not (member-equal node nodes)))
           (equal (st-filter-unmarked123-nodes nodes (update-marksi node x marks))
                  (st-filter-unmarked123-nodes nodes marks)))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :in-theory (disable esci depi update-marksi append-to-esc append-to-dep neighborsi neighbors->destsi marksi))))
(defthm len-st-filter-unmarked-123-nodes-update-marksi-2
  (implies (natp node)
           (<= (len (st-filter-unmarked123-nodes nodes (update-marksi node 2 marks)))
               (len (st-filter-unmarked123-nodes nodes marks))))
  :rule-classes :linear)
(defthm len-st-filter-unmarked-123-nodes-update-marksi-3
  (implies (natp node)
           (<= (len (st-filter-unmarked123-nodes nodes (update-marksi node 3 marks)))
               (len (st-filter-unmarked123-nodes nodes marks))))
  :rule-classes :linear)
(defthm len-st-filter-unmarked-123-nodes-update-marksi-4
  (implies (natp node)
           (<= (len (st-filter-unmarked123-nodes nodes (update-marksi node 4 marks)))
               (len (st-filter-unmarked123-nodes nodes marks))))
  :rule-classes :linear)
(defthm member-implies-occurrences-equal-ac->=-n
  (implies (member-equal a x)
           (>= (occurrences-equal-ac a x n) n))
  :rule-classes :linear)
(defthm member-implies-occurrences->=-1
  (implies (member-equal a x)
           (>= (occurrences-equal a x) 1))
  :rule-classes :linear
  :hints (("Goal" :expand (occurrences-equal a x))))
(defthm ocurrences-equal-0-->not-member
  (iff (equal (occurrences-equal a x) 0)
       (not (member-equal a x))))
(defthm A-valid-nodes-implies-A-natp
  (implies (A-valid-nodes nodes nodeset)
           (A-natp nodes)))
(defthm member-show-nodeset
  (iff (member-equal i (show-nodeset n nodeset))
       (and (natp n)
            (equal (nth i (car nodeset)) 1)
            (natp i)
            (< i n))))
(defthm member-show-all-nodes
  (implies (and (A-valid-nodes nodes nodeset)
                (member-equal node nodes))
           (member-equal node (show-nodeset (nodes-length nodeset) nodeset))))
(defthm not-member-unmarked-implies-marked
  (implies (member-equal node nodes)
           (iff (not (member-equal node (st-filter-unmarked123-nodes nodes marks)))
                (marked node marks))))
(defthm st-filter-unmarked123-nodes-update-marksi-1
  (implies (and (natp node)
                (A-valid-nodes nodes nodeset))
           (equal (st-filter-unmarked123-nodes nodes (update-marksi node 1 marks))
                  (remove-equal node (st-filter-unmarked123-nodes nodes marks))))
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :in-theory (disable esci depi update-marksi append-to-esc append-to-dep neighborsi neighbors->destsi marksi))))
(defthm true-listp-st-filter-unmarked123-nodes
  (true-listp (st-filter-unmarked123-nodes nodes marks))
  :rule-classes :type-prescription)
;; END st-filter-unmarked123-nodes


;; BEGIN filter-3marked-nodes
(defthm filter-3marked-nodes-append-to-esc
  (equal (filter-3marked-nodes n (append-to-esc i x marks) nodeset)
         (filter-3marked-nodes n marks nodeset)))
(defthm len-filter-3marked-nodes-update-marksi-2
  (<= (len (filter-3marked-nodes n (update-marksi i 2 marks) nodeset))
      (len (filter-3marked-nodes n marks nodeset)))
  :rule-classes :linear)
(defthm len-filter-3marked-nodes-update-marksi-1
  (<= (len (filter-3marked-nodes n (update-marksi i 1 marks) nodeset))
      (len (filter-3marked-nodes n marks nodeset)))
  :rule-classes :linear)
(defthm len-<-filter-3marked-nodes-update-marksi-2
  (implies (and (< i n)
                (natp i)
                (natp n)
                (equal (nodesi i nodeset) 1)
                (equal (marksi i marks) 3))
           (< (len (filter-3marked-nodes n (update-marksi i 2 marks) nodeset))
              (len (filter-3marked-nodes n marks nodeset))))
  :rule-classes :linear
  :hints (("Subgoal *1/2" :use (:instance len-filter-3marked-nodes-update-marksi-2
                                  (n i)))))
(defthm marksi-update-depi
  (equal (marksi i (update-depi j x marks))
         (marksi i marks)))
(defthm marksi-update-esci
  (equal (marksi i (update-esci j x marks))
         (marksi i marks)))
(defthm marksi-update-marksi-update-esci
  (equal (marksi i (update-marksi j x (update-esci k y marks)))
         (marksi i (update-marksi j x marks))))
(defthm marksi-update-marksi-update-depi
  (equal (marksi i (update-marksi j x (update-depi k y marks)))
         (marksi i (update-marksi j x marks))))
(defthm filter-3marked-nodes-update-marksi-append-to-esc
  (equal (filter-3marked-nodes n (update-marksi j y (append-to-esc i x marks)) nodeset)
         (filter-3marked-nodes n (update-marksi j y marks) nodeset))
  :hints (("Goal" :in-theory (disable neighborsi marksi update-marksi esci update-esci))))
;; END filter-3marked-nodes

;; BEGIN filter-4marked-nodes
(defthm filter-4marked-nodes-append-to-esc
  (equal (filter-4marked-nodes n (append-to-esc i x marks) nodeset)
         (filter-4marked-nodes n marks nodeset)))
(defthm len-filter-4marked-nodes-update-marksi-2
  (<= (len (filter-4marked-nodes n (update-marksi i 2 marks) nodeset))
      (len (filter-4marked-nodes n marks nodeset)))
  :rule-classes :linear)
(defthm len-filter-4marked-nodes-update-marksi-1
  (<= (len (filter-4marked-nodes n (update-marksi i 1 marks) nodeset))
      (len (filter-4marked-nodes n marks nodeset)))
  :rule-classes :linear)
(defthm len-<-filter-4marked-nodes-update-marksi-2
  (implies (and (< i n)
                (natp i)
                (natp n)
                (equal (nodesi i nodeset) 1)
                (equal (marksi i marks) 4))
           (< (len (filter-4marked-nodes n (update-marksi i 2 marks) nodeset))
              (len (filter-4marked-nodes n marks nodeset))))
  :rule-classes :linear
  :hints (("Subgoal *1/2" :use (:instance len-filter-4marked-nodes-update-marksi-2
                                  (n i)))))
(defthm filter-4marked-nodes-update-marksi-append-to-esc
  (equal (filter-4marked-nodes n (update-marksi j y (append-to-esc i x marks)) nodeset)
         (filter-4marked-nodes n (update-marksi j y marks) nodeset))
  :hints (("Goal" :in-theory (disable neighborsi marksi update-marksi esci update-esci))))
;; END filter-4marked-nodes



;; BEGIN st-filter-2marked-nodes
(defthm subsetp-st-filter-2marked-nodes-setminus
  (subsetp (st-filter-2marked-nodes (setminus nodes x) marks) nodes))
(defthm not-in-st-filter-2marked-nodes-setminus
  (not-in (st-filter-2marked-nodes (setminus nodes x) marks) x))

(defthm st-filter-2marked-nodes-update-depi
  (equal (st-filter-2marked-nodes nodes (update-depi i x marks))
         (st-filter-2marked-nodes nodes marks)))
(defthm st-filter-2marked-nodes-update-marksi-1
  (implies (not (equal (marksi i marks) 2))
           (equal (st-filter-2marked-nodes nodes (update-marksi i 1 marks))
                  (st-filter-2marked-nodes nodes marks))))
(defthm st-filter-2marked-nodes-update-esci
  (equal (st-filter-2marked-nodes nodes (update-esci i x marks))
         (st-filter-2marked-nodes nodes marks)))

(defthm st-filter-2marked-nodes-update-marksi-non-member
  (implies (and (natp node)
                (A-natp nodes)
                (not (member-equal node nodes)))
           (equal (st-filter-2marked-nodes nodes (update-marksi node x marks))
                  (st-filter-2marked-nodes nodes marks)))
  :hints (("Goal" :in-theory (disable esci depi update-marksi marksi))))
(defthm st-filter-2marked-nodes-update-marksi-ineffective
  (implies (equal (marksi node marks) x)
           (equal (st-filter-2marked-nodes nodes (update-marksi node x marks))
                  (st-filter-2marked-nodes nodes marks))))
(defthm st-filter-unmarked123-nodes-update-marksi-unmarked
  (implies (and (natp node)
                (A-natp nodes)
                (or (equal x 1) (equal x 2) (equal x 3)))
           (equal (st-filter-unmarked123-nodes nodes (update-marksi node x marks))
                  (remove-equal node (st-filter-unmarked123-nodes nodes marks)))))
(defthm subsetp-st-filter-2marked-nodes-update-marksi-3
  (subsetp (st-filter-2marked-nodes nodes (update-marksi node 3 marks))
           (st-filter-2marked-nodes nodes marks)))
(defthm remove-st-filter-2marked-nodes-update
  (implies (and (natp node)
                (A-natp nodes)
                (not (equal (marksi node marks) 2)))
           (equal (remove-equal node (st-filter-2marked-nodes nodes (update-marksi node 2 marks)))
                  (st-filter-2marked-nodes nodes marks))))
(defthm st-filter-2marked-nodes-update-marksi-update-esci
  (equal (st-filter-2marked-nodes nodes (update-marksi j y (update-esci i x marks)))
         (st-filter-2marked-nodes nodes (update-marksi j y marks))))
(defthm st-filter-2marked-nodes-update-marksi-update-depi
  (equal (st-filter-2marked-nodes nodes (update-marksi j y (update-depi i x marks)))
         (st-filter-2marked-nodes nodes (update-marksi j y marks))))
(defthm spec-of-member-st-filter-2marked-nodes
  (iff (member-equal node (st-filter-2marked-nodes nodes marks))
       (and (member-equal node nodes)
            (equal (marksi node marks) 2)))
  :hints (("Goal" :in-theory (disable marksi))))

(defthm st-filter-2marked-nodes-append-to-esc
  (equal (st-filter-2marked-nodes nodes (append-to-esc i x marks))
         (st-filter-2marked-nodes nodes marks)))
(defthm st-filter-2marked-nodes-append-to-dep
  (equal (st-filter-2marked-nodes nodes (append-to-dep i x marks))
         (st-filter-2marked-nodes nodes marks)))
(defthm st-filter-2marked-nodes-update-marksi-append-to-esc
  (equal (st-filter-2marked-nodes nodes (update-marksi i x (append-to-esc j y marks)))
         (st-filter-2marked-nodes nodes (update-marksi i x marks))))
(defthm st-filter-2marked-nodes-update-marksi-append-to-dep
  (equal (st-filter-2marked-nodes nodes (update-marksi i x (append-to-dep j y marks)))
         (st-filter-2marked-nodes nodes (update-marksi i x marks))))
(defthm A-valid-nodes-st-filter-2marked-nodes
  (implies (A-valid-nodes nodes nodeset)
           (A-valid-nodes (st-filter-2marked-nodes nodes marks) nodeset)))
(defthm st-filter-2marked-nodes-update-marksi-2-nomember
  (implies (and (natp node)
                (A-natp nodes)
                (not (member-equal node nodes)))
           (equal (st-filter-2marked-nodes nodes (update-marksi node 2 marks))
                  (st-filter-2marked-nodes nodes marks)))
  :hints (("Goal" :in-theory (disable update-marksi marksi))))
(defthm A-natp-st-filter-2marked-nodes
  (implies (A-natp nodes)
           (A-natp (st-filter-2marked-nodes nodes marks))))
(defthm subsetp-st-filter-2marked-nodes
  (subsetp (st-filter-2marked-nodes nodes marks) nodes))
;; END st-filter-2marked-nodes





;; BEGIN st-filter-unmarked123-nodes;:TODO
(defthm st-filter-unmarked123-nodes-append-to-esc
  (equal (st-filter-unmarked123-nodes nodes (append-to-esc i x marks))
         (st-filter-unmarked123-nodes nodes marks)))
(defthm st-filter-unmarked123-nodes-append-to-dep
  (equal (st-filter-unmarked123-nodes nodes (append-to-dep i x marks))
         (st-filter-unmarked123-nodes nodes marks)))
;; END st-filter-unmarked123-nodes

;; BEGIN st-filter-3marked-nodes;:TODO
(defthm A-natp-st-filter-3marked-nodes
  (implies (A-natp nodes)
           (A-natp (st-filter-3marked-nodes nodes marks))))
(defthm st-filter-3marked-nodes-append
  (equal (st-filter-3marked-nodes (append x y) marks)
         (append (st-filter-3marked-nodes x marks)
                 (st-filter-3marked-nodes y marks))))
(defthm st-filter-3marked-nodes-update-marksi-2
  (let ((marks-after (update-marksi i 2 marks)))
    (implies (and (natp i)
                  (A-natp nodes))
             (equal (st-filter-3marked-nodes nodes marks-after)
                    (remove-equal i (st-filter-3marked-nodes nodes marks)))))
  :hints (("Goal" :in-theory (disable update-marksi marksi))))
(defthm st-filter-3marked-nodes-append-to-esc
  (equal (st-filter-3marked-nodes nodes (append-to-esc i x marks))
         (st-filter-3marked-nodes nodes marks)))
(defthm st-filter-3marked-nodes-remove
  (equal (st-filter-3marked-nodes (remove-equal node nodes) marks)
         (remove-equal node (st-filter-3marked-nodes nodes marks))))
(defthm st-filter-3marked-nodes-filter-3-marked-nodes
  (equal (st-filter-3marked-nodes (filter-3marked-nodes n marks nodeset) marks)
         (filter-3marked-nodes n marks nodeset)))
(defthm spec-of-filter-3marked-nodes
  (iff (member-equal i (filter-3marked-nodes n marks nodeset))
       (and (natp i)
            (natp n)
            (< i n)
            (equal (nodesi i nodeset) 1)
            (equal (marksi i marks) 3))))
(defthm consp-filter-3marked-nodes
  (implies (and (natp n)
                (natp node)
                (equal (marksi node marks) 3)
                (equal (nodesi node nodeset) 1)
                (< node n))
           (consp (filter-3marked-nodes n marks nodeset))))
;; END st-filter-3marked-nodes

;; BEGIN st-filter-3parents;:TODO
(defthm st-filter-3parents-update-marksi-2
  (let ((marks-after (update-marksi i 2 marks)))
    (implies (and (natp i)
                  (A-natp nodes))
             (equal (st-filter-3parents node n marks-after graph nodeset)
                    (remove-equal i (st-filter-3parents node n marks graph nodeset)))))
  :hints (("Goal" :in-theory (disable update-marksi marksi))))
(defthm st-filter-3parents-append-to-esc
  (equal (st-filter-3parents node n (append-to-esc i x marks) graph nodeset)
         (st-filter-3parents node n marks graph nodeset)))
(defthm member-st-filter-3parents
  (iff (member-equal parent (st-filter-3parents node n marks graph nodeset))
       (and (member-equal node (neighborsi parent graph))
            (or (equal (marksi parent marks) 3)
                (equal (marksi parent marks) 4))
            (equal (nodesi parent nodeset) 1)
            (natp parent)
            (natp n)
            (< parent n))))
;; END st-filter-3parents
