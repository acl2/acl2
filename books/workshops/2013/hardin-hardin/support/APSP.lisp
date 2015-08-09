(in-package "ACL2")

; Added by Matt K.: This book has taken only a couple of minutes on a decent
; Linux system in 2013.  However, ACL2 built on GCL 2.6.8 and Mac OS 10.6
; cannot complete the certification without running exhausting STRING storage,
; probably because it contains a large stobj.  So we certify it only in
; "everything" regressions.

;;
;;  This data structure and algorithm implementation is based on
;;  "Accelerating Large Graph Algorithms on the GPU using CUDA" by
;;  Parwan Harish and P.J. Narayanan (2007); and
;;  "Parallelizing Dijkstra's Single-Source Shortest-Path Algorithm" by
;;  Dan Ginsburg (2011).
;;
;;  Implements All-Pairs Shortest Path (APSP) for Weighted Graphs
;;

; cert_param: (non-acl2r)

(local (include-book "integer-listp-theorems"))

(defconst *MAX_VERTICES* 1000000)
(defconst *MAX_EDGES_PER_VERTEX* 10)
(defconst *MAX_EDGES* (* *MAX_VERTICES* *MAX_EDGES_PER_VERTEX*))

(defconst *MAX_SOURCES* 10)

(defconst *MAX_RESULTS* (* *MAX_VERTICES* *MAX_SOURCES*))

(defstobj GraphData
  ;; Vertex count
  (vertexCount :type (integer 0 1000000) :initially 1000000)
  (edgeCount :type (integer 0 10000000) :initially 10000000)

  ;; (V) This contains a pointer to the edge list for each vertex
  ;;  (vertexArray :type (array (integer 0 (1- *MAX_EDGES*)) (*MAX_VERTICES*))
  ;;               :initially 0)
  (vertexArray :type (array (integer 0 9999999) (*MAX_VERTICES*)) :initially 0)

  ;; (E) This contains pointers to the vertices that each edge is attached to
  ;;  (edgeArray :type (array (integer 0 (1- *MAX_VERTICES*)) (*MAX_EDGES*))
  ;;             :initially 0)
  (edgeArray :type (array (integer 0 999999) (*MAX_EDGES*)) :initially 0)

  ;; (W) Weight array
  (weightArray :type (array (integer 0 *) (*MAX_EDGES*)) :initially 0)

  ;; (M) Mask array
  (maskArray :type (array (integer 0 1) (*MAX_VERTICES*)) :initially 0)

  ;; (C) Cost array
  (costArray :type (array (integer 0 *) (*MAX_VERTICES*)) :initially 0)

  ;; (U) Updating cost array
  (updatingCostArray :type (array (integer 0 *) (*MAX_VERTICES*)) :initially 0)

  ;; (S) Source Vertices
  ;; (SourceVertexArray :type (array (integer 0 (1- *MAX_SOURCES*)) (*MAX_SOURCES*))
  ;;                    :initially 0)
  (SourceVertexArray :type (array (integer 0 9) (*MAX_SOURCES*)) :initially 0)

  ;; (R) Results
  (ResultArray :type (array (integer 0 *) (*MAX_RESULTS*)) :initially 0)

:inline t)

;; J Moore's let-inserter -- makes stobj-based code more readable
(defmacro seq (stobj &rest rst)
  (cond ((endp rst) stobj)
        ((endp (cdr rst)) (car rst))
        (t `(let ((,stobj ,(car rst)))
              (seq ,stobj ,@(cdr rst))))))


(defthm integerp-forward-to-rationalp--thm
  (implies (integerp x)
           (rationalp x))
  :rule-classes ((:forward-chaining :trigger-terms ((integerp x))) :rewrite))

(defthm integerp-forward-to-acl2-numberp--thm
  (implies (integerp x)
           (acl2-numberp x))
  :rule-classes ((:forward-chaining :trigger-terms ((integerp x))) :rewrite))


(defthm vertexArray-is-integer-listp--thm
  (implies (vertexArrayp x)
           (integer-listp x))
  :rule-classes ((:forward-chaining :trigger-terms ((vertexArrayp x))) :rewrite))

(defthm edgeArray-is-integer-listp--thm
  (implies (edgeArrayp x)
           (integer-listp x))
  :rule-classes ((:forward-chaining :trigger-terms ((edgeArrayp x))) :rewrite))

(defthm weightArray-is-integer-listp--thm
  (implies (weightArrayp x)
           (integer-listp x))
  :rule-classes ((:forward-chaining :trigger-terms ((weightArrayp x))) :rewrite))

(defthm costArray-is-integer-listp--thm
  (implies (costArrayp x)
           (integer-listp x))
  :rule-classes ((:forward-chaining :trigger-terms ((costArrayp x))) :rewrite))

(defthm updatingCostArray-is-integer-listp--thm
  (implies (updatingCostArrayp x)
           (integer-listp x))
:rule-classes ((:forward-chaining :trigger-terms ((updatingCostArrayp x)))
               :rewrite))

(defthm maskArray-is-integer-listp--thm
  (implies (maskArrayp x)
           (integer-listp x))
  :rule-classes ((:forward-chaining :trigger-terms ((maskArrayp x))) :rewrite))

(defthm sourceVertexArray-is-integer-listp--thm
  (implies (sourceVertexArrayp x)
           (integer-listp x))
:rule-classes ((:forward-chaining :trigger-terms ((sourceVertexArrayp x)))
               :rewrite))

(defthm resultArray-is-integer-listp--thm
  (implies (resultArrayp x)
           (integer-listp x))
  :rule-classes ((:forward-chaining :trigger-terms ((resultArrayp x))) :rewrite))

(defthm weightArrayp-update-nth--thm
  (implies
   (and (weightArrayp n)
        (>= x 0)
        (< x (len n))
        (integerp y)
        (<= 0 y))
   (weightArrayp (update-nth x y n)))
  :rule-classes ((:forward-chaining :trigger-terms ((update-nth x y n))) :rewrite))

(defthm maskArrayp-update-nth--thm
  (implies
   (and (maskArrayp n)
        (>= x 0)
        (< x (len n))
        (or (= y 0) (= y 1)))
   (maskArrayp (update-nth x y n)))
  :rule-classes ((:forward-chaining :trigger-terms ((update-nth x y n))) :rewrite))

(defthm edgeArrayp-update-nth--thm
  (implies
   (and (edgeArrayp n)
        (>= x 0)
        (< x (len n))
        (integerp y)
        (<= 0 y)
        (< y *MAX_VERTICES*))
   (edgeArrayp (update-nth x y n)))
  :rule-classes ((:forward-chaining :trigger-terms ((update-nth x y n))) :rewrite))

(defthm costArrayp-update-nth--thm
  (implies
   (and (costArrayp n)
        (>= x 0)
        (< x (len n))
        (integerp y)
        (>= y 0))
   (costArrayp (update-nth x y n)))
  :rule-classes ((:forward-chaining :trigger-terms ((update-nth x y n))) :rewrite))

(defthm updatingCostArrayp-update-nth--thm
  (implies
   (and (updatingCostArrayp n)
        (>= x 0)
        (< x (len n))
        (integerp y)
        (>= y 0))
   (updatingCostArrayp (update-nth x y n)))
  :rule-classes ((:forward-chaining :trigger-terms ((update-nth x y n))) :rewrite))

(defthm resultArrayp-update-nth--thm
  (implies
   (and (resultArrayp n)
        (>= x 0)
        (< x (len n))
        (integerp y)
        (>= y 0))
   (resultArrayp (update-nth x y n)))
  :rule-classes ((:forward-chaining :trigger-terms ((update-nth x y n))) :rewrite))

(defthm sourceVertexArrayp-update-nth--thm
  (implies
   (and (sourceVertexArrayp n)
        (>= x 0)
        (< x (len n))
        (integerp y)
        (>= y 0)
        (< y *MAX_SOURCES*))
   (sourceVertexArrayp (update-nth x y n)))
  :rule-classes ((:forward-chaining :trigger-terms ((update-nth x y n))) :rewrite))

(defthm costArray-ge-0--thm
  (implies
   (and (costArrayp n)
        (>= x 0)
        (< x (len n)))
   (<= 0 (nth x n)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth x n))) :rewrite))

(defthm updatingCostArray-ge-0--thm
  (implies
   (and (updatingCostArrayp n)
        (>= x 0)
        (< x (len n)))
   (<= 0 (nth x n)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth x n))) :rewrite))

(defthm nth-edgeArray-integerp--thm
  (implies
   (and (edgeArrayp n)
        (>= x 0)
        (< x (len n)))
   (integerp (nth x n)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth x n))) :rewrite))

(defthm nth-weightArray-integerp--thm
  (implies
   (and (weightArrayp n)
        (>= x 0)
        (< x (len n)))
   (integerp (nth x n)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth x n))) :rewrite))

(defthm nth-CostArray-integerp--thm
  (implies
   (and (costArrayp n)
        (>= x 0)
        (< x (len n)))
   (integerp (nth x n)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth x n))) :rewrite))

(defthm nth-updatingCostArray-integerp--thm
  (implies
   (and (updatingCostArrayp n)
        (>= x 0)
        (< x (len n)))
   (integerp (nth x n)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth x n))) :rewrite))

(defthm nth-maskArray-integerp--thm
  (implies
   (and (maskArrayp n)
        (>= x 0)
        (< x (len n)))
   (integerp (nth x n)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth x n))) :rewrite))


(defthm edgeArray-ge-0--thm
  (implies
   (and (edgeArrayp n)
        (>= x 0)
        (< x (len n)))
   (<= 0 (nth x n)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth x n))) :rewrite))

(defthm edgeArray-lt-max-vertex-count--thm
  (implies
   (and (edgeArrayp n)
        (>= x 0)
        (< x (len n)))
   (< (nth x n) *MAX_VERTICES*))
  :rule-classes ((:forward-chaining :trigger-terms ((nth x n))) :rewrite))


(defthm vertexArray-lt-max-edge-count--thm
  (implies
   (and (vertexArrayp n)
        (>= x 0)
        (< x (len n)))
   (< (nth x n) *MAX_EDGES*))
  :rule-classes ((:forward-chaining :trigger-terms ((nth x n))) :rewrite))

(defthm natp-max-edge-count-minus-vertexArrayi--thm
  (implies
   (and (vertexArrayp n)
        (>= x 0)
        (< x (len n)))
   (natp (+ *MAX_EDGES* (- (nth x n)))))
  :rule-classes ((:forward-chaining :trigger-terms ((nth x n))) :rewrite))


(defthm sourceVertexArray-ge-0--thm
  (implies
   (and (sourceVertexArrayp n)
        (>= x 0)
        (< x (len n)))
   (<= 0 (nth x n)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth x n))) :rewrite))

(defthm weightArray-ge-0--thm
  (implies
   (and (weightArrayp n)
        (>= x 0)
        (< x (len n)))
   (<= 0 (nth x n)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth x n))) :rewrite))

(defthm vertexArray-ge-0--thm
  (implies
   (and (vertexArrayp n)
        (>= x 0)
        (< x (len n)))
   (<= 0 (nth x n)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth x n))) :rewrite))


(defun init-vertex-array (i GraphData)
  (declare (xargs :stobjs GraphData
                  :guard (and (natp i) (<= i *MAX_VERTICES*))))
  (cond ((not (and (mbt (GraphDatap GraphData))
                   (mbt (natp i))
                   (mbt (<= i *MAX_VERTICES*)))) GraphData)
        ((mbe :logic (zp i)
              :exec (int= i 0)) GraphData)
        (t
         (seq GraphData
              (update-vertexArrayi (1- i) (* (1- i) *MAX_EDGES_PER_VERTEX*)
                                   GraphData)
              (init-vertex-array (1- i) GraphData)))))

;;(in-theory (enable natp-random$))

(defun init-edge-and-weight-arrays (ix GraphData state)
  (declare (xargs :stobjs (GraphData state)
                  :verify-guards nil
                  :guard (and (natp ix) (<= ix *MAX_EDGES*))))
  (cond ((not (GraphDatap GraphData)) (mv GraphData state))
        ((not (natp ix)) (mv GraphData state))
        ((> ix *MAX_EDGES*) (mv GraphData state))
        ((mbe :logic (zp ix)
              :exec (int= ix 0)) (mv GraphData state))
        (t
         (mv-let (rnd1 state) (random$ *MAX_VERTICES* state)
                 (let ((GraphData (update-edgeArrayi (1- ix) rnd1 GraphData)))
                   (mv-let (rnd2 state) (random$ 100 state)
                           (let ((GraphData (update-weightArrayi
                                             (1- ix)
                                             (if (zp rnd2) 1 rnd2) GraphData)))
                             (init-edge-and-weight-arrays (1- ix)
                                                          GraphData state))))))))


;;;
;;  Generate a random graph
;;

(defun generateRandomGraph (GraphData state)
  (declare (xargs :stobjs (GraphData state)
                  :verify-guards nil))
  (seq GraphData
       (init-vertex-array *MAX_VERTICES* GraphData)
       (init-edge-and-weight-arrays *MAX_EDGES* GraphData state)))

;;
;; Check whether the mask array is empty.  This tells the algorithm whether
;; it needs to continue running or not.
;;

(defun maskArrayEmptyp (i GraphData)
  (declare (xargs :stobjs GraphData
                  :guard (and (natp i) (<= i *MAX_VERTICES*))))
  (cond ((not (and (mbt (GraphDatap GraphData))
                   (mbt (natp i)) (mbt (<= i *MAX_VERTICES*)))) nil)
        ((mbe :logic (zp i)
              :exec (int= i 0)) t)
        ((= (maskArrayi (1- i) GraphData) 1) nil)
        (t (maskArrayEmptyp (1- i) GraphData))))


(defun init-mask-cost-updating-cost (v-down result-num GraphData)
  (declare (xargs :stobjs GraphData
                  :guard (and (natp v-down)
                              (<= v-down *MAX_VERTICES*)
                              (natp result-num)
                              (< result-num *MAX_SOURCES*))))
  (cond ((not (and (mbt (GraphDatap GraphData))
                   (mbt (natp v-down))
                   (mbt (natp result-num))
                   (mbt (< result-num *MAX_SOURCES*))
                   (mbt (<= v-down *MAX_VERTICES*)))) GraphData)
        ((mbe :logic (zp v-down)
              :exec (int= v-down 0)) GraphData)
        (t (seq GraphData
                (if (= (- *MAX_VERTICES* v-down)
                       (sourceVertexArrayi result-num GraphData))
                    (seq GraphData
                         (update-maskArrayi (- *MAX_VERTICES* v-down) 1 GraphData)
                         (update-costArrayi (- *MAX_VERTICES* v-down) 0 GraphData)
                         (update-updatingCostArrayi (- *MAX_VERTICES* v-down) 0
                                                    GraphData))
                  (seq GraphData
                       (update-maskArrayi (- *MAX_VERTICES* v-down) 0 GraphData)
                       (update-costArrayi (- *MAX_VERTICES* v-down)
                                          #xffffffffffffffff GraphData)
                       (update-updatingCostArrayi (- *MAX_VERTICES* v-down)
                                                  #xffffffffffffffff GraphData)))
                (init-mask-cost-updating-cost (1- v-down) result-num GraphData)))))

(defthm imcuc-preserves-true-listp--thm
  (IMPLIES (and (true-listp GraphData)
                (natp v-down)
                (<= v-down *MAX_VERTICES*)
                (natp result-num)
                (< result-num *MAX_SOURCES*))
           (TRUE-LISTP (INIT-MASK-COST-UPDATING-COST v-down result-num GRAPHDATA))))

(defthm imcuc-preserves-len--thm
  (implies (true-listp GraphData)
           (= (len (init-mask-cost-updating-cost v-down result-num GraphData))
              (len GraphData))))

(defthm imcuc-preserves-costArrayp--thm
  (implies (COSTARRAYP (NTH *COSTARRAYI* GraphData))
           (COSTARRAYP
            (NTH *COSTARRAYI*
                 (init-mask-cost-updating-cost v-down result-num GraphData)))))

(defthm imcuc-edgeArray-unchanged--thm
  (= (nth *EDGEARRAYI*
          (init-mask-cost-updating-cost v-down result-num GraphData))
     (nth *EDGEARRAYI* GraphData)))

(defthm imcuc-edgeCount-unchanged--thm
  (= (nth *EDGECOUNT*
          (init-mask-cost-updating-cost v-down result-num GraphData))
     (nth *EDGECOUNT* GraphData)))

(defthm imcuc-preserves-maskArrayp--thm
  (implies (MASKARRAYP (NTH *MASKARRAYI* GraphData))
           (MASKARRAYP
            (NTH *MASKARRAYI*
                 (init-mask-cost-updating-cost v-down result-num GraphData)))))

(defthm imcuc-resultArray-unchanged--thm
  (= (nth *RESULTARRAYI*
          (init-mask-cost-updating-cost v-down result-num GraphData))
     (nth *RESULTARRAYI* GraphData)))

(defthm imcuc-sourceVertexArray-unchanged--thm
  (= (nth *SOURCEVERTEXARRAYI*
          (init-mask-cost-updating-cost v-down result-num GraphData))
     (nth *SOURCEVERTEXARRAYI* GraphData)))

(defthm imcuc-vertexArray-unchanged--thm
  (= (nth *VERTEXARRAYI*
          (init-mask-cost-updating-cost v-down result-num GraphData))
     (nth *VERTEXARRAYI* GraphData)))

(defthm imcuc-vertexCount-unchanged--thm
  (= (car (init-mask-cost-updating-cost v-down result-num GraphData))
     (car GraphData)))

(defthm imcuc-weightArray-unchanged--thm
  (= (nth *WEIGHTARRAYI*
          (init-mask-cost-updating-cost v-down result-num GraphData))
     (nth *WEIGHTARRAYI* GraphData)))

(defthm imcuc-preserves-GraphDatap--thm
  (implies (GraphDatap GraphData)
           (GraphDatap (init-mask-cost-updating-cost v-down result-num GraphData))))

(in-theory (disable init-mask-cost-updating-cost))

(defthm plus-ge-0-if-addends-ge-0--thm
  (implies (and (>= x 0) (>= y 0))
           (<= 0 (+ x y))))

(defthm plus-is-integerp-if-addends-integerp--thm
  (implies (and (integerp x) (integerp y))
           (integerp (+ x y))))

;; Would like to use a more modern arithmetic book, but it interferes with
;; Sol's defiteration macro, amongst other things.
(local (include-book "arithmetic/top-with-meta" :dir :system))

(defun dsk1-inner-loop (edge-down edge-max tid GraphData)
  (declare (xargs :stobjs GraphData
                  :guard (and (natp edge-down)
                              (natp edge-max)
                              (natp tid)
                              (< tid *MAX_VERTICES*)
                              (<= edge-down edge-max)
                              (<= edge-max *MAX_EDGES*))))
  (cond ((not (and (mbt (GraphDatap GraphData))
                   (mbt (natp edge-down))
                   (mbt (natp edge-max))
                   (mbt (natp tid))
                   (mbt (< tid *MAX_VERTICES*))
                   (mbt (<= edge-down edge-max))
                   (mbt (<= edge-max *MAX_EDGES*)))) GraphData)
        ((mbe :logic (zp edge-down)
              :exec (int= edge-down 0)) GraphData)
        (t (let ((updating-index (edgeArrayi
                                   (the (integer 0 *) (- edge-max edge-down))
                                   GraphData)))
             (seq GraphData
                  (update-updatingCostArrayi
                   updating-index
                   (min (updatingCostArrayi updating-index GraphData)
                        (+ (costArrayi tid GraphData)
                           (weightArrayi (- edge-max edge-down) GraphData)))
                   GraphData)
                  (dsk1-inner-loop (1- edge-down) edge-max tid GraphData))))))


(defthm dsk1-il-preserves-true-listp--thm
  (implies (true-listp GraphData)
           (true-listp (dsk1-inner-loop edge-down edge-max tid GraphData))))

(defthm dsk1-il-preserves-len--thm
  (implies (true-listp GraphData)
           (= (len (dsk1-inner-loop edge-down edge-max tid GraphData))
              (len GraphData))))

(defthm dsk1-il-costArray-unchanged--thm
  (= (nth *COSTARRAYI*
          (dsk1-inner-loop edge-down edge-max tid GraphData))
     (nth *COSTARRAYI* GraphData)))

(defthm dsk1-il-edgeArray-unchanged--thm
  (= (nth *EDGEARRAYI*
          (dsk1-inner-loop edge-down edge-max tid GraphData))
     (nth *EDGEARRAYI* GraphData)))

(defthm dsk1-il-edgeCount-unchanged--thm
  (= (nth *EDGECOUNT*
          (dsk1-inner-loop edge-down edge-max tid GraphData))
     (nth *EDGECOUNT* GraphData)))

(defthm dsk1-il-maskArray-unchanged--thm
  (= (nth *MASKARRAYI*
          (dsk1-inner-loop edge-down edge-max tid GraphData))
     (nth *MASKARRAYI* GraphData)))

(defthm dsk1-il-resultArray-unchanged--thm
  (= (nth *RESULTARRAYI*
          (dsk1-inner-loop edge-down edge-max tid GraphData))
     (nth *RESULTARRAYI* GraphData)))

(defthm dsk1-il-sourceVertexArray-unchanged--thm
  (= (nth *SOURCEVERTEXARRAYI*
          (dsk1-inner-loop edge-down edge-max tid GraphData))
     (nth *SOURCEVERTEXARRAYI* GraphData)))

(defthm dsk1-il-vertexArray-unchanged--thm
  (= (nth *VERTEXARRAYI*
          (dsk1-inner-loop edge-down edge-max tid GraphData))
     (nth *VERTEXARRAYI* GraphData)))

(defthm dsk1-il-vertexCount-unchanged--thm
  (= (car (dsk1-inner-loop edge-down edge-max tid GraphData))
     (car GraphData)))

(defthm dsk1-il-weightArray-unchanged--thm
  (= (nth *WEIGHTARRAYI*
          (dsk1-inner-loop edge-down edge-max tid GraphData))
     (nth *WEIGHTARRAYI* GraphData)))

(defthm dsk1-il-preserves-updatingCostArrayp--thm
  (implies (UPDATINGCOSTARRAYP (NTH *UPDATINGCOSTARRAYI* GraphData))
           (UPDATINGCOSTARRAYP
            (NTH *UPDATINGCOSTARRAYI*
                 (DSK1-INNER-LOOP EDGE-DOWN EDGE-MAX TID GRAPHDATA)))))

(defthm dsk1-il-preserves-updatingCostArrayp-len--thm
  (= (LEN (NTH *UPDATINGCOSTARRAYI*
               (DSK1-INNER-LOOP EDGE-DOWN EDGE-MAX TID GRAPHDATA)))
     (LEN (NTH *UPDATINGCOSTARRAYI* GRAPHDATA))))

(defthm dsk1-il-preserves-GraphDatap--thm
  (implies (GraphDatap GraphData)
           (GraphDatap (dsk1-inner-loop edge-down edge-max tid GraphData))))

(in-theory (disable dsk1-inner-loop))

;; (defthm dsk1-il-GraphDatap-maskArray-update--thm
;; (implies (and (GraphDatap GraphData)
;;               (or (= y 0) (= y 1)) (>= 0 x) (< x *MAX_VERTICES*)
;;               (Graphdatap (dsk1-inner-loop edge-down edge-max tid
;;                                                               GraphData)))
;;   (Graphdatap (dsk1-inner-loop edge-down edge-max tid
;;               (UPDATE-NTH *MASKARRAYI*
;;                            (UPDATE-NTH x y (NTH *MASKARRAYI* GRAPHDATA))
;;                            GRAPHDATA)))))

(defthm update-updatingCostArray-vertexArray-unchanged--thm
  (= (nth *VERTEXARRAYI* (UPDATE-NTH *UPDATINGCOSTARRAYI* j GRAPHDATA))
     (nth *VERTEXARRAYI* GraphData)))


;; An instance of Hardin's Bridge:
;;
;; array-based iterative loop --> tail-recursive stobj array fn ==
;; non-tail-recursive stobj arrary fn ==> (thm involving nthcdr or take) ==>
;; primitive-recursive fn operating on a list

;; Load Sol's nice iterator stuff
;; Synthesizes tail-recursive and non-tail-recursive stobj array fns
;; and proves them equal
(include-book "centaur/misc/iter" :dir :system)

;; Iteration macro for a "nondecreasing" predicate on vertex array
(defiteration nondec-arr (res GraphData)
  (declare (xargs :stobjs GraphData))
  (and (<= (vertexArrayi (1- (- *MAX_VERTICES* ix)) GraphData)
           (vertexArrayi (- *MAX_VERTICES* ix) GraphData)) res)
   :returns res
   :index ix
   :last *MAX_VERTICES*
   :first 1
)

;; Output from defiteration:

;; We export NONDEC-ARR$INLINE, NONDEC-ARR-ITER, NONDEC-ARR-TAILREC and
;; NONDEC-ARR-STEP$INLINE.

;; (DEFUN NONDEC-ARR$INLINE (RES GRAPHDATA)
;;   (DECLARE (XARGS :STOBJS GRAPHDATA))
;;   (B* NIL
;;       (MBE :LOGIC (NONDEC-ARR-ITER *MAX_VERTICES* RES GRAPHDATA)
;; 	   :EXEC (NONDEC-ARR-TAILREC 1 RES GRAPHDATA))))

;; (DEFUN NONDEC-ARR-STEP$INLINE
;;   (IX RES GRAPHDATA)
;;   (DECLARE (TYPE (INTEGER 1 *) IX)
;; 	   (IGNORABLE IX RES GRAPHDATA)
;; 	   (XARGS :GUARD-HINTS NIL))
;;   (DECLARE (XARGS :STOBJS GRAPHDATA))
;;   (DECLARE (XARGS :GUARD (AND (<= 1 IX)
;; 			      (< IX *MAX_VERTICES*)
;; 			      T)))
;;   (AND (<= (VERTEXARRAYI (1- (- *MAX_VERTICES* IX))
;; 			 GRAPHDATA)
;; 	   (VERTEXARRAYI (- *MAX_VERTICES* IX)
;; 			 GRAPHDATA))
;;        RES))

;; (DEFUN NONDEC-ARR-ITER (IX RES GRAPHDATA)
;;   (DECLARE (TYPE (INTEGER 1 *) IX)
;; 	   (XARGS :MEASURE (NFIX (- (IFIX IX) (IFIX 1)))
;; 		  :VERIFY-GUARDS NIL))
;;   (DECLARE (XARGS :STOBJS GRAPHDATA))
;;   (DECLARE (XARGS :GUARD (AND (<= 1 IX)
;; 			      (<= IX *MAX_VERTICES*)
;; 			      T)))
;;   (B* (((WHEN (MBE :LOGIC (ZP (- (IFIX IX) (IFIX 1)))
;; 		   :EXEC (INT= 1 IX)))
;; 	RES)
;;        (IX (1- (LIFIX IX)))
;;        (RES (NONDEC-ARR-ITER IX RES GRAPHDATA)))
;;       (NONDEC-ARR-STEP IX RES GRAPHDATA)))

;; (DEFUN NONDEC-ARR-TAILREC (IX RES GRAPHDATA)
;;   (DECLARE
;;    (TYPE (INTEGER 1 *) IX)
;;    (XARGS :MEASURE (NFIX (- (IFIX *MAX_VERTICES*) (IFIX IX)))))
;;   (DECLARE (XARGS :STOBJS GRAPHDATA))
;;   (DECLARE (XARGS :GUARD (AND (<= 1 IX)
;; 			      (<= IX *MAX_VERTICES*)
;; 			      T)))
;;   (B*
;;    (((WHEN (MBE :LOGIC (ZP (- (IFIX *MAX_VERTICES*) (IFIX IX)))
;; 		:EXEC (INT= *MAX_VERTICES* IX)))
;;      RES)
;;     (IX (LIFIX IX))
;;     (RES (NONDEC-ARR-STEP IX RES GRAPHDATA)))
;;    (NONDEC-ARR-TAILREC (1+ IX)
;; 		       RES GRAPHDATA)))


;; Pretty wrapper for the tail-recursive fn
;; Needed for guard proof of dijkstra-sssp-kernel-1
(defun vertices-nondecreasing (GraphData)
  (declare (xargs :stobjs GraphData))
  (cond ((not (GraphDatap GraphData)) nil)
        (t (nondec-arr-tailrec 1 t GraphData))))

;; A primitive-recursive fn operating on a list
;; ACL2 likes these sort of fns
(defun nondec (res lst)
  (declare (xargs :guard (integer-listp lst)))
  (cond ((< (len lst) 2) res)
        (t (and (<= (car lst) (cadr lst))
                (nondec res (cdr lst))))))

;; Just a wrapper of the above
(defun nondecreasing (lst)
  (declare (xargs :guard (integer-listp lst)))
  (nondec t lst))

;; A theorem of the sort readily proven about the above fn
(defthm nondecreasing-nth--thm
  (implies (and (> i 0) (< i (len lst)) (nondecreasing lst))
           (<= (nth (1- i) lst) (nth i lst))))


(local (include-book "data-structures/list-defthms" :dir :system))

(local (include-book "nthcdr-theorems"))

(defthm nth-of-cdr--thm
  (implies (natp x)
           (= (nth x (cdr lst)) (nth (1+ x) lst))))

;; Theorem involving nthcdr -- needed for crossing the bridge
(defthm nondec-arr-iter-eq-nondec-nthcdr--thm
  (implies (and (GraphDatap GraphData) (integerp xx) (>= xx 0)
                (<= xx (len (nth *VERTEXARRAYI* GraphData))))
           (= (nondec-arr-iter xx res GraphData)
              (nondec res (nthcdr (- *MAX_VERTICES* xx)
                      (nth *VERTEXARRAYI* GraphData)))))
:hints (("Goal" :in-theory (enable nondec-arr-iter)))
)

;; Non-tail-recursive stobj array fn = Primitive-recursive list fn
(defthm nondec-arr-iter-*MAX_VERTICES*-eq-nondec--thm
  (implies (GraphDatap GraphData)
           (= (nondec-arr-iter *MAX_VERTICES* res GraphData)
              (nondec res (nth *VERTEXARRAYI* GraphData))))
:hints (("Goal" :use (:instance nondec-arr-iter-eq-nondec-nthcdr--thm
                                  (xx *MAX_VERTICES*))))
)

;; Tail-recursive stobj array fn = Primitive-recursive list fn
(defthm nondec-arr-tail-1-eq-nondec--thm
  (implies (GraphDatap GraphData)
           (= (nondec-arr-tailrec 1 res GraphData)
              (nondec res (nth *VERTEXARRAYI* GraphData)))))

;; Pretty final result -- bridge crossed!
(defthm vertices-nondecreasing-is-nondecreasing--thm
  (implies (GraphDatap GraphData)
           (= (vertices-nondecreasing GraphData)
              (nondecreasing (nth *VERTEXARRAYI* GraphData)))))


;; Now it's easier to prove theorems about the tail-recursive stobj fn --
;; fails to prove without the bridge.
(defthm vertices-nondecreasing-nth--thm
  (implies (and (GraphDatap GraphData)
                (> ix 0)
                (< ix (len (nth *VERTEXARRAYI* GraphData)))
                (vertices-nondecreasing GraphData))
           (<= (vertexArrayi (1- ix) GraphData)
               (vertexArrayi ix GraphData))))

(defthm nondecreasing-vertexArray-nth--thm
  (implies (and (GraphDatap GraphData) (> ix 0)
                (< ix (len (nth *VERTEXARRAYI* GraphData)))
                (nondecreasing (nth *VERTEXARRAYI* GraphData)))
           (<= (vertexArrayi (1- ix) GraphData)
               (vertexArrayi ix GraphData))))

(defthm natp-le-plus-of-neg--thm
  (implies (and (integerp x) (integerp y) (<= x y))
           (natp (+ (- x) y))))

(defthm index-lt-len-means-index-minus-1-lt-len--thm
  (implies (and (> ix 0) (< ix (len y))) (< (1- ix) (len y)))
  :rule-classes ((:forward-chaining :trigger-terms ((< ix (len y)))) :rewrite))

;; Needed to complete the guard proof for dijkstra-sssp-kernel-1
(DEFTHM NONDECREASING-VERTEXARRAY-NATP-DIFF-ADJACENT--THM
  (IMPLIES (AND (integer-listp (NTH *VERTEXARRAYI* GRAPHDATA)) ;;(GRAPHDATAP GRAPHDATA)
                (> IX 0) (< (1- ix) (LEN (NTH *VERTEXARRAYI* GRAPHDATA)))
                (< IX (LEN (NTH *VERTEXARRAYI* GRAPHDATA)))
                (NONDECREASING (NTH *VERTEXARRAYI* GRAPHDATA)))
           (NATP (+ (- (VERTEXARRAYI (1- IX) GRAPHDATA))
                    (VERTEXARRAYI IX GRAPHDATA)))))

;; Sigh...
(defthmd lt-means-le--thm
  (implies (< x y)
           (<= x y)))

(defun dijkstra-sssp-kernel-1 (tid-down GraphData)
  (declare (xargs :stobjs GraphData
                  :guard (and (natp tid-down) (<= tid-down *MAX_VERTICES*)
                              (vertices-nondecreasing GraphData))
                  :guard-hints (("Goal" :in-theory (enable lt-means-le--thm))
                                ("Subgoal 1.3" :USE (:INSTANCE
                                 NONDECREASING-VERTEXARRAY-NATP-DIFF-ADJACENT--THM
                                   (IX (+ 1 *MAX_VERTICES* (- TID-DOWN))))))))
  (cond ((not (and (mbt (GraphDatap GraphData))
                   (mbt (natp tid-down))
                   (mbt (<= tid-down *MAX_VERTICES*)))) GraphData)
        ((mbe :logic (zp tid-down)
              :exec (int= tid-down 0)) GraphData)
        (t (if (= (maskArrayi (- *MAX_VERTICES* tid-down) GraphData) 1)
               (seq GraphData
                    (update-maskArrayi (- *MAX_VERTICES* tid-down) 0 GraphData)
                    (dsk1-inner-loop
                     ;; edge-down = edge-end - edge-start
                     (- (if (< (1+ (- *MAX_VERTICES* tid-down))
                               *MAX_VERTICES*)
                            (vertexArrayi
                             (1+ (- *MAX_VERTICES* tid-down))
                             GraphData)
                          *MAX_EDGES*)
                        (vertexArrayi (- *MAX_VERTICES* tid-down) GraphData))
                     ;; edge-end
                     (if (< (1+ (- *MAX_VERTICES* tid-down))
                            *MAX_VERTICES*)
                         (vertexArrayi
                          (1+ (- *MAX_VERTICES* tid-down))
                          GraphData)
                       *MAX_EDGES*)
                     ;; tid
                     (- *MAX_VERTICES* tid-down)
                     GraphData)
                    (dijkstra-sssp-kernel-1 (1- tid-down) GraphData))
             (dijkstra-sssp-kernel-1 (1- tid-down) GraphData)))))


(defthm dsk1-preserves-true-listp--thm
  (implies (true-listp GraphData)
           (true-listp (dijkstra-sssp-kernel-1 x GraphData))))

(defthm dsk1-preserves-len--thm
  (implies (true-listp GraphData)
           (= (len (dijkstra-sssp-kernel-1 x GraphData))
              (len GraphData))))

(defthm dsk1-costArray-unchanged--thm
  (= (nth *COSTARRAYI*
          (dijkstra-sssp-kernel-1 x GraphData))
     (nth *COSTARRAYI* GraphData)))

(defthm dsk1-edgeArray-unchanged--thm
  (= (nth *EDGEARRAYI*
          (dijkstra-sssp-kernel-1 x GraphData))
     (nth *EDGEARRAYI* GraphData)))

(defthm dsk1-edgeCount-unchanged--thm
  (= (nth *EDGECOUNT*
          (dijkstra-sssp-kernel-1 x GraphData))
     (nth *EDGECOUNT* GraphData)))

(defthm dsk1-resultArray-unchanged--thm
  (= (nth *RESULTARRAYI*
          (dijkstra-sssp-kernel-1 x GraphData))
     (nth *RESULTARRAYI* GraphData)))

(defthm dsk1-sourceVertexArray-unchanged--thm
  (= (nth *SOURCEVERTEXARRAYI*
          (dijkstra-sssp-kernel-1 x GraphData))
     (nth *SOURCEVERTEXARRAYI* GraphData)))

(defthm dsk1-vertexArray-unchanged--thm
  (= (nth *VERTEXARRAYI*
          (dijkstra-sssp-kernel-1 x GraphData))
     (nth *VERTEXARRAYI* GraphData)))

(defthm dsk1-vertexCount-unchanged--thm
  (= (car (dijkstra-sssp-kernel-1 x GraphData))
     (car GraphData)))

(defthm dsk1-weightArray-unchanged--thm
  (= (nth *WEIGHTARRAYI*
          (dijkstra-sssp-kernel-1 x GraphData))
     (nth *WEIGHTARRAYI* GraphData)))

(defthm dsk1-preserves-maskArrayp--thm
  (implies (MASKARRAYP (NTH *MASKARRAYI* GraphData))
           (MASKARRAYP
            (NTH *MASKARRAYI*
                 (DIJKSTRA-SSSP-KERNEL-1 X GRAPHDATA)))))

(defthm dsk1-preserves-maskArrayp-len--thm
  (implies (MASKARRAYP (NTH *MASKARRAYI* GraphData))
           (= (LEN (NTH *MASKARRAYI*
                        (DIJKSTRA-SSSP-KERNEL-1 X GRAPHDATA)))
              (LEN (NTH *MASKARRAYI* GRAPHDATA)))))


(defthm dsk1-preserves-GraphDatap--thm
  (implies (GraphDatap GraphData)
           (GraphDatap (dijkstra-sssp-kernel-1 x GraphData))))

(in-theory (disable dijkstra-sssp-kernel-1))

;; Equivalent of OCL_SSSP_KERNEL2()
(defun dijkstra-sssp-kernel-2 (tid-down GraphData)
  (declare (xargs :stobjs GraphData
                  :guard (and (natp tid-down) (<= tid-down *MAX_VERTICES*))))
  (cond ((not (and (mbt (GraphDatap GraphData))
                   (mbt (natp tid-down))
                   (mbt (<= tid-down *MAX_VERTICES*)))) GraphData)
        ((mbe :logic (zp tid-down)
              :exec (int= tid-down 0)) GraphData)
        (t (seq GraphData
                (if (> (costArrayi (- *MAX_VERTICES* tid-down) GraphData)
                       (updatingCostArrayi (- *MAX_VERTICES* tid-down) GraphData))
                    (seq GraphData
                         (update-costArrayi
                          (- *MAX_VERTICES* tid-down)
                          (updatingCostArrayi (- *MAX_VERTICES* tid-down) GraphData)
                          GraphData)
                         (update-maskArrayi (- *MAX_VERTICES* tid-down) 1
                                            GraphData))
                  (update-updatingCostArrayi (- *MAX_VERTICES* tid-down)
                                             (costArrayi
                                              (- *MAX_VERTICES* tid-down)
                                              GraphData)
                                             GraphData))
                (dijkstra-sssp-kernel-2 (1- tid-down) GraphData)))))

(defthm dsk2-preserves-true-listp--thm
  (implies (true-listp GraphData)
           (true-listp (dijkstra-sssp-kernel-2 x GraphData))))

(defthm dsk2-preserves-len--thm
  (implies (true-listp GraphData)
           (= (len (dijkstra-sssp-kernel-2 x GraphData))
              (len GraphData))))

(defthm dsk2-edgeArray-unchanged--thm
  (= (nth *EDGEARRAYI*
          (dijkstra-sssp-kernel-2 x GraphData))
     (nth *EDGEARRAYI* GraphData)))

(defthm dsk2-edgeCount-unchanged--thm
  (= (nth *EDGECOUNT*
          (dijkstra-sssp-kernel-2 x GraphData))
     (nth *EDGECOUNT* GraphData)))

(defthm dsk2-resultArray-unchanged--thm
  (= (nth *RESULTARRAYI*
          (dijkstra-sssp-kernel-2 x GraphData))
     (nth *RESULTARRAYI* GraphData)))

(defthm dsk2-sourceVertexArray-unchanged--thm
  (= (nth *SOURCEVERTEXARRAYI*
          (dijkstra-sssp-kernel-2 x GraphData))
     (nth *SOURCEVERTEXARRAYI* GraphData)))

(defthm dsk2-vertexArray-unchanged--thm
  (= (nth *VERTEXARRAYI*
          (dijkstra-sssp-kernel-2 x GraphData))
     (nth *VERTEXARRAYI* GraphData)))

(defthm dsk2-vertexCount-unchanged--thm
  (= (car (dijkstra-sssp-kernel-2 x GraphData))
     (car GraphData)))

(defthm dsk2-weightArray-unchanged--thm
  (= (nth *WEIGHTARRAYI*
          (dijkstra-sssp-kernel-2 x GraphData))
     (nth *WEIGHTARRAYI* GraphData)))

(defthm dsk2-preserves-costArrayp--thm
  (implies (COSTARRAYP (NTH *COSTARRAYI* GraphData))
           (COSTARRAYP
            (NTH *COSTARRAYI*
             (DIJKSTRA-SSSP-KERNEL-2 X GRAPHDATA)))))

(defthm dsk2-preserves-costArrayp-len--thm
  (implies (COSTARRAYP (NTH *COSTARRAYI* GraphData))
           (= (LEN (NTH *COSTARRAYI*
                        (DIJKSTRA-SSSP-KERNEL-2 X GRAPHDATA)))
              (LEN (NTH *COSTARRAYI* GRAPHDATA)))))

(defthm dsk2-preserves-maskArrayp--thm
  (implies (MASKARRAYP (NTH *MASKARRAYI* GraphData))
           (MASKARRAYP
            (NTH
             *MASKARRAYI*
             (DIJKSTRA-SSSP-KERNEL-2 X GRAPHDATA)))))

(defthm dsk2-preserves-maskArrayp-len--thm
  (implies (MASKARRAYP (NTH *MASKARRAYI* GraphData))
           (= (LEN (NTH *MASKARRAYI*
                        (DIJKSTRA-SSSP-KERNEL-2 X GRAPHDATA)))
              (LEN (NTH *MASKARRAYI* GRAPHDATA)))))

(defthm dsk2-preserves-updatingCostArrayp--thm
  (implies (UPDATINGCOSTARRAYP (NTH *UPDATINGCOSTARRAYI* GraphData))
           (UPDATINGCOSTARRAYP
            (NTH
             *UPDATINGCOSTARRAYI*
             (DIJKSTRA-SSSP-KERNEL-2 X GRAPHDATA)))))

(defthm dsk2-preserves-updatingCostArrayp-len--thm
  (implies (UPDATINGCOSTARRAYP (NTH *UPDATINGCOSTARRAYI* GraphData))
           (= (LEN (NTH *UPDATINGCOSTARRAYI*
                        (DIJKSTRA-SSSP-KERNEL-2 X GRAPHDATA)))
              (LEN (NTH *UPDATINGCOSTARRAYI* GRAPHDATA)))))

(defthm dsk2-preserves-GraphDatap--thm
  (implies (GraphDatap GraphData)
           (GraphDatap (dijkstra-sssp-kernel-2 x GraphData))))

(in-theory (disable dijkstra-sssp-kernel-2))


(defun mask-array-not-empty-processing (countdown GraphData)
  (declare (xargs :stobjs GraphData
                  :guard (and (natp countdown)
                              (vertices-nondecreasing GraphData))))
  (cond ((not (and (mbt (GraphDatap GraphData))
                   (mbt (natp countdown))
                   (mbt (vertices-nondecreasing GraphData)))) GraphData)
        ((maskArrayEmptyp *MAX_VERTICES* GraphData) GraphData)
        ((mbe :logic (zp countdown)
              :exec (int= countdown 0)) GraphData)
        (t (seq GraphData
                (dijkstra-sssp-kernel-1 *MAX_VERTICES* GraphData)
                (dijkstra-sssp-kernel-2 *MAX_VERTICES* GraphData)
                (mask-array-not-empty-processing (1- countdown) GraphData)))))

(defthm manep-preserves-true-listp--thm
  (IMPLIES (and (true-listp GraphData)
                (>= countdown 0))
           (TRUE-LISTP (mask-array-not-empty-processing countdown GraphData))))

(defthm manep-preserves-len--thm
  (implies (true-listp GraphData)
           (= (len (mask-array-not-empty-processing countdown GraphData))
              (len GraphData))))

(defthm manep-preserves-costArrayp--thm
  (implies (COSTARRAYP (NTH *COSTARRAYI* GraphData))
           (COSTARRAYP
            (NTH *COSTARRAYI*
                 (mask-array-not-empty-processing countdown GraphData)))))

(defthm manep-edgeArray-unchanged--thm
  (= (nth *EDGEARRAYI*
          (mask-array-not-empty-processing countdown GraphData))
     (nth *EDGEARRAYI* GraphData)))

(defthm manep-edgeCount-unchanged--thm
  (= (nth *EDGECOUNT*
          (mask-array-not-empty-processing countdown GraphData))
     (nth *EDGECOUNT* GraphData)))

(defthm manep-preserves-maskArrayp--thm
  (implies (MASKARRAYP (NTH *MASKARRAYI* GraphData))
           (MASKARRAYP
            (NTH *MASKARRAYI*
                 (mask-array-not-empty-processing countdown GraphData)))))

(defthm manep-resultArray-unchanged--thm
  (= (nth *RESULTARRAYI*
          (mask-array-not-empty-processing countdown GraphData))
     (nth *RESULTARRAYI* GraphData)))

(defthm manep-sourceVertexArray-unchanged--thm
  (= (nth *SOURCEVERTEXARRAYI*
          (mask-array-not-empty-processing countdown GraphData))
     (nth *SOURCEVERTEXARRAYI* GraphData)))

(defthm manep-vertexArray-unchanged--thm
  (= (nth *VERTEXARRAYI*
          (mask-array-not-empty-processing countdown GraphData))
     (nth *VERTEXARRAYI* GraphData)))

(defthm manep-vertexCount-unchanged--thm
  (= (car (mask-array-not-empty-processing countdown GraphData))
     (car GraphData)))

(defthm manep-weightArray-unchanged--thm
  (= (nth *WEIGHTARRAYI*
          (mask-array-not-empty-processing countdown GraphData))
     (nth *WEIGHTARRAYI* GraphData)))

(defthm manep-preserves-GraphDatap--thm
  (implies (GraphDatap GraphData)
           (GraphDatap (mask-array-not-empty-processing countdown GraphData))))

(in-theory (disable mask-array-not-empty-processing))


(defun copy-out-results (index-down result-num GraphData)
  (declare (xargs :stobjs GraphData
                  :guard (and (natp index-down)
                              (natp result-num)
                              (<= index-down *MAX_VERTICES*)
                              (< result-num *MAX_SOURCES*))))
  (cond ((not (and (mbt (GraphDatap GraphData))
                   (mbt (natp index-down))
                   (mbt (natp result-num))
                   (mbt (<= index-down *MAX_VERTICES*))
                   (mbt (< result-num *MAX_SOURCES*)))) GraphData)
        ((mbe :logic (zp index-down)
              :exec (int= index-down 0)) GraphData)
        (t (seq GraphData
                ;; Copy the result back
                (update-ResultArrayi
                  (+ (* result-num *MAX_VERTICES*) (1- index-down))
                  (costArrayi (1- index-down) GraphData) GraphData)
                (copy-out-results (1- index-down) result-num GraphData)))))

(defthm cor-preserves-true-listp--thm
  (IMPLIES (true-listp GraphData)
           (TRUE-LISTP (copy-out-results index-down result-num GraphData))))

(defthm cor-preserves-len--thm
  (implies (true-listp GraphData)
           (= (len (copy-out-results index-down result-num GraphData))
              (len GraphData))))

(defthm cor-costArray-unchanged--thm
  (= (nth *COSTARRAYI*
          (copy-out-results index-down result-num GraphData))
     (nth *COSTARRAYI* GraphData)))

(defthm cor-edgeArray-unchanged--thm
  (= (nth *EDGEARRAYI*
          (copy-out-results index-down result-num GraphData))
     (nth *EDGEARRAYI* GraphData)))

(defthm cor-edgeCount-unchanged--thm
  (= (nth *EDGECOUNT*
          (copy-out-results index-down result-num GraphData))
     (nth *EDGECOUNT* GraphData)))

(defthm cor-maskArray-unchanged--thm
  (= (nth *MASKARRAYI*
          (copy-out-results index-down result-num GraphData))
     (nth *MASKARRAYI* GraphData)))

(defthm cor-preserves-resultArrayp--thm
  (implies (RESULTARRAYP (NTH *RESULTARRAYI* GraphData))
           (RESULTARRAYP
            (NTH *RESULTARRAYI*
                 (copy-out-results index-down result-num GraphData)))))

(defthm cor-sourceVertexArray-unchanged--thm
  (= (nth *SOURCEVERTEXARRAYI*
          (copy-out-results index-down result-num GraphData))
     (nth *SOURCEVERTEXARRAYI* GraphData)))

(defthm cor-updatingCostArray-unchanged--thm
  (= (nth *UPDATINGCOSTARRAYI*
          (copy-out-results index-down result-num GraphData))
     (nth *UPDATINGCOSTARRAYI* GraphData)))

(defthm cor-vertexArray-unchanged--thm
  (= (nth *VERTEXARRAYI*
          (copy-out-results index-down result-num GraphData))
     (nth *VERTEXARRAYI* GraphData)))

(defthm cor-vertexCount-unchanged--thm
  (= (car (copy-out-results index-down result-num GraphData))
     (car GraphData)))

(defthm cor-weightArray-unchanged--thm
  (= (nth *WEIGHTARRAYI*
          (copy-out-results index-down result-num GraphData))
     (nth *WEIGHTARRAYI* GraphData)))

(defthm cor-preserves-GraphDatap--thm
  (implies (GraphDatap GraphData)
           (GraphDatap (copy-out-results index-down result-num GraphData))))

(in-theory (disable copy-out-results))


(defun APSP-helper (result-num-down GraphData)
  (declare (xargs :stobjs GraphData
                  :guard (and (natp result-num-down)
                              (<= result-num-down *MAX_SOURCES*)
                              (vertices-nondecreasing GraphData))))
  (cond ((not (and (mbt (GraphDatap GraphData))
                   (mbt (natp result-num-down))
                   (mbt (<= result-num-down *MAX_SOURCES*)))) GraphData)
        ((mbe :logic (zp result-num-down)
              :exec (int= result-num-down 0)) GraphData)
        (t (seq GraphData
                (init-mask-cost-updating-cost *MAX_VERTICES*
                                              (- *MAX_SOURCES* result-num-down)
                                              GraphData)
                (mask-array-not-empty-processing #xffffffff GraphData)
                (copy-out-results *MAX_VERTICES*
                                  (- *MAX_SOURCES* result-num-down) GraphData)
                (APSP-helper (1- result-num-down) GraphData)))))


(defun init-source-vertex-array (index-down numResults GraphData)
  (declare (xargs :stobjs GraphData
                  :guard (and (natp index-down)
                              (natp numResults)
                              (<= index-down *MAX_SOURCES*)
                              (<= numResults *MAX_SOURCES*))))
  (cond ((not (and (mbt (GraphDatap GraphData))
                   (mbt (natp index-down))
                   (mbt (natp numResults))
                   (mbt (<= index-down *MAX_SOURCES*))
                   (mbt (<= numResults *MAX_SOURCES*)))) GraphData)
        ((mbe :logic (zp numResults)
              :exec (int= numResults 0)) GraphData)
        ((mbe :logic (zp index-down)
              :exec (int= index-down 0)) GraphData)
        (t (seq GraphData
                (if (<= index-down numResults)
                    (update-SourceVertexArrayi (1- index-down) (1- index-down)
                                               GraphData)
                  (update-SourceVertexArrayi (1- index-down) 0 GraphData))
                (init-source-vertex-array (1- index-down) numResults GraphData)))))

(defthm isva-0-0--thm
  (implies (GraphDatap GraphData)
           (= (INIT-SOURCE-VERTEX-ARRAY 0 1 GRAPHDATA) GraphData)))

(defthm isva-0-1--thm
  (implies (GraphDatap GraphData)
           (= (INIT-SOURCE-VERTEX-ARRAY 0 1 GRAPHDATA) GraphData)))

(defthm isva-index-1-0--thm
  (implies (GraphDatap GraphData)
           (= (INIT-SOURCE-VERTEX-ARRAY 1 0 GRAPHDATA) GraphData)))

(defthm isva-1-1--thm
  (implies (GraphDatap GraphData)
           (= (INIT-SOURCE-VERTEX-ARRAY 1 1 GRAPHDATA)
              (update-SourceVertexArrayi 0 0 GraphData))))


(defthm isva-preserves-true-listp--thm
  (IMPLIES (true-listp GraphData)
           (TRUE-LISTP (init-source-vertex-array index-down numResults GraphData))))

(defthm isva-preserves-len--thm
  (implies (true-listp GraphData)
           (= (len (init-source-vertex-array index-down numResults GraphData))
              (len GraphData))))

(defthm isva-costArray-unchanged--thm
  (= (nth *COSTARRAYI*
          (init-source-vertex-array index-down numResults GraphData))
     (nth *COSTARRAYI* GraphData)))

(defthm isva-edgeArray-unchanged--thm
  (= (nth *EDGEARRAYI*
          (init-source-vertex-array index-down numResults GraphData))
     (nth *EDGEARRAYI* GraphData)))

(defthm isva-edgeCount-unchanged--thm
  (= (nth *EDGECOUNT*
          (init-source-vertex-array index-down numResults GraphData))
     (nth *EDGECOUNT* GraphData)))

(defthm isva-maskArray-unchanged--thm
  (= (nth *MASKARRAYI*
          (init-source-vertex-array index-down numResults GraphData))
     (nth *MASKARRAYI* GraphData)))

(defthm isva-resultArray-unchanged--thm
  (= (nth *RESULTARRAYI*
          (init-source-vertex-array index-down numResults GraphData))
     (nth *RESULTARRAYI* GraphData)))

(defthm isva-preserves-sourceVertexArrayp--thm
  (implies (SOURCEVERTEXARRAYP (NTH *SOURCEVERTEXARRAYI* GraphData))
           (SOURCEVERTEXARRAYP
            (NTH *SOURCEVERTEXARRAYI*
                 (init-source-vertex-array index-down numResults GraphData)))))

(defthm isva-updatingCostArray-unchanged--thm
  (= (nth *UPDATINGCOSTARRAYI*
          (init-source-vertex-array index-down numResults GraphData))
     (nth *UPDATINGCOSTARRAYI* GraphData)))

(defthm isva-vertexArray-unchanged--thm
  (= (nth *VERTEXARRAYI*
          (init-source-vertex-array index-down numResults GraphData))
     (nth *VERTEXARRAYI* GraphData)))

(defthm isva-vertexCount-unchanged--thm
  (= (car (init-source-vertex-array index-down numResults GraphData))
     (car GraphData)))

(defthm isva-weightArray-unchanged--thm
  (= (nth *WEIGHTARRAYI*
          (init-source-vertex-array index-down numResults GraphData))
     (nth *WEIGHTARRAYI* GraphData)))

(defthm isva-preserves-GraphDatap--thm
  (implies (GraphDatap GraphData)
           (GraphDatap (init-source-vertex-array index-down numResults GraphData))))

(in-theory (disable init-source-vertex-array))


(defun init-results (index-down GraphData)
  (declare (xargs :stobjs GraphData
                  :guard (and (natp index-down)
                              (<= index-down *MAX_RESULTS*))))
  (cond ((not (and (mbt (GraphDatap GraphData))
                   (mbt (natp index-down))
                   (mbt (<= index-down *MAX_RESULTS*)))) GraphData)
        ((mbe :logic (zp index-down)
              :exec (int= index-down 0)) GraphData)
        (t (seq GraphData
                (update-ResultArrayi (1- index-down) 0 GraphData)
                (init-results (1- index-down) GraphData)))))


(defthm ir-preserves-true-listp--thm
  (IMPLIES (true-listp GraphData)
           (TRUE-LISTP (init-results index-down GraphData))))

(defthm ir-preserves-len--thm
  (implies (true-listp GraphData)
           (= (len (init-results index-down GraphData))
              (len GraphData))))

(defthm ir-costArray-unchanged--thm
  (= (nth *COSTARRAYI*
          (init-results index-down GraphData))
     (nth *COSTARRAYI* GraphData)))

(defthm ir-preserves-costArrayp--thm
  (implies (COSTARRAYP (NTH *COSTARRAYI* GraphData))
           (COSTARRAYP
            (NTH *COSTARRAYI*
                 (init-results index-down GraphData)))))

(defthm ir-edgeArray-unchanged--thm
  (= (nth *EDGEARRAYI*
          (init-results index-down GraphData))
     (nth *EDGEARRAYI* GraphData)))

(defthm ir-edgeCount-unchanged--thm
  (= (nth *EDGECOUNT*
          (init-results index-down GraphData))
     (nth *EDGECOUNT* GraphData)))

(defthm ir-maskArray-unchanged--thm
  (= (nth *MASKARRAYI*
          (init-results index-down GraphData))
     (nth *MASKARRAYI* GraphData)))

(defthm ir-preserves-resultArrayp--thm
  (implies (RESULTARRAYP (NTH *RESULTARRAYI* GraphData))
           (RESULTARRAYP
            (NTH *RESULTARRAYI*
                 (init-results index-down GraphData)))))

(defthm ir-sourceVertexArray-unchanged--thm
  (= (nth *SOURCEVERTEXARRAYI*
          (init-results index-down GraphData))
     (nth *SOURCEVERTEXARRAYI* GraphData)))

(defthm ir-updatingCostArray-unchanged--thm
  (= (nth *UPDATINGCOSTARRAYI*
          (init-results index-down GraphData))
     (nth *UPDATINGCOSTARRAYI* GraphData)))

(defthm ir-vertexArray-unchanged--thm
  (= (nth *VERTEXARRAYI*
          (init-results index-down GraphData))
     (nth *VERTEXARRAYI* GraphData)))

(defthm ir-vertexCount-unchanged--thm
  (= (car (init-results index-down GraphData))
     (car GraphData)))

(defthm ir-weightArray-unchanged--thm
  (= (nth *WEIGHTARRAYI*
          (init-results index-down GraphData))
     (nth *WEIGHTARRAYI* GraphData)))

(defthm ir-preserves-GraphDatap--thm
  (implies (GraphDatap GraphData)
           (GraphDatap (init-results index-down GraphData))))

(in-theory (disable init-results))


;; Top-level function
(defun APSP (numResults GraphData)
  (declare (xargs :stobjs GraphData
                  :guard (and (natp numResults)
                              (<= numResults *MAX_SOURCES*)
                              (vertices-nondecreasing GraphData))))
  (cond ((not (and (mbt (GraphDatap GraphData))
                   (mbt (natp numResults))
                   (mbt (<= numResults *MAX_SOURCES*)))) GraphData)
        (t (seq GraphData
                (init-source-vertex-array *MAX_SOURCES* numResults GraphData)
                (init-results *MAX_RESULTS* GraphData)
                (APSP-helper numResults GraphData)))))

;;;;;;;; Testing regime
;;
;; (ld "APSP.lisp" :ld-pre-eval-print t)
;; (generateRandomGraph GraphData state)
;; (time$ (APSP *MAX_SOURCES* GraphData))
;;
;; In general:
;; (APSP <numberofsources> GraphData)
;;
;;;;;;;;
