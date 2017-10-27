#||

seq-pp-equivalence.lisp
~~~~~~~~~~~~~~~~~~~~~~~~

Author: Disha Puri
Last Updated: 12th April 2014

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Invariant
;; We are claiming that executing pre pipeline + k iterations of loop pipeline, where you do not exit
;; is same as executing seq-loop for pre + (k-1) iterations of seq-loop + m blocks of seq-loop + m-I blocks
;; of seq-loop and so on till 0 or 1

;; From this invariant, we want to claim that running pre-pp-loop + k iterations of pp-loop + post-pp-loop
;; is same as running seq-loop for pre + (k-1) iterations of seq-loop + x iterations of seq-loop where x =
;; number of iterations created from pre and post






||#

(in-package "ACL2")
(include-book "superstep-construction")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Defining the invariant
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; x is state after k iterations of pipelined loop
;; run seq for k iterations completely + (run-block-seq blocks m)
;; seq-ccdfg == (list '(1 2 3) '(1 2 3) nil)
(defun get-m-blocks-seq (m c pp-interval)
  (if (or (not (posp m))
          (not (posp pp-interval))) nil
    (if (<= m pp-interval) (take-n m c) ; why doesn't it terminate without this?
      (append (take-n m c)
              (get-m-blocks-seq (- m pp-interval) c pp-interval)))))

(defun pipeline-loop-invariant (pp-state k pre loop pp-interval init-state prev m)
  (let* ((seq-loop-top (run-block-set pre init-state nil prev))
         (seq-loop-k (run-blocks-iters loop seq-loop-top (- k 1) prev))
         (seq-loop-x (run-block-set (get-m-blocks-seq m loop pp-interval) seq-loop-k nil prev)))
    (equal pp-state
           seq-loop-x)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Theorems
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm get-m-block-seq-equal-pre-superstep
  (equal (pre-superstep-from-loop m loop pp-interval)
         (get-m-blocks-seq m loop pp-interval))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(pre-superstep-from-loop
                                 get-m-blocks-seq)))))

(defthm ceiling-m-pp-interval
  (implies (and (posp m)
                (posp pp-interval)
                (<= m pp-interval))
           (equal (ceiling m pp-interval) 1)))

(defthm ceiling-m-pp-interval-add
  (implies (and (posp m)
                (posp pp-interval)
                (> m pp-interval))
           (equal (ceiling m pp-interval)
                  (+ (ceiling (- m pp-interval) pp-interval) 1))))

(defthm ceiling-+
  (implies (and (posp m)
                (posp pp-interval)
                (< pp-interval m))
           (> (ceiling (- m pp-interval) pp-interval) 0)))

(defthm ceiling-same
  (implies (posp m)
           (equal (ceiling m m) 1)))


(defthm ceiling-natp
  (implies (and (posp m)
                (posp pp-interval))
           (natp (ceiling m pp-interval))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Invariant base case
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun induction-hint-invariant-case (m loop init-state pp-interval prev)
  (if (or (not (posp m))
          (not (posp pp-interval))
          (<= m pp-interval)) (list m loop init-state pp-interval prev)
    (induction-hint-invariant-case (- m pp-interval) loop
                                   (run-block-set (take-n (+ m pp-interval) loop) init-state nil prev)
                                   pp-interval
                                   prev)))

(defthm branch-restriction-get-m-seq
  (implies (branch-restriction-ccdfg loop)
           (branch-restriction-ccdfg (get-m-blocks-seq m loop pp-interval)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(branch-restriction-ccdfg
                                 get-m-blocks-seq)))))

(defthm invariant-base-case-loop
  (implies (and (posp m)
                (posp pp-interval)
                (branch-restriction-ccdfg loop)
                (not (equal (loop-superstep-from-loop m loop pp-interval) "error")))
           (equal (run-block-set
                   (loop-superstep-from-loop m loop pp-interval)
                   (run-block-set (pre-superstep-from-loop m loop pp-interval)
                                  init-state nil prev)
                   nil prev)
                  (run-block-set (get-m-blocks-seq m loop pp-interval)
                                 (run-block-set (take-n (+ m pp-interval) loop)
                                                init-state
                                                nil prev)
                                 nil prev)))
  :otf-flg t
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(induction-hint-invariant-case
                                 branch-restriction-loop-from-loop
                                 branch-restriction-pre-from-loop
                                 branch-restriction-get-m-seq
                                 loop-superstep-from-loop
                                 pre-superstep-from-loop
                                 get-m-blocks-seq
                                 take-return-take
                                 run-block-set-append
                                 run-block-set-nil
                                 branch-restriction-take-n
                                 branch-restriction-remove-n))
    :induct (induction-hint-invariant-case m loop init-state pp-interval prev)
    :do-not-induct t
    :do-not '(eliminate-destructors fertilize generalize))
   ("Subgoal *1/2.1"
    :use
    ((:instance run-block-set-no-conflict
                (a (take-n pp-interval (remove-n m loop)))
                (b (pre-superstep-from-loop (- m pp-interval) loop pp-interval))
                (init-state (run-block-set (take-n m loop) init-state nil prev)))))))

(defthm invariant-base-case-subgoal-1
  (implies (and (posp m)
                (posp pp-interval)
                (branch-restriction-ccdfg pre)
                (branch-restriction-ccdfg loop)
                (not (equal (loop-superstep-in-order m pre loop pp-interval) "error")))
           (equal (run-block-set (loop-superstep-in-order m pre loop pp-interval)
                                 (run-block-set (pre-superstep-in-order m pre loop pp-interval)
                                                init-state nil prev)
                                 nil prev)
                  (run-block-set (get-m-blocks-seq m loop pp-interval)
                                 (run-block-set pre init-state nil prev)
                                 nil prev)))

  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(branch-restriction-ccdfg-cdr
                                 branch-restriction-remove-n
                                 branch-restriction-take-n
                                 branch-restriction-loop-from-loop
                                 branch-restriction-pre-from-loop
                                 branch-restriction-get-m-seq
                                 pre-superstep-in-order
                                 loop-superstep-in-order
                                 get-m-blocks-seq
                                 run-block-set-append
                                 run-block-set-cons
                                 run-block-set-nil
                                 run-block-set-remove-take-n
                                 error-loop
                                 loop-superstep-error))
    :do-not-induct t
    :use
    ((:instance run-block-set-no-conflict
                (a (remove-n m pre))
                (b (pre-superstep-from-loop (- m pp-interval) loop pp-interval))
                (init-state (run-block-set (take-n m pre) init-state nil prev)))
     (:instance invariant-base-case-loop
                (init-state (RUN-BLOCK-SET PRE INIT-STATE NIL PREV))
                (m (- m pp-interval)))))))

;; pp-ccdfg is the pipelined ccdfg created by superstep-construction
;; pp-state is state after running pp-ccdfg for pre + k iterations
;; then, invariant is true, which means pp-state is equal to executing seq-ccdfg's pre + (- k 1) iterations + sequence of m
;; (let* ((m (+ (* (floor (- (len (car seq-ccdfg)) (+ pp-interval 1)) pp-interval) pp-interval) 1))

(defthm invariant-base-case
  (implies (and (phi-restriction-ccdfg pre)
                (phi-restriction-ccdfg loop)
                (equal k 1)
                (posp m)
                (posp pp-interval)
                (branch-restriction-ccdfg pre)
                (branch-restriction-ccdfg loop)
                (true-listp pre)
                (true-listp loop)
                (not (equal (pre-supersteps-in-parallel m pre loop pp-interval) "error"))
                (not (equal (loop-superstep-in-parallel m pre loop pp-interval) "error"))
                (not (equal (loop-superstep-in-order m pre loop pp-interval) "error"))
                (equal pp-ccdfg (superstep-construction pre loop pp-interval m))
                (equal pp-state (run-ccdfg-k (car pp-ccdfg) (cadr pp-ccdfg)
                                             1 init-state prev)))
           (pipeline-loop-invariant pp-state 1 pre loop pp-interval init-state prev m))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(pipeline-loop-invariant
                                 superstep-construction
                                 branch-restriction-ccdfg-cdr
                                 branch-restriction-remove-n
                                 branch-restriction-take-n
                                 branch-restriction-loop-from-loop
                                 branch-restriction-pre-from-loop
                                 branch-restriction-get-m-seq
                                 pre-parallel-order-same
                                 loop-parallel-order-same
                                 run-blocks-iters
                                 run-ccdfg-k
                                 run-block-set-from-iters
                                 invariant-base-case-subgoal-1
                                 phi-restriction-loop-superstep-in-order))
    :use
    ((:instance phi-restriction-block-set
                (c (loop-superstep-in-order m pre loop pp-interval))
                (i (run-block-set (pre-superstep-in-order m pre loop pp-interval)
                                  init-state nil prev))
                (next nil)
                (pre1 (prefix (car (last (cadar (last (loop-superstep-in-parallel m pre loop pp-interval)))))))
                (pre2 prev)))
    :do-not-induct t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Prove for k > 1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm invariant-greater-1-subgoal-2
  (implies (and (posp m)
                (posp pp-interval)
                (branch-restriction-ccdfg loop)
                (not (equal (loop-superstep-from-loop m loop pp-interval) "error")))
           (equal (run-block-set (loop-superstep-from-loop m
                                                           loop pp-interval)
                                 (run-block-set (get-m-blocks-seq
                                                 m
                                                 loop pp-interval)
                                                init-state nil prev)
                                 nil prev)
                  (run-block-set (get-m-blocks-seq m loop pp-interval)
                                 (run-block-set (take-n (+ m pp-interval) loop) init-state nil prev)
                                 nil prev)))
  :otf-flg t
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(induction-hint-invariant-case
                                 branch-restriction-ccdfg-cdr
                                 branch-restriction-remove-n
                                 branch-restriction-take-n
                                 branch-restriction-loop-from-loop
                                 branch-restriction-pre-from-loop
                                 branch-restriction-get-m-seq
                                 loop-superstep-error
                                 loop-superstep-from-loop
                                 get-m-blocks-seq
                                 run-block-set-append
                                 take-n-plus-interval
                                 get-m-block-seq-equal-pre-superstep))
    :induct (induction-hint-invariant-case m loop init-state pp-interval prev)
    :do-not-induct t
    :do-not '(eliminate-destructors fertilize generalize))
   ("Subgoal *1/2.1"
    :use
    ((:instance run-block-set-no-conflict
                (a (take-n pp-interval (remove-n m loop)))
                (b (get-m-blocks-seq (- m pp-interval) loop pp-interval))
                (init-state (run-block-set (take-n m loop) init-state nil prev)))))))

(defthm invariant-greater-1-subgoal
  (implies (and (posp m)
                (posp pp-interval)
                (> m pp-interval)
                (branch-restriction-ccdfg pre)
                (branch-restriction-ccdfg loop)
                (not (equal (loop-superstep-in-order m pre loop pp-interval) "error")))
           (equal (run-block-set (loop-superstep-from-loop (- m pp-interval)
                                                           loop pp-interval)
                                 (run-block-set (get-m-blocks-seq
                                                 (- m pp-interval)
                                                 loop pp-interval)
                                                init-state nil prev)
                                 nil prev)
                  (run-block-set (get-m-blocks-seq (- m pp-interval) loop pp-interval)
                                 (run-block-set (take-n m loop) init-state nil prev)
                                 nil prev)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(loop-superstep-error
                                 error-loop
                                 get-m-block-seq-equal-pre-superstep
                                 branch-restriction-ccdfg-cdr
                                 branch-restriction-remove-n
                                 branch-restriction-take-n
                                 branch-restriction-loop-from-loop
                                 branch-restriction-pre-from-loop
                                 branch-restriction-get-m-seq))
    :use
    ((:instance invariant-greater-1-subgoal-2
                (m (- m pp-interval)))))))

(defthm phi-restriction-ccdfg-append
  (implies (and (phi-restriction-ccdfg a)
                (phi-restriction-ccdfg b))
           (phi-restriction-ccdfg (append a b))))

(defthm phi-restriction-loop-from-loop
  (implies (phi-restriction-ccdfg loop)
           (phi-restriction-ccdfg (loop-superstep-from-loop x loop pp-interval)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(phi-restriction-ccdfg
                                 loop-superstep-from-loop
                                 phi-restriction-cdr
                                 phi-restriction-ccdfg-append
                                 phi-restriction-remove-n
                                 phi-restriction-take-n)))))

(defthm phi-restriction-loop-in-order
  (implies (and (phi-restriction-ccdfg pre)
                (phi-restriction-ccdfg loop))
           (phi-restriction-ccdfg (loop-superstep-in-order m pre loop pp-interval)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(phi-restriction-ccdfg
                                 loop-superstep-in-order
                                 phi-restriction-cdr
                                 phi-restriction-ccdfg-append
                                 phi-restriction-remove-n
                                 phi-restriction-take-n
                                 phi-restriction-loop-from-loop)))))

(DEFTHM
  phi-RESTRICTION-GET-M-SEQ
  (IMPLIES (phi-RESTRICTION-CCDFG LOOP)
           (phi-RESTRICTION-CCDFG
            (GET-M-BLOCKS-SEQ M LOOP PP-INTERVAL)))
  :HINTS
  (("Goal" :IN-THEORY
    (UNION-THEORIES
     (THEORY 'GROUND-ZERO)
     '(phi-RESTRICTION-CCDFG GET-M-BLOCKS-SEQ)))))

(defthm invariant-holds-k-greater-1
  (implies (and (posp k)
                (posp m)
                (posp pp-interval)
                (<= m (len pre))
                (consp pre)
                (consp loop)
                (seq-ccdfg-p (list pre loop))
                (phi-restriction-ccdfg pre)
                (phi-restriction-ccdfg loop)
                (branch-restriction-ccdfg loop)
                (branch-restriction-ccdfg pre)
                (true-listp pre)
                (true-listp loop)
                (not (equal (pre-supersteps-in-parallel m pre loop pp-interval) "error"))
                (not (equal (loop-superstep-in-parallel m pre loop pp-interval) "error"))
                (not (equal (loop-superstep-in-order m pre loop pp-interval) "error"))
                (equal pp-ccdfg (superstep-construction pre loop pp-interval m))
                (equal pp-state (run-ccdfg-k (car pp-ccdfg) (second pp-ccdfg) k init-state prev))
                (pipeline-loop-invariant pp-state k pre loop pp-interval init-state prev m))
           (pipeline-loop-invariant (run-ccdfg-k (car pp-ccdfg) (second pp-ccdfg) (+ k 1) init-state prev)
                                    (+ k 1) pre loop pp-interval init-state prev m))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(run-block-set-append
                                 run-ccdfg-k
                                 pre-parallel-order-same
                                 loop-parallel-order-same
                                 phi-restriction-get-m-seq
                                 superstep-construction
                                 pipeline-loop-invariant
                                 run-block-iters-append
                                 branch-restriction-take-n
                                 branch-restriction-remove-n
                                 branch-restriction-pre-from-loop
                                 branch-restriction-loop-from-loop
                                 branch-restriction-get-m-seq
                                 phi-restriction-take-n
                                 phi-restriction-remove-n
                                 phi-restriction-ccdfg-append
                                 phi-restriction-loop-from-loop
                                 loop-superstep-in-order
                                 get-m-blocks-seq
                                 pre-loop-cdr-same
                                 run-block-set-append
                                 run-block-set-remove-take-n
                                 error-loop
                                 invariant-greater-1-subgoal
                                 loop-superstep-error
                                 get-m-block-seq-equal-pre-superstep))
    :do-not-induct t
    :use
    ((:instance phi-restriction-block-iters
                (c (loop-superstep-in-order m pre loop pp-interval))
                (i (run-block-set (pre-superstep-in-order m pre loop pp-interval) init-state nil prev))
                (iter k)
                (pre1 (prefix (last (cadar (loop-superstep-in-parallel m pre loop pp-interval)))))
                (pre2 prev))
     (:instance phi-restriction-block-iters
                (c (loop-superstep-in-order m pre loop pp-interval))
                (i (run-block-set (pre-superstep-in-order m pre loop pp-interval) init-state nil prev))
                (iter (+ k 1))
                (pre1 (prefix (last (cadar (loop-superstep-in-parallel m pre loop pp-interval)))))
                (pre2 prev))
     (:instance phi-restriction-block-set
                (c (loop-superstep-in-order m pre loop pp-interval))
                (i (run-block-set (get-m-blocks-seq m loop pp-interval)
                                  (run-blocks-iters loop (run-block-set pre init-state nil prev)
                                                    (- k 1)
                                                    prev) nil prev))
                (next nil)
                (pre1 (prefix (car (last (cadar (last (loop-superstep-in-parallel m pre loop pp-interval)))))))
                (pre2 prev))
     (:instance run-block-iters-reverse-append
                (c loop)
                (i (run-block-set pre init-state nil prev)))
     (:instance run-block-set-remove-take-n
                (pre loop)
                (init-state (run-block-set (pre-superstep-from-loop m loop pp-interval)
                                           (run-blocks-iters loop
                                                             (run-block-set pre init-state nil prev)
                                                             (+ -1 k)
                                                             prev)
                                           nil prev)))
     (:instance run-block-set-remove-take-n
                (pre loop)
                (init-state (run-blocks-iters loop (run-block-set pre init-state nil prev)
                                              (+ -1 k) prev))
                (prev (prefix (car (last (cadar (last (loop-superstep-in-parallel m pre loop pp-interval))))))))
     (:instance run-block-set-no-conflict
                (a (remove-n m loop))
                (b (get-m-blocks-seq (- m pp-interval)
                                     loop pp-interval))
                (init-state (run-block-set (take-n m loop)
                                           (run-blocks-iters loop
                                                             (run-block-set pre init-state nil prev)
                                                             (+ -1 k)
                                                             prev)
                                           nil prev)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Invariant holds
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun induction-hint-invariant-function (k m pre loop pp-interval prev init-state)
  (if (not (posp k)) (list m pre loop pp-interval prev init-state)
    (induction-hint-invariant-function (- k 1) m pre loop pp-interval prev init-state)))

(defthm invariant-holds
  (implies (and (posp k)
                (posp m)
                (posp pp-interval)
                (true-listp pre)
                (true-listp loop)
                (consp pre)
                (consp loop)
                (<= m (len pre))
                (phi-restriction-ccdfg pre)
                (phi-restriction-ccdfg loop)
                (branch-restriction-ccdfg pre)
                (branch-restriction-ccdfg loop)
                (seq-ccdfg-p (list pre loop))
                (not (equal (pre-supersteps-in-parallel m pre loop pp-interval) "error"))
                (not (equal (loop-superstep-in-order m pre loop pp-interval) "error"))
                (not (equal (loop-superstep-in-parallel m pre loop pp-interval) "error"))
                (equal pp-ccdfg (superstep-construction pre loop pp-interval m)))
           (pipeline-loop-invariant
            (run-ccdfg-k (car pp-ccdfg) (second pp-ccdfg) k init-state prev)
            k pre loop pp-interval init-state prev m))
  :otf-flg t
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(induction-hint-invariant-function))
    :induct (induction-hint-invariant-function k m pre loop pp-interval prev init-state)
    :do-not-induct t)
   ("Subgoal *1/2'"
    :in-theory (union-theories (theory 'ground-zero)
                               '(invariant-base-case)))

   ("Subgoal *1/1"
    :in-theory (union-theories (theory 'ground-zero)
                               '(invariant-base-case))
    :use
    ((:instance invariant-holds-k-greater-1
                (k (- k 1))
                (pp-ccdfg (superstep-construction pre loop pp-interval m))
                (pp-state (run-ccdfg-k (car (superstep-construction pre loop pp-interval m))
                                       (cadr (superstep-construction pre loop pp-interval m))
                                       (+ -1 k)
                                       init-state prev)))
     (:instance m
                (m k))))))

(defthm usable-invariant-holds
  (implies (and (posp k)
                (posp m)
                (posp pp-interval)
                (true-listp pre)
                (true-listp loop)
                (consp pre)
                (consp loop)
                (<= m (len pre))
                (phi-restriction-ccdfg pre)
                (phi-restriction-ccdfg loop)
                (branch-restriction-ccdfg pre)
                (branch-restriction-ccdfg loop)
                (seq-ccdfg-p (list pre loop))
                (not (equal (loop-superstep-in-parallel m pre loop pp-interval) "error"))
                (not (equal (pre-supersteps-in-parallel m pre loop pp-interval) "error"))
                (not (equal (loop-superstep-in-order m pre loop pp-interval) "error")))
           (pipeline-loop-invariant
            (run-ccdfg-k
             (pre-supersteps-in-parallel m pre loop pp-interval)
             (loop-superstep-in-parallel m pre loop pp-interval)
             k init-state prev)
            k pre loop pp-interval init-state prev m))
  :otf-flg t
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (union-theories (theory 'ground-zero)
                               '(superstep-construction
                                 branch-restriction-take-n
                                 branch-restriction-remove-n))
    :use
    ((:instance invariant-holds
                (pp-ccdfg (superstep-construction pre loop pp-interval m)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main correctness theorem
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; run-ccdfg in terms of run-ccdfg-k in pipelined ccdfg
(defthm run-ccdfg->run-k
  (implies (phi-restriction-ccdfg post)
           (equal (run-ccdfg pre loop post k init-state prev)
                  (run-block-set post
                                 (run-ccdfg-k pre loop k init-state prev)
                                 nil
                                 prev)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(run-ccdfg
                                 run-ccdfg-k))
    :use
    ((:instance phi-restriction-block-set
                (c post)
                (i (run-blocks-iters loop (run-block-set pre
                                                         init-state nil prev)
                                     k
                                     (prefix (car (last (cadar (last loop)))))))
                (next nil)
                (pre1 (prefix (car (last (cadar (last post))))))
                (pre2 prev))))))

(defun induction-hint-post (m pp-interval init-state loop prev)
  (if (or (not (posp m))
          (not (posp pp-interval))
          (< m pp-interval)) (list m pp-interval init-state loop prev)
    (induction-hint-post (- m pp-interval) pp-interval
                         (run-block-set loop init-state nil prev)
                         loop prev)))

(defthm branch-restriction-post-from-loop
  (implies (branch-restriction-ccdfg loop)
           (branch-restriction-ccdfg (post-superstep-in-order x loop pp-interval))))

(defthm run-post-subgoal
  (implies (and (posp m)
                (posp pp-interval)
                (branch-restriction-ccdfg loop)
                (not (equal (post-superstep-in-order m loop pp-interval) "error")))
           (equal (run-block-set (post-superstep-in-order m loop pp-interval)
                                 (run-block-set (get-m-blocks-seq m loop pp-interval)
                                                init-state
                                                nil
                                                prev)
                                 nil prev)
                  (run-blocks-iters loop init-state (ceiling m pp-interval) prev)))
  :otf-flg t
  :hints
  (("Goal"
    :in-theory (union-theories
                (set-difference-theories (theory 'ground-zero)
                                         (list 'ceiling))
                (list 'induction-hint-post
                      'post-superstep-in-order
                      'get-m-blocks-seq
                      'run-block-set-from-iters
                      'run-block-set-nil
                      'run-block-set-remove-take-n
                      'ceiling-same
                      'get-m-block-seq-equal-pre-superstep
                      'run-block-set-append
                      'branch-restriction-remove-n
                      'branch-restriction-take-n
                      'branch-restriction-combine-iters
                      'branch-restriction-get-m-seq
                      'branch-restriction-post-from-loop))
    :induct (induction-hint-post m pp-interval init-state loop prev)
    :do-not-induct t
    :do-not '(eliminate-destructors fertilize generalize))
   ("Subgoal *1/2.2"
    :use
    ((:instance run-block-set-no-conflict
                (a (remove-n m loop))
                (b (get-m-blocks-seq (- m pp-interval) loop pp-interval))
                (init-state (run-block-set (take-n m loop) init-state nil prev)))
     (:instance run-block-iters-from-set
                (c loop))
     (:instance run-block-iters-add
                (c loop)
                (m 1)
                (k (ceiling (- m pp-interval) pp-interval))
                (i init-state))
     (:instance ceiling-+)
     (:instance ceiling-m-pp-interval-add)))
   ("Subgoal *1/1''"
    :use
    ((:instance ceiling-m-pp-interval)
     (:instance (:definition post-superstep-in-order))
     (:instance (:definition get-m-blocks-seq))))))

;; pp-ccdfg is the pipelined ccdfg created by superstep-construction
;; pp-state is state after running pp-ccdfg for pre + k iterations
;; invariant is true which means pp-state is equal to executing seq-ccdfg's pre + (- k 1) iterations + sequence of m

(defthm invariant-implies-correctness
  (implies (and (posp k)
                (seq-ccdfg-p (list pre loop)) ;; needed to say cdr of pre = cdr of loop
                (posp pp-interval)
                (posp m)
                (true-listp pre)
                (true-listp loop)
                (consp pre)
                (consp loop)
                (<= m (len pre))
                (branch-restriction-ccdfg pre)
                (branch-restriction-ccdfg loop)
                (phi-restriction-ccdfg pre)
                (phi-restriction-ccdfg loop)
                (not (equal (pre-supersteps-in-parallel m pre loop pp-interval) "error"))
                (not (equal (post-superstep-in-order m loop pp-interval) "error"))
                (not (equal (loop-superstep-in-order m pre loop pp-interval) "error"))
                (not (equal (loop-superstep-in-parallel m pre loop pp-interval) "error"))
                (not (equal (post-superstep-in-parallel m loop pp-interval) "error"))
                (equal pp-ccdfg (superstep-construction pre loop pp-interval m)))
           (equal (run-ccdfg (car pp-ccdfg) (second pp-ccdfg) (third pp-ccdfg) k init-state prev)
                  (run-ccdfg pre loop nil (+ (+ -1 k) (ceiling m pp-interval)) init-state prev)))
  :hints
  (("Goal"
    :do-not '(preprocess)
    :in-theory (union-theories
                (set-difference-theories (theory 'ground-zero)
                                         (list 'ceiling))
                (list 'superstep-construction
                      'run-ccdfg
                      'run-post-subgoal
                      'ceiling-m-pp-interval
                      'run-block-set-nil
                      'run-block-set-remove-take-n
                      'run-block-iters-reverse-append
                      'get-m-block-seq-equal-pre-superstep
                      'run-block-set-append
                      'run-block-iters-add
                      'pre-parallel-order-same
                      'post-parallel-order-same
                      'loop-parallel-order-same
                      'ceiling-natp
                      'phi-restriction-loop-superstep-in-order
                      'phi-restriction-loop-superstep-from-loop
                      'phi-restriction-loop-superstep-in-parallel
                      'phi-restriction-post-superstep-in-parallel
                      'branch-restriction-remove-n
                      'branch-restriction-take-n
                      'branch-restriction-combine-iters
                      'branch-restriction-get-m-seq
                      'branch-restriction-post-from-loop
                      'branch-restriction-pre-from-loop
                      'branch-restriction-loop-from-loop))
    :do-not-induct t
    :use
    ((:instance usable-invariant-holds)
     (:instance run-ccdfg->run-k
                (pre (pre-supersteps-in-parallel m pre loop pp-interval))
                (loop (loop-superstep-in-parallel m pre loop pp-interval))
                (post (post-superstep-in-parallel m loop pp-interval)))
     (:instance pipeline-loop-invariant
                (pp-state (run-ccdfg-k (pre-supersteps-in-parallel m pre loop pp-interval)
                                       (loop-superstep-in-parallel m pre loop pp-interval)
                                       k init-state prev)))
     (:instance phi-restriction-block-iters
                (c loop)
                (i (run-block-set pre init-state nil prev))
                (iter (+ -1 k (ceiling m pp-interval)))
                (pre1 (prefix (car (last (cadar (last loop))))))
                (pre2 prev))))))#|ACL2s-ToDo-Line|#
