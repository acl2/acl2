#||

superstep-construction.lisp
~~~~~~~~~~~~~~~~~~~~~~
Author: Disha Puri
Last Updated: 12th April 2014

This file contains the functions to create scheduling supersteps for pipelined CCDFG
from the sequential CCDFG.

sequential CCDFG = (list pre loop)
pipelined CCDFG = (list pre loop post)

||#

(in-package "ACL2")
(include-book "general-theorems")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pre superstep construction in order
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun pre-superstep-from-loop (m loop pp-interval)
  (if (or (not (posp m))
          (not (posp pp-interval))) nil
    (if (<= m pp-interval) (take-n m loop)
      (append (take-n m loop)
              (pre-superstep-from-loop (- m pp-interval) loop pp-interval)))))

(defun pre-superstep-in-order (m pre loop pp-interval)
  (if (or (not (posp m))
          (not (posp pp-interval))) nil
    (if (<= m pp-interval) (take-n m pre)
      (append (take-n m pre)
              (pre-superstep-from-loop (- m pp-interval) loop pp-interval)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pre superstep construction in parallel
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun pre-supersteps-from-loop-in-parallel (new-ccdfg m loop pp-interval n)
  (if (or (not (posp m))
          (not (posp pp-interval))) nil
    (if (<= m pp-interval)
        (combine-iters new-ccdfg (take-n m loop) (* n pp-interval))
      (pre-supersteps-from-loop-in-parallel (combine-iters new-ccdfg (take-n m loop) (* n pp-interval))
                                            (- m pp-interval)
                                            loop
                                            pp-interval
                                            (+ n 1)))))

(defun pre-supersteps-in-parallel (m pre loop pp-interval)
  (if (or (not (posp m))
          (not (posp pp-interval))) nil
    (if (<= m pp-interval) (take-n m pre)
      (pre-supersteps-from-loop-in-parallel (take-n m pre)
                                            (- m pp-interval)
                                            loop pp-interval 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Loop superstep construction in order
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun loop-superstep-from-loop (m loop pp-interval)
  (if (or (not (posp m))
          (not (posp pp-interval))) nil
    (if (<= m pp-interval) (append (take-n pp-interval (remove-n m loop))
                                   (take-n m loop))
      (if (equal (loop-superstep-from-loop (- m pp-interval) loop pp-interval) "error") "error"
        (if (no-conflict (take-n pp-interval (remove-n m loop))
                         (pre-superstep-from-loop (- m pp-interval) loop pp-interval))
            (append (take-n pp-interval (remove-n m loop))
                    (loop-superstep-from-loop (- m pp-interval) loop pp-interval))
          "error")))))

(defun loop-superstep-in-order (m pre loop pp-interval)
  (if (or (not (posp m))
          (not (posp pp-interval))) nil
    (if (<= m pp-interval) (append (remove-n m pre)
                                   (take-n m loop))
      (if (equal (loop-superstep-from-loop (- m pp-interval) loop pp-interval) "error") "error"
        (if (no-conflict (remove-n m pre) (pre-superstep-from-loop
                                           (- m pp-interval) loop pp-interval))
            (append (remove-n m pre)
                    (loop-superstep-from-loop (- m pp-interval) loop pp-interval))
          "error")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; loop superstep construction in parallel
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun loop-superstep-from-loop-in-parallel (new-ccdfg m loop pp-interval pos)
  (if (or (not (posp m))
          (not (posp pp-interval))) nil
    (if (<= m pp-interval) (combine-iters (combine-iters new-ccdfg (take-n pp-interval (remove-n m loop)) pos)
                                          (take-n m loop)
                                          pos)
      (if (no-conflict (take-n pp-interval (remove-n m loop))
                       (pre-superstep-from-loop (- m pp-interval) loop pp-interval))
          (loop-superstep-from-loop-in-parallel
           (combine-iters new-ccdfg (take-n pp-interval (remove-n m loop)) pos)
           (- m pp-interval)
           loop
           pp-interval
           pos)
        "error"))))

(defun loop-superstep-in-parallel (m pre loop pp-interval)
  (if (or (not (posp m))
          (not (posp pp-interval))) nil
    (if (<= m pp-interval) (combine-iters (remove-n m pre) (take-n m loop) 0)
      (if (no-conflict (remove-n m pre) (pre-superstep-from-loop
                                         (- m pp-interval) loop pp-interval))
          (loop-superstep-from-loop-in-parallel (remove-n m pre)
                                                (- m pp-interval)
                                                loop
                                                pp-interval
                                                0)
        "error"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; post superstep construction in order
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun post-superstep-in-order (m loop pp-interval)
  (if (or (not (posp m))
          (not (posp pp-interval))) nil
    (if (<= m pp-interval) (remove-n m loop)
      (if (equal (post-superstep-in-order (- m pp-interval) loop pp-interval) "error") "error"
        (if (no-conflict (remove-n m loop) (pre-superstep-from-loop (- m pp-interval)
                                                                    loop pp-interval))
            (append (remove-n m loop)
                    (post-superstep-in-order (- m pp-interval) loop pp-interval))
          "error")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; post superstep construction-in-parallel
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun post-superstep-sub (new-ccdfg m loop pp-interval)
  (if (or (not (posp m))
          (not (posp pp-interval))) nil
    (if (<= m pp-interval) (combine-iters new-ccdfg (remove-n m loop) 0)
      (if (no-conflict (remove-n m loop)
                       (pre-superstep-from-loop (- m pp-interval)
                                                loop pp-interval))
          (post-superstep-sub (combine-iters new-ccdfg (remove-n m loop) 0)
                              (- m pp-interval)
                              loop
                              pp-interval)
        "error"))))

(defun post-superstep-in-parallel (m loop pp-interval)
  (if (or (not (posp m))
          (not (posp pp-interval))) nil
    (if (<= m pp-interval) (remove-n m loop)
      (post-superstep-sub (remove-n m loop) (- m pp-interval) loop pp-interval))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; superstep construction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun superstep-construction (pre loop interval m)
  (list (pre-supersteps-in-parallel m pre loop interval)
        (loop-superstep-in-parallel m pre loop interval)
        (post-superstep-in-parallel m loop interval)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Theorems about error
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm loop-superstep-error
  (implies (and (posp m)
                (posp pp-interval)
                (equal (loop-superstep-from-loop (- m pp-interval) loop pp-interval) "error"))
           (equal (loop-superstep-from-loop m loop pp-interval) "error")))

(defthm error-loop
  (implies (and (posp m)
                (posp pp-interval)
                (not (equal (loop-superstep-in-order m pre loop pp-interval) "error")))
           (not (equal (loop-superstep-from-loop (- m pp-interval) loop pp-interval) "error"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Theorems related to branch restriction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm branch-restriction-extended
  (implies (and (branch-restriction-ccdfg b)
                (branch-restriction-ccdfg c))
           (branch-restriction-ccdfg (cons (list (car (nth pos c))
                                                 (append (cadr (nth pos c))
                                                         (cadar b)))
                                           (remove-n (+ 1 pos) c)))))

(defthm branch-restriction-extended-2
  (implies (and (branch-restriction-ccdfg b)
                (branch-restriction-ccdfg c))
           (branch-restriction-ccdfg
            (list (list (car (nth pos c))
                        (append (cadr (nth pos c)) (cadar b)))))))

(defthm branch-restriction-block-cdr
  (implies (branch-restriction-block b)
           (branch-restriction-block (cdr b))))

(defthm branch-restriction-block-extended
  (implies (and (branch-restriction-block b)
                (branch-restriction-block a))
           (not (get-next-block (cons (car a)
                                      (append (cdr a) b))
                                init-state))))

(defthm branch-restriction-error
  (branch-restriction-ccdfg "error"))


(defthm branch-restriction-append
  (implies (and (branch-restriction-ccdfg a)
                (branch-restriction-ccdfg b))
           (branch-restriction-ccdfg (append a b))))

(defthm branch-restriction-cons
  (implies (and (branch-restriction-ccdfg a)
                (branch-restriction-ccdfg b))
           (branch-restriction-ccdfg (cons (list (car (nth pos a))
                                                 (append (cadr (nth pos a))
                                                         (cadar b)))
                                           (remove-n (+ 1 pos) a)))))

(defthm branch-restriction-combine-blocks
  (implies (and (branch-restriction-ccdfg a)
                (branch-restriction-ccdfg b))
           (branch-restriction-ccdfg (combine-blocks a b pos)))
  :otf-flg t
  :hints
  (("Goal"
    :do-not '(eliminate-destructors fertilize generalize)
    :in-theory (union-theories (theory 'ground-zero)
                               '(combine-blocks
                                 branch-restriction-take-n
                                 branch-restriction-remove-n
                                 branch-restriction-error
                                 branch-restriction-append
                                 branch-restriction-cons))
    :do-not-induct t)))

(defthm branch-restriction-list-car
  (implies (branch-restriction-ccdfg a)
           (branch-restriction-ccdfg (list (car a)))))

(defthm branch-restriction-combine-iters
  (implies (and (branch-restriction-ccdfg a)
                (branch-restriction-ccdfg b))
           (branch-restriction-ccdfg (combine-iters a b pos)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(combine-iters
                                 branch-restriction-combine-blocks
                                 branch-restriction-error
                                 branch-restriction-list-car))
    :use
    ((:instance branch-restriction-combine-blocks
                (b (list (car b))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; theorems related to true-listp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm true-listp-take-n
  (implies (true-listp c)
           (true-listp (take-n m c))))

(defthm true-listp-remove-n
  (implies (true-listp c)
           (true-listp (remove-n m c)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(remove-n)))))

(defthm true-listp-cdr
  (implies (true-listp c)
           (true-listp (cdr c))))

(defthm true-listp-add
  (implies (and (true-listp  c1)
                (true-listp c2))
           (true-listp (append (take-n pos c1)
                               (cons (list (car (nth pos c1))
                                           (append (cadr (nth pos c1)) (cadar c2)))
                                     (remove-n (+ 1 pos) c1))))))

(defthm true-listp-car
  (implies (true-listp c)
           (true-listp (list (car c)))))

(defthm true-listp-combine-blocks
  (implies (and (true-listp  c1)
                (true-listp c2)
                (not (equal (combine-blocks c1 c2 pos) "error")))
           (true-listp (combine-blocks c1 c2 pos)))
  :hints
  (("Goal"
    :induct t
    :do-not-induct t
    :in-theory (union-theories (theory 'ground-zero)
                               '(combine-blocks
                                 true-listp-cdr
                                 true-listp-take-n
                                 true-listp-remove-n
                                 true-listp-add
                                 true-listp-car)))))

(defthm no-conflict-nil
  (equal (no-conflict '(nil) a) t)
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(no-conflict
                                 not-in
                                 all-write
                                 all-read
                                 get-msteps
                                 get-msteps-blocks
                                 append)))))

(defthm blocks-iters-error
  (implies (not (equal (combine-iters a b pos) "error"))
           (not (equal (combine-blocks a (list (car b)) pos) "error")))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(combine-iters
                                 combine-blocks
                                 no-conflict-nil)))))

(defthm true-listp-combine-iters
  (implies (and (true-listp  c1)
                (true-listp c2)
                (not (equal (combine-iters c1 c2 pos) "error")))
           (true-listp (combine-iters c1 c2 pos)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(combine-iters
                                 true-listp-combine-blocks
                                 true-listp-cdr
                                 true-listp-take-n
                                 true-listp-remove-n
                                 true-listp-car
                                 blocks-iters-error))
    :use
    ((:instance true-listp-combine-blocks
                (c2 (list (car c2))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Prove iterations in order is same as combine-iters in parallel
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm run-block-set-not-consp
  (equal (run-block-set '(nil) init-state nil prev)
         init-state)
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(run-block-set
                                 run-block)))))

(defthm run-block-append
  (implies (and (branch-restriction-block a)
                (branch-restriction-block b))
           (equal (run-block (append a b)
                             init-state nil prev)
                  (run-block b
                             (run-block a init-state nil prev)
                             nil prev)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(run-block
                                 branch-restriction-block-cdr
                                 branch-restriction-block-get-next-block
                                 branch-restriction-block-extended)))))

(defthm branch-restriction-extended-3
  (implies (and (branch-restriction-ccdfg c)
                (branch-restriction-ccdfg b))
           (branch-restriction-ccdfg (list (list (car (nth pos c))
                                                 (append (cadr (nth pos c))
                                                         (cadar b)))))))


(defthm run-block-set-append-block
  (implies (and (branch-restriction-block a)
                (branch-restriction-block b))
           (equal (run-block-set (list (list name (append a b))) init-state nil prev)
                  (run-block-set (list (list name b))
                                 (run-block-set (list (list name a))
                                                init-state nil prev)
                                 nil prev)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(run-block-set
                                 run-block-append))
    :do-not-induct t)))

(defthm branch-restriction-block-nil
  (branch-restriction-block nil))

(defthm branch-restriction-block-nth
  (implies (branch-restriction-ccdfg c)
           (branch-restriction-block (cadr (nth pos c)))))

(defthm branch-restriction-block-cadar
  (implies (branch-restriction-ccdfg b)
           (branch-restriction-block (cadar b))))

(defthm run-block-set-pos
  (equal (run-block-set (list (list (car (nth pos c)) (cadr (nth pos c)))) init-state nil prev)
         (run-block-set (list (nth pos c)) init-state nil prev))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(run-block-set)))))

(defthm branch-restriction-nth
  (implies (branch-restriction-ccdfg c)
           (branch-restriction-ccdfg (list (nth pos c)))))

(include-book "arithmetic-5/top" :dir :system)

(defthm mstep-consp
  (implies (mstep-p x)
           (consp x)))

(include-book "arithmetic/top-with-meta" :dir :system)

(defthm nth-remove
  (implies (and (< (+ i n) (len l))
                (natp i)
                (natp n))
           (equal (nth i (remove-n n l))
                  (nth (+ i n) l))))

(defthm nth-remove-2
  (implies (and (>= (+ i n) (len l))
                (natp i)
                (natp n))
           (equal (nth i (remove-n n l)) nil))
  :hints (("Goal"
           :induct (remove-n n l))))

(defthm nth-remove-3
  (implies (and (>= m (len l))
                (natp m))
           (equal (nth m l) nil)))

(defthm nth-remove-summarized
  (implies (and (natp i)
                (natp n))
           (equal (nth i (remove-n n l))
                  (nth (+ i n) l)))
  :hints (("Goal"
           :cases ((>= (+ i n) (len l))))))

(defthm nth-append
  (implies (natp i)
           (equal (nth i (append x y))
                  (if (< i (len x))
                      (nth i x)
                    (nth (- i (len x)) y)))))

(defthm nth-take
  (implies (and (natp i)
                (natp n))
           (equal (nth i (take-n n l))
                  (if (< i n)
                      (nth i l)
                    nil))))

(defthm nth-desired
  (implies (and (natp pos)
                (natp i))
           (equal (nth i (append (take-n pos c)
                                 (list (nth pos c))
                                 (remove-n (+ 1 pos) c)))
                  (nth i c))))

(defthm nth-car
  (implies (true-listp c)
           (equal (nth 0 c) (car c))))

(defun induction-hint-nth (i c d)
  (if (zp i) (list i c d)
    (induction-hint-nth (- i 1) (cdr c) (cdr d))))

(defthm nth-list-car
  (implies (and (zp i)
                (true-listp c)
                (true-listp d)
                (equal (nth i c) (nth i d)))
           (equal (car c) (car d))))

(defthm pos-add
  (equal (+ -1 1 pos) (+ 1 -1 pos)))

;; working on the proof
;; would use "nth-desired"
(defthms append-ccdfg
  (implies (and (natp pos)
                (true-listp c))
           (equal (append (append (take-n pos c)
                                  (list (nth pos c)))
                          (remove-n (+ 1 pos) c))
                  c)))

(defthm run-block-set-combined
  (implies (and (branch-restriction-ccdfg c)
                (true-listp c)
                (natp pos))
           (equal (run-block-set (remove-n (+ 1 pos) c)
                                 (run-block-set (list (list (car (nth pos c))
                                                            (cadr (nth pos c))))
                                                (run-block-set (take-n pos c)
                                                               init-state nil prev)
                                                nil prev)
                                 nil prev)
                  (run-block-set c init-state nil prev)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(run-block-set-pos
                                 run-block-set-reverse-append
                                 branch-restriction-take-n
                                 branch-restriction-remove-n
                                 branch-restriction-nth
                                 branch-restriction-append))
    :do-not-induct t
    :use
    ((:instance append-ccdfg)))))

(defthm run-block-nil
  (equal (run-block nil init-state next-bb prev)
         init-state)
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(run-block)))))

(defthm branch-restriction-extended-4
  (implies (and (branch-restriction-ccdfg c)
                (branch-restriction-ccdfg b))
           (branch-restriction-ccdfg (list (list (car (nth pos c))
                                                 (cadar b))))))

(defthm block-in-parallel
  (implies (and (branch-restriction-ccdfg c)
                (branch-restriction-ccdfg b)
                (true-listp c)
                (true-listp d)
                (not (cdr b))
                (natp pos)
                (not (equal (combine-blocks c b pos) "error")))
           (equal (run-block-set (combine-blocks c b pos) init-state nil prev)
                  (run-block-set b
                                 (run-block-set c init-state nil prev)
                                 nil prev)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(combine-blocks
                                 run-block-set-combined
                                 run-block-set-cons
                                 run-block-set-append
                                 branch-restriction-take-n
                                 branch-restriction-remove-n
                                 branch-restriction-cons
                                 branch-restriction-list-car
                                 branch-restriction-extended-3
                                 branch-restriction-extended-4
                                 branch-restriction-block-nil
                                 branch-restriction-block-nth
                                 branch-restriction-block-cadar
                                 run-block-set-nil
                                 run-block-nil
                                 no-conflict-extended))
    :use
    ((:instance run-block-set-append-block
                (name (car (nth pos c)))
                (a (cadr (nth pos c)))
                (b (cadar b))
                (init-state (run-block-set (take-n pos c) init-state nil prev)))
     (:instance run-block-set-no-conflict
                (b (list (list (car (nth pos c)) (cadar b))))
                (a (remove-n (+ 1 pos) c))
                (init-state (run-block-set (list (list (car (nth pos c))
                                                       (cadr (nth pos c))))
                                           (run-block-set (take-n pos c)
                                                          init-state nil prev)
                                           nil prev)))))
   ("Subgoal 2'"
    :use
    ((:instance run-block-set
                (c (list (list (car (nth pos c)) (cadar b))))
                (init-state (run-block-set c init-state nil prev))
                (next-bb nil))
     (:instance run-block-set
                (c b)
                (init-state (run-block-set c init-state nil prev))
                (next-bb nil))))
   ("Subgoal 1'"
    :use
    ((:instance run-block-set
                (c (list (list (car (nth pos c)) (cadar b))))
                (init-state (run-block-set c init-state nil prev))
                (next-bb nil))
     (:instance run-block-set
                (c b)
                (init-state (run-block-set c init-state nil prev))
                (next-bb nil))))))

(defthm run-block-set-not-cons
  (implies (not (consp c))
           (equal (run-block-set c init-state next-bb prev)
                  init-state)))

(defthm iter-in-parallel
  (implies (and (branch-restriction-ccdfg c1)
                (branch-restriction-ccdfg c2)
                (true-listp c1)
                (true-listp c2)
                (natp pos)
                (not (equal (combine-iters c1 c2 pos) "error")))
           (equal (run-block-set (combine-iters c1 c2 pos) init-state nil prev)
                  (run-block-set c2
                                 (run-block-set c1 init-state nil prev)
                                 nil prev)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(combine-iters
                                 run-block-set-not-cons
                                 block-in-parallel
                                 branch-restriction-list-car
                                 branch-restriction-combine-blocks
                                 blocks-iters-error
                                 true-listp-combine-blocks))
    :induct t
    :do-not-induct t)
   ("Subgoal *1/2.2'"
    :use
    ((:instance block-in-parallel
                (c c1)
                (b (list (car c2))))
     (:instance run-block-set-reverse-append
                (a (cdr c2))
                (b (list (car c2)))
                (init-state (run-block-set c1 init-state nil prev)))))
   ("Subgoal *1/2.1'"
    :use
    ((:instance block-in-parallel
                (c c1)
                (b (list (car c2))))
     (:instance run-block-set-reverse-append
                (a (cdr c2))
                (b (list (car c2)))
                (init-state (run-block-set c1 init-state nil prev)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; for pre
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm branch-restriction-pre-from-loop
  (implies (branch-restriction-ccdfg loop)
           (branch-restriction-ccdfg (pre-superstep-from-loop x loop pp-interval)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(branch-restriction-ccdfg
                                 pre-superstep-from-loop)))))

(defthm not-error-pre-loop
  (implies (and (not (equal (pre-supersteps-from-loop-in-parallel new-ccdfg m loop pp-interval pos) "error"))
                (posp m)
                (posp pp-interval))
           (not (equal (combine-iters new-ccdfg (take-n m loop) (* pos pp-interval)) "error")))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(pre-supersteps-from-loop-in-parallel
                                 combine-iters)))))

(defthm pre-parallel-order-loop-same
  (implies (and (posp m)
                (posp pp-interval)
                (natp pos)
                (branch-restriction-ccdfg loop)
                (branch-restriction-ccdfg new-ccdfg)
                (true-listp loop)
                (true-listp new-ccdfg)
                (not (equal (pre-supersteps-from-loop-in-parallel new-ccdfg m loop pp-interval pos) "error")))
           (equal (run-block-set (pre-supersteps-from-loop-in-parallel new-ccdfg m loop pp-interval pos) init-state nil prev)
                  (run-block-set (pre-superstep-from-loop m loop pp-interval)
                                 (run-block-set new-ccdfg init-state nil prev)
                                 nil prev)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(pre-supersteps-from-loop-in-parallel
                                 pre-superstep-from-loop
                                 run-block-set-nil
                                 not-error-pre-loop
                                 branch-restriction-ccdfg-cdr
                                 branch-restriction-pre-from-loop
                                 iter-in-parallel
                                 run-block-set-append
                                 branch-restriction-take-n
                                 branch-restriction-remove-n
                                 branch-restriction-combine-iters
                                 true-listp-combine-iters
                                 true-listp-take-n
                                 true-listp-remove-n
                                 true-listp-cdr))
    :induct t
    :do-not-induct t)))

(defthm pre-parallel-order-same
  (implies (and (branch-restriction-ccdfg loop)
                (branch-restriction-ccdfg pre)
                (true-listp pre)
                (true-listp loop)
                (not (equal (pre-supersteps-in-parallel m pre loop pp-interval) "error")))
           (equal (run-block-set (pre-supersteps-in-parallel m pre loop pp-interval) init-state nil prev)
                  (run-block-set (pre-superstep-in-order m pre loop pp-interval) init-state nil prev)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(pre-supersteps-in-parallel
                                 pre-superstep-in-order
                                 pre-parallel-order-loop-same
                                 run-block-set-append
                                 branch-restriction-ccdfg-cdr
                                 branch-restriction-take-n
                                 branch-restriction-remove-n
                                 branch-restriction-pre-from-loop
                                 true-listp-combine-iters
                                 true-listp-take-n
                                 true-listp-remove-n
                                 true-listp-cdr)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; for loop
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm branch-restriction-loop-from-loop
  (implies (branch-restriction-ccdfg loop)
           (branch-restriction-ccdfg (loop-superstep-from-loop x loop pp-interval)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(loop-superstep-from-loop
                                 branch-restriction-ccdfg
                                 branch-restriction-take-n
                                 branch-restriction-remove-n
                                 branch-restriction-append)))))

(defthm combine-iters-error
  (implies (not (equal (combine-iters a b pos) "error"))
           (not (equal a "error"))))

(defthm not-error-loop-loop
  (implies (and (not (equal (loop-superstep-from-loop-in-parallel new-ccdfg m loop pp-interval pos) "error"))
                (posp m)
                (posp pp-interval))
           (not (equal (combine-iters new-ccdfg (take-n pp-interval (remove-n m loop)) pos) "error")))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(loop-superstep-from-loop-in-parallel
                                 combine-iters)))))

(defthm loop-parallel-order-loop-same
  (implies (and (posp m)
                (posp pp-interval)
                (natp pos)
                (branch-restriction-ccdfg loop)
                (branch-restriction-ccdfg new-ccdfg)
                (true-listp loop)
                (true-listp new-ccdfg)
                (not (equal (loop-superstep-from-loop m loop pp-interval) "error"))
                (not (equal (loop-superstep-from-loop-in-parallel new-ccdfg m loop pp-interval pos) "error")))
           (equal (run-block-set (loop-superstep-from-loop-in-parallel new-ccdfg m loop pp-interval pos)
                                 init-state nil prev)
                  (run-block-set (loop-superstep-from-loop m loop pp-interval)
                                 (run-block-set new-ccdfg init-state nil prev)
                                 nil prev)))
  :hints
  (("Goal"
    :induct t
    :do-not-induct t
    :in-theory (union-theories (theory 'ground-zero)
                               '(loop-superstep-from-loop-in-parallel
                                 loop-superstep-from-loop
                                 error-loop
                                 not-error-loop-loop
                                 combine-iters-error
                                 iter-in-parallel
                                 branch-restriction-ccdfg-cdr
                                 branch-restriction-take-n
                                 branch-restriction-remove-n
                                 branch-restriction-combine-iters
                                 branch-restriction-loop-from-loop
                                 run-block-set-append
                                 true-listp-combine-iters
                                 true-listp-take-n
                                 true-listp-remove-n
                                 true-listp-cdr)))))

(defthm remove-n-nil
  (equal (remove-n m nil) nil))

(defthm combine-blocks-with-nil
  (equal (combine-blocks nil a 0) a))

(defthm loop-parallel-order-same
  (implies (and (branch-restriction-ccdfg pre)
                (branch-restriction-ccdfg loop)
                (true-listp pre)
                (true-listp loop)
                (not (equal (loop-superstep-in-parallel m pre loop pp-interval) "error"))
                (not (equal (loop-superstep-in-order m pre loop pp-interval) "error")))
           (equal (run-block-set (loop-superstep-in-parallel m pre loop pp-interval) init-state nil prev)
                  (run-block-set (loop-superstep-in-order m pre loop pp-interval) init-state nil prev)))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (union-theories (theory 'ground-zero)
                               '(loop-superstep-in-parallel
                                 loop-superstep-in-order
                                 iter-in-parallel
                                 branch-restriction-take-n
                                 branch-restriction-remove-n
                                 true-listp-take-n
                                 true-listp-remove-n
                                 run-block-set-append
                                 loop-parallel-order-loop-same
                                 branch-restriction-loop-from-loop)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; for post
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm branch-restriction-post-in-order
  (implies (branch-restriction-ccdfg loop)
           (branch-restriction-ccdfg (post-superstep-in-order x loop pp-interval)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(branch-restriction-ccdfg
                                 post-superstep-in-order)))))

(defthm not-error-post-loop
  (implies (and (posp m)
                (posp pp-interval)
                (not (equal (post-superstep-sub new-ccdfg m loop pp-interval) "error")))
           (not (equal (combine-iters new-ccdfg (remove-n m loop) 0) "error")))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(post-superstep-sub
                                 combine-iters)))))

(defthm post-parallel-sub-order-same
  (implies (and (posp m)
                (posp pp-interval)
                (not (equal (post-superstep-sub new-ccdfg m loop pp-interval) "error"))
                (not (equal (post-superstep-in-order m loop pp-interval) "error"))
                (branch-restriction-ccdfg loop)
                (branch-restriction-ccdfg new-ccdfg)
                (true-listp loop)
                (true-listp new-ccdfg))
           (equal (run-block-set (post-superstep-sub new-ccdfg m loop pp-interval) init-state nil prev)
                  (run-block-set (post-superstep-in-order m loop pp-interval)
                                 (run-block-set new-ccdfg init-state nil prev)
                                 nil prev)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(not-error-post-loop
                                 branch-restriction-ccdfg-cdr
                                 branch-restriction-take-n
                                 branch-restriction-remove-n
                                 branch-restriction-combine-iters
                                 branch-restriction-post-in-order
                                 post-superstep-sub
                                 post-superstep-in-order
                                 run-block-set-append
                                 iter-in-parallel
                                 true-listp-combine-iters
                                 true-listp-take-n
                                 true-listp-remove-n
                                 true-listp-cdr)))))


(defthm post-parallel-order-same
  (implies (and (posp m)
                (posp pp-interval)
                (branch-restriction-ccdfg loop)
                (true-listp loop)
                (not (equal (post-superstep-in-order m loop pp-interval) "error"))
                (not (equal (post-superstep-in-parallel m loop pp-interval) "error")))
           (equal (run-block-set (post-superstep-in-parallel m loop pp-interval) init-state nil prev)
                  (run-block-set (post-superstep-in-order m loop pp-interval) init-state nil prev)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(branch-restriction-ccdfg-cdr
                                 branch-restriction-take-n
                                 branch-restriction-remove-n
                                 branch-restriction-combine-iters
                                 branch-restriction-post-in-order
                                 post-superstep-in-parallel
                                 post-superstep-in-order
                                 post-parallel-sub-order-same
                                 run-block-set-append
                                 iter-in-parallel
                                 true-listp-combine-iters
                                 true-listp-take-n
                                 true-listp-remove-n
                                 true-listp-cdr)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Theorems related to phi-restriction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm phi-restriction-loop-superstep-from-loop
  (implies (phi-restriction-ccdfg loop)
           (phi-restriction-ccdfg (loop-superstep-from-loop m loop pp-interval)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(phi-restriction-ccdfg
                                 loop-superstep-from-loop
                                 phi-restriction-append-reverse
                                 phi-restriction-take-n
                                 phi-restriction-remove-n
                                 loop-superstep-from-loop)))))

(defthm phi-restriction-loop-superstep-in-order
  (implies (and (phi-restriction-ccdfg pre)
                (phi-restriction-ccdfg loop))
           (phi-restriction-ccdfg (loop-superstep-in-order m pre loop pp-interval)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(phi-restriction-ccdfg
                                 loop-superstep-in-order
                                 phi-restriction-append-reverse
                                 phi-restriction-take-n
                                 phi-restriction-remove-n
                                 loop-superstep-from-loop
                                 phi-restriction-loop-superstep-from-loop))
    :do-not-induct t)))

(defthm phi-restriction-cons
  (implies (and (phi-restriction-ccdfg a)
                (phi-restriction-ccdfg b))
           (phi-restriction-ccdfg (cons (list (car (nth pos a))
                                              (append (cadr (nth pos a))
                                                      (cadar b)))
                                        (remove-n (+ 1 pos) a))))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(phi-restriction-ccdfg
                                 phi-restriction-block
                                 remove-n
                                 append
                                 phi-restriction-remove-n
                                 phi-restriction-cdr)))))

(defthm phi-restriction-error
  (phi-restriction-ccdfg "error"))

(defthm phi-restriction-combine-blocks
  (implies (and (phi-restriction-ccdfg a)
                (phi-restriction-ccdfg b))
           (phi-restriction-ccdfg (combine-blocks a b pos)))
  :otf-flg t
  :hints
  (("Goal"
    :do-not '(eliminate-destructors fertilize generalize)
    :in-theory (union-theories (theory 'ground-zero)
                               '(combine-blocks
                                 phi-restriction-take-n
                                 phi-restriction-remove-n
                                 phi-restriction-error
                                 phi-restriction-append-reverse
                                 phi-restriction-cdr
                                 phi-restriction-cons))
    :do-not-induct t
    :use
    ((:instance phi-restriction-append-reverse
                (a (take-n pos a))
                (b (cons (list (car (nth pos a))
                               (append (cadr (nth pos a))
                                       (cadar b)))
                         (remove-n (+ 1 pos) a))))))))

(defthm phi-restriction-list-car
  (implies (phi-restriction-ccdfg a)
           (phi-restriction-ccdfg (list (car a)))))



(defthm phi-restriction-combine-iters
  (implies (and (phi-restriction-ccdfg a)
                (phi-restriction-ccdfg b))
           (phi-restriction-ccdfg (combine-iters a b pos)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(combine-iters
                                 phi-restriction-combine-blocks
                                 phi-restriction-cdr
                                 phi-restriction-error
                                 phi-restriction-list-car))
    :use
    ((:instance phi-restriction-combine-blocks
                (b (list (car b))))))))

(defthm phi-restriction-take-remove
  (implies (phi-restriction-ccdfg loop)
           (phi-restriction-ccdfg (take-n y (remove-n x loop)))))

(defthm phi-restriction-loop-superstep-from-loop-in-parallel
  (implies (and (phi-restriction-ccdfg pre)
                (phi-restriction-ccdfg loop))
           (phi-restriction-ccdfg (loop-superstep-from-loop-in-parallel pre x loop y n)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(loop-superstep-from-loop-in-parallel
                                 phi-restriction-nil
                                 phi-restriction-take-n
                                 phi-restriction-remove-n
                                 phi-restriction-take-remove
                                 phi-restriction-combine-iters
                                 phi-restriction-error)))))

(defthm phi-restriction-loop-superstep-in-parallel
  (implies (and (posp m)
                (phi-restriction-ccdfg pre)
                (phi-restriction-ccdfg loop))
           (phi-restriction-ccdfg (loop-superstep-in-parallel m pre loop pp-interval)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(loop-superstep-in-parallel
                                 loop-superstep-from-loop-in-parallel
                                 phi-restriction-nil
                                 phi-restriction-take-n
                                 phi-restriction-remove-n
                                 phi-restriction-combine-iters
                                 phi-restriction-error)))))

(defthm phi-restriction-post-superstep-sub
  (implies (and (phi-restriction-ccdfg loop)
                (phi-restriction-ccdfg new-ccdfg))
           (phi-restriction-ccdfg (post-superstep-sub new-ccdfg x loop pp-interval)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(post-superstep-sub
                                 phi-restriction-nil
                                 phi-restriction-take-n
                                 phi-restriction-remove-n
                                 phi-restriction-combine-iters
                                 phi-restriction-error)))))

(defthm phi-restriction-post-superstep-in-parallel
  (implies (phi-restriction-ccdfg loop)
           (phi-restriction-ccdfg (post-superstep-in-parallel m loop pp-interval)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(post-superstep-in-parallel
                                 phi-restriction-nil
                                 phi-restriction-take-n
                                 phi-restriction-remove-n
                                 phi-restriction-combine-iters
                                 phi-restriction-error
                                 phi-restriction-post-superstep-sub)))))
