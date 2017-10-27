#||

general-theorems.lisp
~~~~~~~~~~~~~~~~~~~~~~
Author: Disha Puri
Last Updated: 12th April 2014

This file the general theorems about syntax and semantics
to be used in other files.

||#

(in-package "ACL2")
(include-book "semantics")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Theorems when there is no phi-statement in the CCDFG
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm phi-restriction-next-block
  (implies (phi-restriction-list l)
           (phi-restriction-list (next-to-execute l a))))

(defthm phi-restriction-run-lists
  (implies (phi-restriction-list l)
           (equal (run-lists l i next pre1)
                  (run-lists l i next pre2)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(phi-restriction-list
                                 run-lists
                                 execute-statement
                                 phi-restriction-next-block)))))

;; if no phi-step then previous scheduling step does not matter in execution
(defthm phi-restriction-run-block
  (implies (phi-restriction-block b)
           (equal (run-block b i next pre1)
                  (run-block b i next pre2)))
  :otf-flg t
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(run-block
                                 phi-restriction-block))
    :induct t
    :do-not-induct t)
   ("Subgoal *1/2''"
    :use
    ((:instance phi-restriction-run-lists
                (l (car b)))
     (:instance (:definition run-block)
                (init-state i)
                (prev pre2))))))

(defthm phi-restriction-block-set
  (implies (phi-restriction-ccdfg c)
           (equal (run-block-set c i next pre1)
                  (run-block-set c i next pre2)))
  :otf-flg t
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(phi-restriction-ccdfg
                                 run-block-set))
    :do-not '(eliminate-destructors fertilize generalize)
    :induct (run-block-set c i next pre1)
    :do-not-induct t)
   ("Subgoal *1/2''"
    :use
    ((:instance (:definition run-block-set)
                (init-state i)
                (next-bb next)
                (prev pre2))
     (:instance phi-restriction-run-block
                (b (cadar c)))))))

(in-theory (disable phi-restriction-block-set))

(defthm phi-restriction-block-iters
  (implies (phi-restriction-ccdfg c)
           (equal (run-blocks-iters c i iter pre1)
                  (run-blocks-iters c i iter pre2)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(run-blocks-iters)))
   ("Subgoal *1/2'"
    :use
    ((:instance (:definition run-blocks-iters)
                (init-state i)
                (prev pre2))
     (:instance phi-restriction-block-set
                (next nil))))))

(in-theory (disable phi-restriction-block-iters))

(defthm phi-restriction-append-reverse
  (implies (and (phi-restriction-ccdfg a)
                (phi-restriction-ccdfg b))
           (phi-restriction-ccdfg (append a b))))

(defthm phi-restriction-remove-n
  (implies (phi-restriction-ccdfg a)
           (phi-restriction-ccdfg (remove-n x a))))

(defthm phi-restriction-take-n
  (implies (phi-restriction-ccdfg a)
           (phi-restriction-ccdfg (take-n x a))))

(defthm phi-restriction-cdr
  (implies (phi-restriction-ccdfg a)
           (phi-restriction-ccdfg (cdr a))))

(defthm phi-restriction-nil
  (phi-restriction-ccdfg nil))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Theorems when there are no branch statements in the CCDFG
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm branch-restriction-list-get-next-block
  (implies (branch-restriction-list b)
           (equal (get-next-lists b i) nil))
  :hints
  (("Goal"
    :in-theory (disable branch-statement-p)
    :induct t
    :do-not-induct t)))

(defthm branch-restriction-block-get-next-block
  (implies (branch-restriction-block b)
           (equal (get-next-block b i) nil))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(branch-restriction-block
                                 branch-restriction-list-get-next-block
                                 get-next-block)))))

(defthm branch-restriction-ccdfg-cdr
  (implies (branch-restriction-ccdfg c)
           (branch-restriction-ccdfg (cdr c))))

(defthm branch-restriction-ccdfg-car
  (implies (branch-restriction-ccdfg c)
           (branch-restriction-ccdfg (list (car c)))))

(defthm branch-restriction-remove-n
  (implies (branch-restriction-ccdfg a)
           (branch-restriction-ccdfg (remove-n x a))))

(defthm branch-restriction-take-n
  (implies (branch-restriction-ccdfg a)
           (branch-restriction-ccdfg (take-n x a))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Trivial theorems
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm take-n-1
  (implies (consp pre)
           (equal (take-n 1 pre)
                  (list (car pre)))))

(defthm remove-n-1
  (implies (consp pre)
           (equal (remove-n 1 pre)
                  (cdr pre))))

(defthm m
  (implies (acl2-numberp m)
           (equal (+ -1 1 m) m)))

(defthm add-3
  (equal (+ a b c) (+ b c a)))

(defthm not-posp
  (implies (<= m pp-interval)
           (not (posp (- m pp-interval)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Theorems related to run-block-set
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; not proving this theorem in this script
;; The theorem says that if there are no read-write hazards and no conditional
;; branches, then executing a followed by b is same as executing b followed by a
;; not part of invariant, part of algorithm
;; we have not worked on this proof yet, as we were more focussed on proving
;; that if we can create a pipelined CCDFG with this acceptable assumption, then
;; that CCDFG follows our invariant
(defthms run-block-set-no-conflict
  (implies (and (no-conflict a b)
                (branch-restriction-ccdfg a)
                (branch-restriction-ccdfg b))
           (equal (run-block-set a (run-block-set b init-state nil prev) nil prev)
                  (run-block-set b (run-block-set a init-state nil prev) nil prev)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(run-block-set))
    :induct t
    :do-not-induct t)))

;; will prove theorem related to no-conflict later
(defthms no-conflict-extended
  (implies (no-conflict b c)
           (no-conflict c (list (list name (cadar b))))))

(defthm run-block-set-append
  (implies (and (branch-restriction-ccdfg a)
                (branch-restriction-ccdfg b))
           (equal (run-block-set (append a b) init-state nil prev)
                  (run-block-set b
                                 (run-block-set a init-state nil prev)
                                 nil
                                 prev)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(run-block-set
                                 branch-restriction-ccdfg
                                 branch-restriction-block-get-next-block))
    :induct t
    :do-not-induct t)))

(defthm run-block-set-from-iters
  (equal (run-blocks-iters c init-state 1 prev)
         (run-block-set c init-state nil prev))
  :hints
  (("Goal"
    :in-theory (theory 'ground-zero)
    :use
    ((:instance run-blocks-iters
                (iter 1))
     (:instance run-blocks-iters
                (iter 0)
                (init-state (run-block-set c init-state nil prev)))))))

(defthm not-consp-run-block-set
  (implies (not (consp c))
           (equal (run-block-set c init-state nil prev) init-state)))

(defthm run-block-set-reverse-append
  (implies (and (branch-restriction-ccdfg a)
                (branch-restriction-ccdfg b))
           (equal (run-block-set a (run-block-set b init-state nil prev)
                                 nil prev)
                  (run-block-set (append b a) init-state nil prev)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(run-block-set-append)))))

(defthm run-block->run-set
  (equal (run-block (cadr b) init-state nil prev)
         (run-block-set (list b) init-state nil prev))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(run-block-set)))))

(defthm run-block-set-cons
  (implies (and (branch-restriction-ccdfg (list a))
                (branch-restriction-ccdfg b))
           (equal (run-block-set (cons a b) init-state nil prev)
                  (run-block-set b
                                 (run-block-set (list a) init-state nil prev)
                                 nil prev))))

(defthm run-block-set-nil
  (equal (run-block-set nil init-state next prev)
         init-state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Theorems related to execution of pre and loop
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun induction-hint-run-block-set-remove-take-n (m init-state pre prev)
  (if (or (endp pre)
          (zp m)) (list m init-state pre prev)
    (induction-hint-run-block-set-remove-take-n (- m 1)
                                                (run-block-set (list (car pre))
                                                               init-state nil prev)
                                                (cdr pre)
                                                prev)))

(defthm run-block-set-remove-take-n
  (implies (and (posp m)
                (branch-restriction-ccdfg pre))
           (equal (run-block-set (remove-n m pre)
                                 (run-block-set (take-n m pre)
                                                init-state nil prev)
                                 nil prev)
                  (run-block-set pre init-state nil prev)))
  :hints
  (("Goal"
    :do-not '(preprocess generalize fertilize)
    :induct (induction-hint-run-block-set-remove-take-n m init-state pre prev)
    :do-not-induct t
    :in-theory (union-theories (theory 'ground-zero)
                               '(induction-hint-run-block-set-remove-take-n
                                 remove-n-1
                                 take-n-1
                                 branch-restriction-ccdfg-cdr
                                 branch-restriction-ccdfg-car
                                 branch-restriction-take-n
                                 branch-restriction-remove-n
                                 run-block-set-reverse-append
                                 run-block-set-nil
                                 take-n
                                 remove-n
                                 append)))))

(defthm take-return-take
  (implies (and (posp m)
                (posp pp-interval)
                (branch-restriction-ccdfg loop))
           (equal (run-block-set (take-n pp-interval (remove-n m loop))
                                 (run-block-set (take-n m loop) init-state nil prev)
                                 nil prev)
                  (run-block-set (take-n (+ m pp-interval) loop)
                                 init-state nil prev)))
  :otf-flg t
  :hints
  (("Goal"
    :do-not '(preprocess generalize fertilize)
    :induct (induction-hint-run-block-set-remove-take-n m init-state loop prev)
    :do-not-induct t
    :in-theory (union-theories (theory 'ground-zero)
                               '(induction-hint-run-block-set-remove-take-n
                                 remove-n-1
                                 take-n-1
                                 branch-restriction-take-n
                                 branch-restriction-remove-n
                                 branch-restriction-ccdfg-cdr
                                 branch-restriction-ccdfg-car
                                 run-block-set-reverse-append
                                 take-n
                                 append
                                 run-block-set-nil
                                 remove-n)))
   ("Subgoal *1/2.3''"
    :use
    ((:instance (:definition take-n)
                (n (+ 1 pp-interval))
                (l loop))
     (:instance m
                (m pp-interval))))
   ("Subgoal *1/2.1'"
    :use
    ((:instance (:definition take-n)
                (n (+ m pp-interval))
                (l loop))
     (:instance add-3
                (a pp-interval)
                (b -1)
                (c m))))))

(defthm append-three
  (equal (append (append a b) c) (append a (append b c))))

(defthm run-block-iters-from-set
  (equal (run-block-set c init-state nil prev)
         (run-blocks-iters c init-state 1 prev))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(run-block-set-from-iters)))))

(defthm k
  (equal (+ 1 -1 k) (+ -1 1 k)))

(defthm run-block-iters-append-subgoal
  (implies (and (natp k)
                (natp m))
           (equal (run-blocks-iters c i (+ m k) prev)
                  (run-blocks-iters c (run-blocks-iters c i k prev)
                                    m prev)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(run-blocks-iters
                                 run-block-iters-from-set)))
   ("Subgoal *1/3'"
    :use
    ((:instance (:definition run-blocks-iters)
                (init-state i)
                (iter (+ 1 m)))
     (:instance m)))))

(defthm run-block-iters-append
  (implies (natp k)
           (equal (run-blocks-iters c i (+ 1 k) prev)
                  (run-block-set c (run-blocks-iters c i k prev)
                                 nil prev)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(run-block-iters-append-subgoal
                                 run-block-set-from-iters)))))

(defthm run-block-iters-add
  (implies (and (natp m)
                (natp k))
           (equal (run-blocks-iters c (run-blocks-iters c i m prev) k prev)
                  (run-blocks-iters c i (+ k m) prev)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(run-block-iters-append-subgoal)))))

;; you need this notion that apart from first block, pre and loop are same
;; true by assumption
(defthm pre-loop-cdr-same
  (implies (and (posp m)
                (consp pre)
                (consp loop)
                (seq-ccdfg-p (list pre loop)))
           (equal (remove-n m pre)
                  (remove-n m loop)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(seq-ccdfg-p
                                 remove-n)))))

(defthm run-block-iters-reverse-append
  (implies (posp k)
           (equal  (run-block-set c (run-blocks-iters c i (+ -1 k) prev)
                                  nil prev)
                   (run-blocks-iters c i (+ -1 1 k) prev)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(k))
    :use
    ((:instance run-block-iters-append
                (k (- k 1)))))))

(defthm take-n-plus-interval
  (implies (and (posp m)
                (posp pp-interval)
                (branch-restriction-ccdfg loop))
           (equal (run-block-set (take-n (+ m pp-interval) loop) init-state nil prev)
                  (run-block-set (take-n pp-interval (remove-n m loop))
                                 (run-block-set (take-n m loop) init-state nil prev)
                                 nil prev)))
  :hints
  (("Goal"
    :in-theory (union-theories (theory 'ground-zero)
                               '(take-return-take
                                 branch-restriction-ccdfg-cdr
                                 branch-restriction-take-n
                                 branch-restriction-remove-n)))))
