; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The raw-Lisp part of the graph benchmarks. Loaded by benchmark.lsp;
; see the usage comment there. This file is read by the Common Lisp
; reader (via cl:load), not by ld, so it may define and enter its own
; package.

(defpackage "GRAPH-BENCH"
  (:use "COMMON-LISP" "BENCH")
  (:export "RUN-QUICK"
           "RUN-FULL"
           "STACK-REPORT"))

(in-package "GRAPH-BENCH")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Graphs

;; The nodes of a benchmark graph are the integers below n. Each node has
;; edges to degree targets chosen uniformly at random, all with the label 0,
;; so a node's expected number of predecessors is also degree. A target
;; drawn twice for the same source gives a single edge.

(defparameter *degree* 4)

(defun build-graph (n degree)
  (let ((*random-state*
          (sb-ext:seed-random-state
            (bench::subseed (format nil "graph/~A/~A" n degree))))
        (g (graph::empty)))
    (dotimes (node n)
      (setq g (graph::add-node node g)))
    (dotimes (from n g)
      (dotimes (i degree)
        (setq g (graph::add-edge! from (random n) 0 g))))))

(defvar *graphs* (make-hash-table :test #'equal))

(defun graph-of (n degree)
  "The benchmark graph with n nodes and the given out-degree, built once
   and cached."
  (let ((key (list n degree)))
    (or (gethash key *graphs*)
        (progn
          (format t "; building graph: ~:D nodes, out-degree ~D~%" n degree)
          (finish-output)
          (setf (gethash key *graphs*) (build-graph n degree))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Node sets

(defun all-nodes (n)
  (tset::from-list (loop for node below n collect node)))

(defun random-nodes (n k)
  "A list of min(k, n) distinct nodes below n, drawn with the current
   random state."
  (let ((seen (make-hash-table))
        (acc nil))
    (loop while (< (hash-table-count seen) (min k n))
          do (let ((node (random n)))
               (unless (gethash node seen)
                 (setf (gethash node seen) t)
                 (push node acc))))
    acc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Specs

;; Each timed spec cycles through this many inputs.
(defparameter *inputs-per-spec* 16)

;; The size of the small node sets given to predecessors-of-set and
;; successors-of-set.
(defparameter *set-size* 16)

(defun degree-class ()
  (format nil "deg~D" *degree*))

(defun size-specs (n)
  "Timed specs on the n-node benchmark graph."
  (let ((g (graph-of n *degree*))
        (k *set-size*))
    (list
      (spec "predecessors" (degree-class) n
            (lambda ()
              (corpus (format nil "nodes/~A" n)
                      *inputs-per-spec*
                      (lambda () (random n))))
            (lambda (node) (graph::predecessors node g)))
      (spec "predecessors-of-set" (format nil "~A/k~D" (degree-class) k) n
            (lambda ()
              (corpus (format nil "node-sets/~A/~A" n k)
                      *inputs-per-spec*
                      (lambda () (tset::from-list (random-nodes n k)))))
            (lambda (set) (graph::predecessors-of-set set g)))
      (spec "successors-of-set" (format nil "~A/k~D" (degree-class) k) n
            (lambda ()
              (corpus (format nil "node-sets/~A/~A" n k)
                      *inputs-per-spec*
                      (lambda () (tset::from-list (random-nodes n k)))))
            (lambda (set) (graph::successors-of-set set g)))
      (spec "successors-of-set" (format nil "~A/all" (degree-class)) n
            (lambda () (vector (all-nodes n)))
            (lambda (set) (graph::successors-of-set set g)))
      (spec "transpose" (degree-class) n
            (lambda () (vector g))
            (lambda (graph) (graph::transpose graph))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Stack report

(defun try-op (thunk)
  "Run thunk, returning :ok, or :exhausted if it exhausts the control
   stack."
  (handler-case (progn (funcall thunk) :ok)
    (storage-condition () :exhausted)))

;; Each operation whose recursion depth grows with the graph, as a function
;; of the graph and its node count. predecessors-of-set is left out: it
;; recurses as deeply as predecessors, once per element of its set.
(defparameter *stack-ops*
  (list (cons "predecessors"
              (lambda (g n) (declare (ignore n)) (graph::predecessors 0 g)))
        (cons "successors-of-set/all"
              (lambda (g n) (graph::successors-of-set (all-nodes n) g)))
        (cons "transpose"
              (lambda (g n) (declare (ignore n)) (graph::transpose g)))))

(defun stack-report (&key (degree 1) (start 1024) (limit (expt 2 23)))
  "For each operation in *stack-ops*, the least node count, doubling from
   start up to limit, at which the operation exhausts the control stack on
   a graph of the given out-degree."
  (format t "~&Stack report (out-degree ~D, sizes doubling from ~:D to ~:D)~%"
          degree start limit)
  (finish-output)
  (let ((pending *stack-ops*)
        (found nil))
    (loop for n = start then (* 2 n)
          while (and pending (<= n limit))
          do (let ((g (build-graph n degree))
                   (still nil)
                   (exhausted nil))
               (dolist (op pending)
                 (if (eq (try-op (lambda () (funcall (cdr op) g n)))
                         :exhausted)
                     (progn (push (cons (car op) n) found)
                            (push (car op) exhausted))
                   (push op still)))
               (setq pending (reverse still))
               (format t "; ~:D nodes: ~:[all ok~;exhausted: ~:*~{~A~^, ~}~]~%"
                       n (reverse exhausted))
               (finish-output)))
    (dolist (entry (reverse found))
      (format t "  ~24A exhausts the stack at ~:D nodes~%"
              (car entry) (cdr entry)))
    (dolist (op pending)
      (format t "  ~24A no exhaustion up to ~:D nodes~%" (car op) limit))
    (values)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Suites

(defun samples-for (n samples)
  "Fewer samples for the largest graphs, where one call takes seconds."
  (if (>= n 1000000)
      (min samples 5)
    samples))

(defun run-suite (&key (seed 1)
                       (sizes '(1000 10000 100000 1000000))
                       (samples *samples*)
                       (warmup *warmup*)
                       (gc :per-round)
                       (stack t)
                       (out nil)
                       notes)
  (init-random seed)
  (clear-results)
  ;; One size at a time, so that only one large graph is live at once.
  (dolist (n sizes)
    (run-specs (size-specs n)
               :samples (samples-for n samples)
               :warmup (min warmup (samples-for n samples))
               :gc gc)
    (clrhash *graphs*))
  (print-results)
  (when out
    (let ((path (write-results out :notes notes)))
      (format t "~&Results written to ~A~%" path)))
  (when stack
    (stack-report))
  (values))

(defun run-quick ()
  "Small sizes and few samples; a smoke test, not a measurement."
  (let ((bench::*samples* 5)
        (bench::*warmup* 1)
        (bench::*target-region-ms* 5))
    (run-suite :sizes '(1000 10000)
               :stack nil)))

(defun run-full ()
  (let ((stamp (substitute #\- #\: (bench::timestamp))))
    (run-suite :out (format nil "results/graph-bench-~A.csv" stamp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(format t "~&; Running quick smoke suite; use (graph-bench::run-full) ~
           for the real thing.~%")
(run-quick)
