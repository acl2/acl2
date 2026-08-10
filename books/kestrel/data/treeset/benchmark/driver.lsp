; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The raw-Lisp part of the treeset benchmarks. Loaded by benchmark.lsp;
; see the usage comment there. This file is read by the Common Lisp
; reader (via cl:load), not by ld, so it may define and enter its own
; package.

(defpackage "TREESET-BENCH"
  (:use "COMMON-LISP" "BENCH")
  (:export "RUN-QUICK"
           "RUN-FULL"
           "DEPTH-REPORT"
           "HASH-SHARE-REPORT"))

(in-package "TREESET-BENCH")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Input generation. All randomness goes through bench's keyed corpora,
;; so every structure of a given cardinality is built from the identical
;; key vector and every competing lookup spec sees the identical probe
;; stream.

(defun random-u60 ()
  (random (expt 2 60)))

(defparameter *probes-per-spec* 4096)
(defparameter *union-pairs* 8)

(defun keys-vector (n)
  ;; Random u60 keys; duplicates are negligible at these sizes.
  (corpus (format nil "u60-keys/~A" n) n #'random-u60))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Containers. For each cardinality, all four structures are built once
;; from the same key vector and cached.

(defvar *containers* (make-hash-table :test #'eql))

(defun containers (n)
  (or (gethash n *containers*)
      (setf (gethash n *containers*)
            (let* ((keys (keys-vector n))
                   (lst (coerce keys 'list)))
              (format t "; building cardinality-~:D containers~%" n)
              (finish-output)
              (list :keys keys
                    :treeset (treeset::from-list lst)
                    :oset (set::mergesort lst)
                    ;; The fast alist is for lookup benchmarks only;
                    ;; repeatedly re-extending one alist would break the
                    ;; fast-alist discipline, so there is no fast-alist
                    ;; insert spec.
                    :fal (let ((al nil))
                           (dolist (k lst al)
                             (setq al (acl2::hons-acons k t al))))
                    :ht (let ((ht (make-hash-table :test #'eql
                                                   :size (* 2 n))))
                          (dolist (k lst ht)
                            (setf (gethash k ht) t))))))))

(defun probes-vector (n hit-prob)
  "Probe elements for the cardinality-n key set: with probability
   hit-prob a uniformly chosen member key, otherwise a fresh random u60
   (a miss with overwhelming probability)."
  (let ((keys (getf (containers n) :keys))
        (p (float hit-prob)))
    (corpus (format nil "u60-probes/~A/~A" n hit-prob)
            *probes-per-spec*
            (lambda ()
              (if (< (random 1.0) p)
                  (svref keys (random (length keys)))
                (random-u60))))))

(defun probe-class (hit-prob)
  (format nil "p~A" hit-prob))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Specs. Structures are prebuilt; the measured operation is a single
;; lookup, insert, delete, or union. Functional operations build and
;; discard a new structure per call.

(defun in-specs (n hit-prob)
  (let* ((c (containers n))
         (tset (getf c :treeset))
         (oset (getf c :oset))
         (fal (getf c :fal))
         (ht (getf c :ht))
         (class (probe-class hit-prob))
         (setup (lambda () (probes-vector n hit-prob))))
    (list
      (spec "treeset-in" class n setup
            (lambda (x) (treeset::in x tset :test =)))
      (spec "oset-in" class n setup
            (lambda (x) (set::in x oset)))
      (spec "fast-alist-get" class n setup
            (lambda (x) (acl2::hons-get x fal)))
      (spec "hash-table-get" class n setup
            (lambda (x) (gethash x ht))))))

(defun insert-specs (n hit-prob)
  ;; The hash-table row is imperative and uses a private copy: a probe
  ;; that misses is added on the first cycle through the inputs and
  ;; overwritten thereafter, so its steady state measures
  ;; mostly-overwrite puts.
  (let* ((c (containers n))
         (tset (getf c :treeset))
         (oset (getf c :oset))
         (class (probe-class hit-prob))
         (setup (lambda () (probes-vector n hit-prob)))
         (ht-copy nil))
    (list
      (spec "treeset-insert" class n setup
            (lambda (x) (treeset::insert x tset :test =)))
      (spec "oset-insert" class n setup
            (lambda (x) (set::insert x oset)))
      (spec "hash-table-put" class n
            (lambda ()
              (let ((ht (make-hash-table :test #'eql :size (* 4 n))))
                (loop for k across (getf c :keys)
                      do (setf (gethash k ht) t))
                (setq ht-copy ht))
              (funcall setup))
            (lambda (x) (setf (gethash x ht-copy) t))))))

(defun delete-specs (n hit-prob)
  (let* ((c (containers n))
         (tset (getf c :treeset))
         (oset (getf c :oset))
         (class (probe-class hit-prob))
         (setup (lambda () (probes-vector n hit-prob))))
    (list
      (spec "treeset-delete" class n setup
            (lambda (x) (treeset::delete x tset :test =)))
      (spec "oset-delete" class n setup
            (lambda (x) (set::delete x oset))))))

(defun union-key-lists (n overlap)
  "A pair of key lists, each of length n, sharing floor(overlap*n)
   random keys. Random keys replace the old generator's consecutive
   naturals, whose blockwise key ranges made union's merge pattern
   degenerate."
  (let* ((nshared (floor (* n overlap)))
         (shared (loop repeat nshared collect (random-u60))))
    (cons (append (loop repeat (- n nshared) collect (random-u60))
                  shared)
          (append (loop repeat (- n nshared) collect (random-u60))
                  shared))))

(defun memo-setup (thunk)
  "Memoize a setup thunk so specs sharing it share one inputs vector."
  (let ((cache nil))
    (lambda ()
      (or cache (setq cache (funcall thunk))))))

(defun binary-specs (n overlap)
  ;; union, intersect, and diff, all on the same prebuilt set pairs.
  (let* ((class (format nil "overlap~A" overlap))
         (pairs (corpus (format nil "union-keys/~A/~A" n overlap)
                        *union-pairs*
                        (lambda () (union-key-lists n overlap))))
         (setup-tree
           (memo-setup
             (lambda ()
               (map 'vector
                    (lambda (p) (cons (treeset::from-list (car p))
                                      (treeset::from-list (cdr p))))
                    pairs))))
         (setup-oset
           (memo-setup
             (lambda ()
               (map 'vector
                    (lambda (p) (cons (set::mergesort (car p))
                                      (set::mergesort (cdr p))))
                    pairs)))))
    (list
      (spec "treeset-union" class n setup-tree
            (lambda (p) (treeset::union (car p) (cdr p) :test =)))
      (spec "oset-union" class n setup-oset
            (lambda (p) (set::union (car p) (cdr p))))
      (spec "treeset-intersect" class n setup-tree
            (lambda (p) (treeset::intersect (car p) (cdr p) :test =)))
      (spec "oset-intersect" class n setup-oset
            (lambda (p) (set::intersect (car p) (cdr p))))
      (spec "treeset-diff" class n setup-tree
            (lambda (p) (treeset::diff (car p) (cdr p) :test =)))
      (spec "oset-diff" class n setup-oset
            (lambda (p) (set::difference (car p) (cdr p)))))))

(defun construction-specs (n)
  ;; Whole-container construction from the same random key list.
  (let ((setup-list (lambda () (vector (coerce (keys-vector n) 'list))))
        (setup-set (lambda () (vector (getf (containers n) :treeset)))))
    (list
      (spec "treeset-from-list" "u60" n setup-list
            (lambda (l) (treeset::from-list l)))
      (spec "oset-mergesort" "u60" n setup-list
            (lambda (l) (set::mergesort l)))
      (spec "treeset-to-oset" "u60" n setup-set
            (lambda (s) (treeset::to-oset s))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Treap shape statistics (untimed). The raw treeset representation is
;; nil for the empty tree and (head . (left . right)) otherwise; the
;; walkers traverse the conses directly. Depth is O(log n) with high
;; probability, so recursion is safe.

(defun tree-max-depth (tree)
  (if (null tree)
      0
    (1+ (max (tree-max-depth (cadr tree))
             (tree-max-depth (cddr tree))))))

(defun tree-depth-sum (tree depth)
  "(values sum-of-node-depths node-count), root at depth 1."
  (if (null tree)
      (values 0 0)
    (multiple-value-bind (ls lc) (tree-depth-sum (cadr tree) (1+ depth))
      (multiple-value-bind (rs rc) (tree-depth-sum (cddr tree) (1+ depth))
        (values (+ depth ls rs)
                (+ 1 lc rc))))))

(defun depth-report (&key (cardinalities '(1000 10000 100000 1000000)))
  "Treap depth statistics for random and sequential keys, against the
   ~1.39*log2(n) expected average node depth of a random binary search
   tree. Sequential keys exercise the consecutive-integer hash stream,
   whose 32-bit collision counts looked slightly high; excess depth here
   would mean those collisions cluster enough to hurt balance."
  (format t "~&Treap depth (expected average ~~1.39*log2(n)):~%")
  (format t "  ~10@A ~12A ~10A ~10A ~12A~%"
          "n" "keys" "avg" "max" "1.39log2n")
  (dolist (n cardinalities)
    (dolist (entry
              (list (cons "random" (getf (containers n) :treeset))
                    (cons "sequential"
                          (treeset::from-list
                            (loop for i below n collect i)))))
      (multiple-value-bind (sum count) (tree-depth-sum (cdr entry) 1)
        (format t "  ~10:D ~12A ~10,2F ~10D ~12,2F~%"
                n
                (car entry)
                (float (/ sum (max 1 count)))
                (tree-max-depth (cdr entry))
                (* 1.39 (log n 2))))))
  (values))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Derived report: how much of an insert is spent hashing the element.
;; This bounds the whole-operation benefit of any faster hash function.

(defun median-of (name class size)
  (loop for row in bench:*results*
        when (and (equal (getf row :name) name)
                  (equal (getf row :class) class)
                  (eql (getf row :size) size))
          return (getf row :median-ns)))

(defun median-ns-of-op (op inputs &key (regions 7))
  "Standalone quick measurement, without a spec row: median real ns/op
   over a few calibrated regions."
  (let ((iters (bench::calibrate op inputs)))
    (bench::median
      (loop repeat regions
            collect (bench::ticks-to-ns
                      (nth-value 0 (bench::time-region op inputs iters))
                      iters)))))

(defun hash-share-report (&key (cardinalities '(1000 10000 100000 1000000))
                               (hit-prob 1/2))
  ;; treeset::hash (= hash::jenkins, benchmarked in the hash library's
  ;; own suite) is measured inline rather than as a spec row: its cost
  ;; is independent of cardinality, and only the ratio matters here.
  (let* ((class (probe-class hit-prob))
         (n0 (car (last cardinalities)))
         (h (median-ns-of-op (lambda (x) (treeset::hash x))
                             (probes-vector n0 hit-prob))))
    (format t "~&Hash share of treeset-insert (p=~A, hash ~,1Fns):~%"
            hit-prob h)
    (dolist (n cardinalities)
      (let ((i (median-of "treeset-insert" class n)))
        (when (and i (plusp i))
          (format t "  n=~10:D: insert ~8,1Fns -> hash share ~5,1F%~%"
                  n i (* 100 (/ h i))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Suites

(defun run-suite (&key (seed 1)
                       (cardinalities '(1000 10000 100000 1000000))
                       (in-probs '(0 1))
                       (mixed-prob 1/2)
                       (pair-cardinalities '(1000 10000 100000))
                       (overlaps '(0 1/2 1))
                       (construction t)
                       ;; Per-sample GC would dominate the run at this
                       ;; spec count and live-heap size; interleaving
                       ;; plus median statistics absorb the extra
                       ;; variance of per-round collection.
                       (gc :per-round)
                       (depth t)
                       (hash-share t)
                       (out nil)
                       (samples-out nil)
                       notes)
  (init-random seed)
  (clear-results)
  (clrhash *containers*)
  (run-specs
    (append
      (loop for n in cardinalities
            append (append
                     (loop for p in in-probs append (in-specs n p))
                     (insert-specs n mixed-prob)
                     (delete-specs n mixed-prob)))
      (loop for n in pair-cardinalities
            append (loop for ov in overlaps append (binary-specs n ov)))
      (and construction
           (loop for n in cardinalities append (construction-specs n))))
    :gc gc)
  (print-results)
  (when depth
    (depth-report :cardinalities cardinalities))
  (when hash-share
    (hash-share-report :cardinalities cardinalities :hit-prob mixed-prob))
  (when out
    (let ((path (write-results out :notes notes)))
      (format t "~&Results written to ~A~%" path)))
  (when samples-out
    (let ((path (write-samples samples-out :notes notes)))
      (format t "~&Raw samples written to ~A~%" path)))
  (values))

(defun run-quick ()
  "Small sizes and few samples; a smoke test, not a measurement."
  (let ((bench::*samples* 5)
        (bench::*warmup* 1)
        (bench::*target-region-ms* 5))
    (run-suite :cardinalities '(1000 10000)
               :pair-cardinalities '(1000)
               :overlaps '(1/2))))

(defun run-full ()
  (let ((stamp (substitute #\- #\: (bench::timestamp))))
    (run-suite :out (format nil "results/treeset-bench-~A.csv" stamp)
               :samples-out
               (format nil "results/treeset-bench-~A-samples.csv" stamp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(format t "~&; Running quick smoke suite; use (treeset-bench::run-full) ~
           for the real thing.~%")
(run-quick)
