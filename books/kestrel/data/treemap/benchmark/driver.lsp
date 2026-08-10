; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The raw-Lisp part of the treemap benchmarks. Loaded by benchmark.lsp;
; see the usage comment there. This file is read by the Common Lisp
; reader (via cl:load), not by ld, so it may define and enter its own
; package.

(defpackage "TREEMAP-BENCH"
  (:use "COMMON-LISP" "BENCH")
  (:export "RUN-QUICK"
           "RUN-FULL"
           "DEPTH-REPORT"
           "HASH-SHARE-REPORT"))

(in-package "TREEMAP-BENCH")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Input generation. All randomness goes through bench's keyed corpora,
;; so every structure of a given cardinality is built from the identical
;; alist and every competing lookup spec sees the identical probe
;; stream. Keys are random u60s (duplicates negligible); the value bound
;; to key k is (1+ k), so values are determined by the keys and do not
;; need their own corpus.

(defun random-u60 ()
  (random (expt 2 60)))

(defparameter *probes-per-spec* 4096)
(defparameter *merge-pairs* 8)

(defparameter *omap-quadratic-max* 10000
  "Largest cardinality at which the omap rows of the quadratic
   operations (from-alist and update*, both built from repeated O(n)
   updates) are included; above this they would dominate the whole run
   (measured: omap::from-alist already takes ~0.7s at n = 10000).")

(defun keys-vector (n)
  (corpus (format nil "u60-keys/~A" n) n #'random-u60))

(defun keys-alist (keys)
  (map 'list (lambda (k) (cons k (1+ k))) keys))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Containers. For each cardinality, all four structures are built once
;; from the same alist and cached.

(defvar *containers* (make-hash-table :test #'eql))

(defun containers (n)
  (or (gethash n *containers*)
      (setf (gethash n *containers*)
            (let* ((keys (keys-vector n))
                   (alist (keys-alist keys)))
              (format t "; building cardinality-~:D containers~%" n)
              (finish-output)
              (list :keys keys
                    :alist alist
                    :treemap (treemap::from-alist alist)
                    :omap (omap::from-alist alist)
                    ;; The fast alist is for lookup benchmarks only;
                    ;; repeatedly re-extending one alist would break the
                    ;; fast-alist discipline, so there is no fast-alist
                    ;; update spec.
                    :fal (let ((al nil))
                           (dolist (pair alist al)
                             (setq al (acl2::hons-acons (car pair)
                                                        (cdr pair)
                                                        al))))
                    :ht (let ((ht (make-hash-table :test #'eql
                                                   :size (* 2 n))))
                          (dolist (pair alist ht)
                            (setf (gethash (car pair) ht) (cdr pair))))
                    )))))

(defun probes-vector (n hit-prob)
  "Probe keys for the cardinality-n key set: with probability hit-prob a
   uniformly chosen member key, otherwise a fresh random u60 (a miss
   with overwhelming probability)."
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
;; lookup, update, delete, or a whole-map merge. Functional operations
;; build and discard a new structure per call.

(defun lookup-specs (n hit-prob)
  (let* ((c (containers n))
         (tmap (getf c :treemap))
         (omap (getf c :omap))
         (fal (getf c :fal))
         (ht (getf c :ht))
         (class (probe-class hit-prob))
         (setup (lambda () (probes-vector n hit-prob))))
    (list
      (spec "treemap-lookup" class n setup
            (lambda (x) (treemap::lookup x tmap :test =)))
      (spec "omap-lookup" class n setup
            (lambda (x) (omap::lookup x omap)))
      (spec "fast-alist-get" class n setup
            (lambda (x) (acl2::hons-get x fal)))
      (spec "hash-table-get" class n setup
            (lambda (x) (gethash x ht))))))

(defun update-specs (n hit-prob)
  ;; A hit overwrites an existing binding; a miss adds a new one. The
  ;; hash-table row is imperative and uses a private copy: a probe that
  ;; misses is added on the first cycle through the inputs and
  ;; overwritten thereafter, so its steady state measures
  ;; mostly-overwrite puts.
  (let* ((c (containers n))
         (tmap (getf c :treemap))
         (omap (getf c :omap))
         (class (probe-class hit-prob))
         (setup (lambda () (probes-vector n hit-prob)))
         (ht-copy nil))
    (list
      (spec "treemap-update" class n setup
            (lambda (x) (treemap::update x (1+ x) tmap :test =)))
      (spec "omap-update" class n setup
            (lambda (x) (omap::update x (1+ x) omap)))
      (spec "hash-table-put" class n
            (lambda ()
              (let ((ht (make-hash-table :test #'eql :size (* 4 n))))
                (dolist (pair (getf c :alist))
                  (setf (gethash (car pair) ht) (cdr pair)))
                (setq ht-copy ht))
              (funcall setup))
            (lambda (x) (setf (gethash x ht-copy) (1+ x)))))))

(defun delete-specs (n hit-prob)
  (let* ((c (containers n))
         (tmap (getf c :treemap))
         (omap (getf c :omap))
         (class (probe-class hit-prob))
         (setup (lambda () (probes-vector n hit-prob))))
    (list
      (spec "treemap-delete" class n setup
            (lambda (x) (treemap::delete x tmap :test =)))
      (spec "omap-delete" class n setup
            (lambda (x) (omap::delete x omap))))))

(defun merge-key-alists (n overlap)
  "A pair of alists, each binding n keys, sharing floor(overlap*n)
   random keys (with different values, so the merge's left bias is
   exercised); the remaining keys are fresh random u60s."
  (let* ((nshared (floor (* n overlap)))
         (shared (loop repeat nshared collect (random-u60))))
    (flet ((fresh (m)
             (loop repeat m collect (cons (random-u60) 0))))
      (cons (append (fresh (- n nshared))
                    (mapcar (lambda (k) (cons k 1)) shared))
            (append (fresh (- n nshared))
                    (mapcar (lambda (k) (cons k 2)) shared))))))

(defun memo-setup (thunk)
  "Memoize a setup thunk so specs sharing it share one inputs vector."
  (let ((cache nil))
    (lambda ()
      (or cache (setq cache (funcall thunk))))))

(defun merge-specs (n overlap)
  ;; update* is the left-biased map union; measured on the same prebuilt
  ;; map pairs for both representations.
  (let* ((class (format nil "overlap~A" overlap))
         (pairs (corpus (format nil "merge-keys/~A/~A" n overlap)
                        *merge-pairs*
                        (lambda () (merge-key-alists n overlap))))
         (setup-tree
           (memo-setup
             (lambda ()
               (map 'vector
                    (lambda (p) (cons (treemap::from-alist (car p))
                                      (treemap::from-alist (cdr p))))
                    pairs))))
         (setup-omap
           (memo-setup
             (lambda ()
               (map 'vector
                    (lambda (p) (cons (omap::from-alist (car p))
                                      (omap::from-alist (cdr p))))
                    pairs)))))
    (append
      (list
        (spec "treemap-update*" class n setup-tree
              (lambda (p) (treemap::update* (car p) (cdr p) :test =))))
      (and (<= n *omap-quadratic-max*)
           (list
             (spec "omap-update*" class n setup-omap
                   (lambda (p) (omap::update* (car p) (cdr p)))))))))

(defun construction-specs (n)
  ;; Whole-container construction from the same random alist.
  (let ((setup-alist
          (lambda () (vector (keys-alist (keys-vector n)))))
        (setup-map
          (lambda () (vector (getf (containers n) :treemap)))))
    (append
      (list
        (spec "treemap-from-alist" "u60" n setup-alist
              (lambda (al) (treemap::from-alist al))))
      (and (<= n *omap-quadratic-max*)
           (list
             (spec "omap-from-alist" "u60" n setup-alist
                   (lambda (al) (omap::from-alist al)))))
      (list
        (spec "treemap-to-omap" "u60" n setup-map
              (lambda (m) (treemap::to-omap m)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Treap shape statistics (untimed). The raw treemap representation is
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
   tree."
  (format t "~&Treap depth (expected average ~~1.39*log2(n)):~%")
  (format t "  ~10@A ~12A ~10A ~10A ~12A~%"
          "n" "keys" "avg" "max" "1.39log2n")
  (dolist (n cardinalities)
    (dolist (entry
              (list (cons "random" (getf (containers n) :treemap))
                    (cons "sequential"
                          (treemap::from-alist
                            (loop for i below n collect (cons i i))))))
      (multiple-value-bind (sum count) (tree-depth-sum (cdr entry) 1)
        (format t "  ~10:D ~12A ~10,2F ~10D ~12,2F~%"
                n
                (car entry)
                (float (/ sum (max 1 count)))
                (tree-max-depth (cdr entry))
                (* 1.39 (log n 2))))))
  (values))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Derived report: how much of an update is spent hashing the key. This
;; bounds the whole-operation benefit of any faster hash function.

(defun median-ns-of-op (op inputs &key (regions 7))
  "Standalone quick measurement, without a spec row: median real ns/op
   over a few calibrated regions."
  (let ((iters (bench::calibrate op inputs)))
    (bench::median
      (loop repeat regions
            collect (bench::ticks-to-ns
                      (nth-value 0 (bench::time-region op inputs iters))
                      iters)))))

(defun median-of (name class size)
  (loop for row in bench:*results*
        when (and (equal (getf row :name) name)
                  (equal (getf row :class) class)
                  (eql (getf row :size) size))
          return (getf row :median-ns)))

(defun hash-share-report (&key (cardinalities '(1000 10000 100000 1000000))
                               (hit-prob 1/2))
  ;; treeset::hash (= hash::jenkins, benchmarked in the hash library's
  ;; own suite) is measured inline rather than as a spec row: its cost
  ;; is independent of cardinality, and only the ratio matters here.
  (let* ((class (probe-class hit-prob))
         (n0 (car (last cardinalities)))
         (h (median-ns-of-op (lambda (x) (treeset::hash x))
                             (probes-vector n0 hit-prob))))
    (format t "~&Hash share of treemap-update (p=~A, hash ~,1Fns):~%"
            hit-prob h)
    (dolist (n cardinalities)
      (let ((i (median-of "treemap-update" class n)))
        (when (and i (plusp i))
          (format t "  n=~10:D: update ~8,1Fns -> hash share ~5,1F%~%"
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
                     (loop for p in in-probs append (lookup-specs n p))
                     (update-specs n mixed-prob)
                     (delete-specs n mixed-prob)))
      (loop for n in pair-cardinalities
            append (loop for ov in overlaps append (merge-specs n ov)))
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
    (run-suite :out (format nil "results/treemap-bench-~A.csv" stamp)
               :samples-out
               (format nil "results/treemap-bench-~A-samples.csv" stamp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(format t "~&; Running quick smoke suite; use (treemap-bench::run-full) ~
           for the real thing.~%")
(run-quick)
