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
           "HASH-SHARE-REPORT"
           "CLASS-SIZE-REPORT"
           "TEST-VARIANT-REPORT"
           "SERIALIZED-SIZE"))

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

(defun union-key-lists (n m overlap)
  "A pair of key lists of lengths n and m, sharing floor(overlap*m)
   random keys -- the overlap is a fraction of the SMALLER set, so that
   it stays meaningful when m < n. Random keys replace the old
   generator's consecutive naturals, whose blockwise key ranges made
   union's merge pattern degenerate."
  (let* ((nshared (floor (* (min n m) overlap)))
         (shared (loop repeat nshared collect (random-u60))))
    (cons (append (loop repeat (- n nshared) collect (random-u60))
                  shared)
          (append (loop repeat (- m nshared) collect (random-u60))
                  shared))))

(defun memo-setup (thunk)
  "Memoize a setup thunk so specs sharing it share one inputs vector."
  (let ((cache nil))
    (lambda ()
      (or cache (setq cache (funcall thunk))))))

(defun binary-specs (n overlap &optional (m n))
  ;; union, intersect, and diff, all on the same prebuilt set pairs.
  ;; m defaults to n (the equal-cardinality case). The advantage the
  ;; complexity table claims, O(m log(n/m)) against O(n+m), only shows
  ;; when m is much smaller than n; at m = n the bound degenerates to
  ;; O(n) and osets win outright, so the asymmetric case is the one that
  ;; tests the claim.
  (let* ((class (if (eql m n)
                    (format nil "overlap~A" overlap)
                  (format nil "m~A/overlap~A" m overlap)))
         (pairs (corpus (format nil "union-keys/~A/~A/~A" n m overlap)
                        *union-pairs*
                        (lambda () (union-key-lists n m overlap))))
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

;; Key classes. The specs above draw u60 keys, which is the cheapest
;; case for both << and hash: the complexity table's entries count
;; comparisons, and a comparison is O(k) in the size of the element.
;; These generators widen that to keys of a controlled size, so the
;; margin over osets can be plotted against element size rather than
;; asserted at one point of it.
;;
;; Size is reported as serialized byte length, (len (to-bytes x)): that
;; is what the hash actually walks, and it is comparable across types,
;; so strings, conses and bignums share one x axis. The generators aim
;; at a target size rather than hitting it exactly, so the sweep reports
;; the size the corpus actually has (class-size-report).
;;
;; Every class here uses the default :test (equal), including the u60
;; baseline, so the classes are compared on equal footing. The specs
;; further up use :test = for u60, which is a different (faster) path;
;; the two sets of numbers are not interchangeable.

(defun random-string (nchars)
  (let ((s (make-string nchars)))
    (dotimes (i nchars s)
      (setf (char s i) (code-char (+ 32 (random 95)))))))

(defun random-symbol (nchars)
  ;; Interned in this package rather than ACL2, to avoid filling the
  ;; ACL2 package with junk. Note the package name is part of a symbol's
  ;; encoding, so it contributes a fixed overhead to the serialized size.
  (intern (random-string nchars) "TREESET-BENCH"))

(defun random-character ()
  (code-char (random 256)))

(defun random-bignum (nbits)
  (random (expt 2 nbits)))

(defun random-cons (nleaves)
  "A balanced binary tree with nleaves u60 leaves."
  (if (<= nleaves 1)
      (random-u60)
    (let ((half (floor nleaves 2)))
      (cons (random-cons half)
            (random-cons (- nleaves half))))))

(defun random-acl2-atom ()
  "Weighted toward the types ACL2 data actually contains, but covering
   every one of to-bytes' constructible tag paths: integer, string,
   symbol, character, rational and complex rational. (Bad atoms are the
   seventh tag and cannot be built from the logic.) Rationals may reduce
   to integers, which is harmless -- the object is still arbitrary."
  (let ((r (random 100)))
    (cond ((< r 30) (random-u60))
          ((< r 40) (- (random-u60)))
          ((< r 60) (random-string (+ 1 (random 16))))
          ((< r 85) (random-symbol (+ 1 (random 16))))
          ((< r 92) (random-character))
          ((< r 98) (/ (- (random-u60) (expt 2 59))
                       (+ 1 (random (expt 2 20)))))
          ;; A non-zero imaginary part, or complex would return a real.
          (t (complex (- (random 1000) 500) (+ 1 (random 1000)))))))

(defun random-acl2-object (&optional (depth 3))
  "An arbitrary ACL2 object: an atom of some type, or a cons of two."
  (if (or (<= depth 0) (< (random 1.0) 0.5))
      (random-acl2-atom)
    (cons (random-acl2-object (1- depth))
          (random-acl2-object (1- depth)))))

(defun keyclass (name gen &key (tests '(equal)))
  "tests are the :test variants the class's keys admit. The guards are
   on the whole set, not just the probe: in-= wants an acl2-number-setp,
   in-eq a symbol set, in-eql an eqlable one, so which variants apply is
   a property of the class."
  (list :name name :gen gen :tests tests))

(defun default-key-classes ()
  (list (keyclass "u60" #'random-u60 :tests '(equal = eql))
        (keyclass "char" #'random-character :tests '(equal eql))
        (keyclass "string8" (lambda () (random-string 8)))
        (keyclass "string64" (lambda () (random-string 64)))
        (keyclass "string512" (lambda () (random-string 512)))
        (keyclass "symbol8" (lambda () (random-symbol 8))
                  :tests '(equal eq eql))
        (keyclass "cons8" (lambda () (random-cons 8)))
        (keyclass "cons64" (lambda () (random-cons 64)))
        (keyclass "bignum512" (lambda () (random-bignum 512))
                  :tests '(equal = eql))
        (keyclass "mixed" (lambda () (random-acl2-object)))))

(defun serialized-size (x)
  (length (hash::to-bytes x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Containers and probes for a key class. Only treesets and osets are
;; built: the fast alist and hash table rows exist to place the two
;; libraries on a scale, which one cardinality already does, and an eql
;; hash table would not even accept the non-atomic classes.

(defvar *class-containers* (make-hash-table :test #'equal))

(defun class-containers (kc n)
  (let ((ckey (list (getf kc :name) n)))
    (or (gethash ckey *class-containers*)
        (setf (gethash ckey *class-containers*)
              (let* ((keys (corpus (format nil "class-keys/~A/~A"
                                           (getf kc :name) n)
                                   n (getf kc :gen)))
                     (lst (coerce keys 'list)))
                (format t "; building ~A cardinality-~:D containers~%"
                        (getf kc :name) n)
                (finish-output)
                (list :keys keys
                      :treeset (treeset::from-list lst)
                      :oset (set::mergesort lst)))))))

(defun class-probes-vector (kc n hit-prob)
  (let ((keys (getf (class-containers kc n) :keys))
        (p (float hit-prob))
        (gen (getf kc :gen)))
    (corpus (format nil "class-probes/~A/~A/~A" (getf kc :name) n hit-prob)
            *probes-per-spec*
            (lambda ()
              (if (< (random 1.0) p)
                  (svref keys (random (length keys)))
                (funcall gen))))))

(defun size-specs (kc n hit-prob)
  ;; in and insert only: they are the operations whose cost is dominated
  ;; by the element, and insert is the only one that hashes.
  (let* ((c (class-containers kc n))
         (tset (getf c :treeset))
         (oset (getf c :oset))
         (class (getf kc :name))
         (setup (lambda () (class-probes-vector kc n hit-prob))))
    (list
      (spec "treeset-in" class n setup
            (lambda (x) (treeset::in x tset)))
      (spec "oset-in" class n setup
            (lambda (x) (set::in x oset)))
      (spec "treeset-insert" class n setup
            (lambda (x) (treeset::insert x tset)))
      (spec "oset-insert" class n setup
            (lambda (x) (set::insert x oset))))))

(defun test-in-op (test tset)
  ;; :test is a macro keyword and must be literal, so each variant is
  ;; its own lambda rather than a parameter.
  (ecase test
    (equal (lambda (x) (treeset::in x tset)))
    (=     (lambda (x) (treeset::in x tset :test =)))
    (eq    (lambda (x) (treeset::in x tset :test eq)))
    (eql   (lambda (x) (treeset::in x tset :test eql)))))

(defun test-insert-op (test tset)
  (ecase test
    (equal (lambda (x) (treeset::insert x tset)))
    (=     (lambda (x) (treeset::insert x tset :test =)))
    (eq    (lambda (x) (treeset::insert x tset :test eq)))
    (eql   (lambda (x) (treeset::insert x tset :test eql)))))

(defun test-specs (kc n hit-prob)
  "in and insert under each :test the class admits, so the cost of the
   specialized guards and hashes can be read off against the default."
  (let* ((c (class-containers kc n))
         (tset (getf c :treeset))
         (class (getf kc :name))
         (setup (lambda () (class-probes-vector kc n hit-prob))))
    (loop for test in (getf kc :tests)
          append
          (list
            (spec (format nil "treeset-in-~(~A~)" test) class n setup
                  (test-in-op test tset))
            (spec (format nil "treeset-insert-~(~A~)" test) class n setup
                  (test-insert-op test tset))))))

(defparameter *size-report-sample* 1000)

(defun class-size-report (classes n)
  "The serialized size the corpora actually have, which is the x axis
   the timing rows should be plotted against."
  (format t "~&Serialized key size by class (bytes, over ~:D sampled keys):~%"
          *size-report-sample*)
  (format t "  ~12A ~10A ~10A ~10A~%" "class" "mean" "min" "max")
  (dolist (kc classes)
    (let* ((keys (getf (class-containers kc n) :keys))
           (sample (min *size-report-sample* (length keys)))
           (sizes (loop for i below sample
                        collect (serialized-size (svref keys i)))))
      (format t "  ~12A ~10,1F ~10D ~10D~%"
              (getf kc :name)
              (float (/ (reduce #'+ sizes) sample))
              (reduce #'min sizes)
              (reduce #'max sizes))))
  (values))

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

(defun test-variant-report (classes n)
  "What the specialized :tests buy, as a percentage of the default
   equal. Only classes admitting more than one test appear."
  (format t "~&:test variants, as a percentage of the default equal:~%")
  (format t "  ~12A ~8A ~8A ~12A ~10A~%"
          "class" "op" "test" "median-ns" "vs equal")
  (dolist (kc classes)
    (let ((class (getf kc :name)))
      (when (cdr (getf kc :tests))
        (dolist (op '("in" "insert"))
          (let ((base (median-of (format nil "treeset-~A-equal" op)
                                 class n)))
            (when (and base (plusp base))
              (dolist (test (getf kc :tests))
                (let ((v (median-of (format nil "treeset-~A-~(~A~)" op test)
                                    class n)))
                  (when v
                    (format t "  ~12A ~8A ~8A ~12,1F ~9,1F%~%"
                            class op (string-downcase (symbol-name test))
                            v (* 100 (/ v base))))))))))))
  (values))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Suites

(defun run-suite (&key (seed 1)
                       (cardinalities '(1000 10000 100000 1000000))
                       (in-probs '(0 1))
                       (mixed-prob 1/2)
                       (pair-cardinalities '(1000 10000 100000))
                       (overlaps '(0 1/2 1))
                       ;; Ratios m/n for the binary operations. 1 is the
                       ;; equal-cardinality case; the smaller ratios are
                       ;; where the O(m log(n/m)) bound is supposed to pay.
                       (pair-ratios '(1 1/10 1/100))
                       ;; Key classes for the element-size sweep, run at a
                       ;; single cardinality rather than crossed with the
                       ;; sweep above, which would multiply the runtime.
                       (key-classes nil)
                       (key-class-cardinality 10000)
                       ;; Adds in/insert rows under each :test a class
                       ;; admits, alongside the default-equal rows.
                       (test-variants nil)
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
            append (loop for ov in overlaps
                         append (loop for r in pair-ratios
                                      append (binary-specs
                                               n ov (max 1 (floor (* n r)))))))
      (and construction
           (loop for n in cardinalities append (construction-specs n)))
      (loop for kc in key-classes
            append (size-specs kc key-class-cardinality mixed-prob))
      (and test-variants
           (loop for kc in key-classes
                 when (cdr (getf kc :tests))
                   append (test-specs kc key-class-cardinality mixed-prob))))
    :gc gc)
  (print-results)
  (when depth
    (depth-report :cardinalities cardinalities))
  (when hash-share
    (hash-share-report :cardinalities cardinalities :hit-prob mixed-prob))
  (when key-classes
    (class-size-report key-classes key-class-cardinality))
  (when (and key-classes test-variants)
    (test-variant-report key-classes key-class-cardinality))
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
               :overlaps '(1/2)
               :pair-ratios '(1 1/100)
               :key-classes (list (keyclass "u60" #'random-u60
                                            :tests '(equal = eql))
                                  (keyclass "symbol8"
                                            (lambda () (random-symbol 8))
                                            :tests '(equal eq eql))
                                  (keyclass "string512"
                                            (lambda () (random-string 512))))
               :key-class-cardinality 1000
               :test-variants t)))

(defun run-full ()
  (let ((stamp (substitute #\- #\: (bench::timestamp))))
    (run-suite :key-classes (default-key-classes)
               :test-variants t
               :out (format nil "results/treeset-bench-~A.csv" stamp)
               :samples-out
               (format nil "results/treeset-bench-~A-samples.csv" stamp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(format t "~&; Running quick smoke suite; use (treeset-bench::run-full) ~
           for the real thing.~%")
(run-quick)
