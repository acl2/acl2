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
           "HASH-SHARE-REPORT"
           "CLASS-SIZE-REPORT"
           "TEST-VARIANT-REPORT"
           "SERIALIZED-SIZE"))

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

(defun merge-key-alists (n m overlap)
  "A pair of alists binding n and m keys respectively, sharing
   floor(overlap*min(n,m)) random keys (with different values, so the
   merge's left bias is exercised) -- the overlap is a fraction of the
   SMALLER map, so that it stays meaningful when m < n. The remaining
   keys are fresh random u60s."
  (let* ((nshared (floor (* (min n m) overlap)))
         (shared (loop repeat nshared collect (random-u60))))
    (flet ((fresh (k)
             (loop repeat k collect (cons (random-u60) 0))))
      (cons (append (fresh (- n nshared))
                    (mapcar (lambda (k) (cons k 1)) shared))
            (append (fresh (- m nshared))
                    (mapcar (lambda (k) (cons k 2)) shared))))))

(defun memo-setup (thunk)
  "Memoize a setup thunk so specs sharing it share one inputs vector."
  (let ((cache nil))
    (lambda ()
      (or cache (setq cache (funcall thunk))))))

(defun merge-specs (n overlap &optional (m n))
  ;; update* is the left-biased map union; measured on the same prebuilt
  ;; map pairs for both representations. m defaults to n (the
  ;; equal-cardinality case). The advantage the complexity table claims,
  ;; O(m log(n/m)) against O(n+m), only shows when m is much smaller
  ;; than n; at m = n the bound degenerates to O(n) and the flat merge
  ;; wins outright, so the asymmetric case is the one that tests the
  ;; claim.
  (let* ((class (if (eql m n)
                    (format nil "overlap~A" overlap)
                  (format nil "m~A/overlap~A" m overlap)))
         (pairs (corpus (format nil "merge-keys/~A/~A/~A" n m overlap)
                        *merge-pairs*
                        (lambda () (merge-key-alists n m overlap))))
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
              (lambda (m) (treemap::to-omap m)))
        ;; The linear treap-from-omap path, against from-alist above, which
        ;; pays hashing plus O(log n) path copying per entry.
        (spec "treemap-from-omap" "u60" n
              (memo-setup
                (lambda ()
                  (vector (treemap::to-omap
                            (getf (containers n) :treemap)))))
              (lambda (m) (treemap::from-omap m)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Key classes. The specs above draw u60 keys, which is the cheapest
;; case for both << and hash: the complexity table's entries count
;; comparisons, and a comparison is O(k) in the size of the key. These
;; generators widen that to keys of a controlled size, so the margin
;; over omaps can be plotted against key size rather than asserted at
;; one point of it. Values are a constant 0 throughout: the operations
;; under measurement walk keys, never values.
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
  (intern (random-string nchars) "TREEMAP-BENCH"))

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
   on the whole map's keys, not just the probe: lookup-= wants
   acl2-number keys, lookup-eq symbol keys, lookup-eql eqlable ones, so
   which variants apply is a property of the class."
  (list :name name :gen gen :tests tests))

(defun default-key-classes ()
  (list (keyclass "u60" #'random-u60 :tests '(equal = eql))
        ;; Note this class caps out at 256 distinct keys, so its map is
        ;; that size whatever cardinality is asked for. That makes it
        ;; unusable as a point on a speedup-against-key-size plot -- the
        ;; n differs from every other class -- though it stays valid in
        ;; the :test variant report, where both sides share the n.
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

;; Size sweeps: one type, many sizes. The default classes above vary type
;; and size together, which is good coverage but leaves no controlled
;; variable -- a speedup plotted against size across them confounds the
;; two, and the resulting scatter has no trend to read. These hold the
;; type fixed so size is the only thing moving. Two families, because the
;; mechanism should be type-independent: comparisons exit at the first
;; differing byte while the hash walks the whole key, so the lookup ratio
;; should be flat in size and the update ratio should decay.

(defun bignum-sweep-classes (&optional (bits '(64 256 1024 4096 16384)))
  (loop for b in bits
        collect (let ((b b))
                  (keyclass (format nil "nat~D" b)
                            (lambda () (random-bignum b))
                            :tests '(equal = eql)))))

(defun string-sweep-classes (&optional (lens '(8 32 128 512 2048)))
  (loop for n in lens
        collect (let ((n n))
                  (keyclass (format nil "str~D" n)
                            (lambda () (random-string n))))))

(defun serialized-size (x)
  (length (hash::to-bytes x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Containers and probes for a key class. Only treemaps and omaps are
;; built: the fast alist and hash table rows exist to place the two
;; libraries on a scale, which one cardinality already does, and an eql
;; hash table would not even accept the non-atomic classes. The omap is
;; extracted from the treemap by to-omap, which is linear, rather than
;; built by omap::from-alist, which is quadratic; with every value 0 the
;; two constructions agree even on classes with duplicate keys.

(defvar *class-containers* (make-hash-table :test #'equal))

(defun class-containers (kc n)
  (let ((ckey (list (getf kc :name) n)))
    (or (gethash ckey *class-containers*)
        (setf (gethash ckey *class-containers*)
              (let* ((keys (corpus (format nil "class-keys/~A/~A"
                                           (getf kc :name) n)
                                   n (getf kc :gen)))
                     (alist (map 'list (lambda (k) (cons k 0)) keys))
                     (tmap (treemap::from-alist alist)))
                (format t "; building ~A cardinality-~:D containers~%"
                        (getf kc :name) n)
                (finish-output)
                (list :keys keys
                      :treemap tmap
                      :omap (treemap::to-omap tmap)))))))

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
  ;; lookup and update only: they are the operations whose cost is
  ;; dominated by the key, and update is the only one that hashes.
  (let* ((c (class-containers kc n))
         (tmap (getf c :treemap))
         (omap (getf c :omap))
         (class (getf kc :name))
         (setup (lambda () (class-probes-vector kc n hit-prob))))
    (list
      (spec "treemap-lookup" class n setup
            (lambda (x) (treemap::lookup x tmap)))
      (spec "omap-lookup" class n setup
            (lambda (x) (omap::lookup x omap)))
      (spec "treemap-update" class n setup
            (lambda (x) (treemap::update x 0 tmap)))
      (spec "omap-update" class n setup
            (lambda (x) (omap::update x 0 omap))))))

(defun test-lookup-op (test tmap)
  ;; :test is a macro keyword and must be literal, so each variant is
  ;; its own lambda rather than a parameter.
  (ecase test
    (equal (lambda (x) (treemap::lookup x tmap)))
    (=     (lambda (x) (treemap::lookup x tmap :test =)))
    (eq    (lambda (x) (treemap::lookup x tmap :test eq)))
    (eql   (lambda (x) (treemap::lookup x tmap :test eql)))))

(defun test-update-op (test tmap)
  (ecase test
    (equal (lambda (x) (treemap::update x 0 tmap)))
    (=     (lambda (x) (treemap::update x 0 tmap :test =)))
    (eq    (lambda (x) (treemap::update x 0 tmap :test eq)))
    (eql   (lambda (x) (treemap::update x 0 tmap :test eql)))))

(defun test-specs (kc n hit-prob)
  "lookup and update under each :test the class admits, so the cost of
   the specialized guards and hashes can be read off against the
   default."
  (let* ((c (class-containers kc n))
         (tmap (getf c :treemap))
         (class (getf kc :name))
         (setup (lambda () (class-probes-vector kc n hit-prob))))
    (loop for test in (getf kc :tests)
          append
          (list
            (spec (format nil "treemap-lookup-~(~A~)" test) class n setup
                  (test-lookup-op test tmap))
            (spec (format nil "treemap-update-~(~A~)" test) class n setup
                  (test-update-op test tmap))))))

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

;; A random BST reference for the depth report. The measured rows are
;; treaps over hashed keys; the question they answer is whether the hash
;; behaves like a random priority, which is only meaningful against the
;; distribution being claimed. With distinct random priorities a treap
;; has exactly the shape distribution of a BST built by inserting a
;; uniformly random permutation, so we build such trees and measure them
;; the same way rather than plotting an asymptotic formula. The expected
;; mean depth does have a closed form, but the expected height does not
;; -- it is alpha*ln(n) - beta*ln(ln(n)) + O(1) with the O(1) unknown,
;; and over this range that constant is worth about five levels.

(defun random-permutation (n)
  (let ((v (make-array n :element-type 'fixnum)))
    (dotimes (i n) (setf (aref v i) i))
    (loop for i from (1- n) downto 1
          do (rotatef (aref v i) (aref v (random (1+ i)))))
    v))

(defun bst-insert (root key)
  "Destructively insert KEY into the cons-shaped BST ROOT, returning the
   root. The shape is the treap's own -- head in the car, left and right
   in the cdr -- so the depth functions above apply unchanged."
  (if (null root)
      (cons key (cons nil nil))
    (let ((node root))
      (loop
        (if (< key (car node))
            (if (cadr node)
                (setf node (cadr node))
              (progn (setf (cadr node) (cons key (cons nil nil)))
                     (return root)))
          (if (cddr node)
              (setf node (cddr node))
            (progn (setf (cddr node) (cons key (cons nil nil)))
                   (return root))))))))

(defun random-bst (n)
  (let ((root nil))
    (loop for key across (random-permutation n)
          do (setf root (bst-insert root key)))
    root))

(defun random-bst-depth-stats (n trials)
  "(values mean-depth height), each averaged over TRIALS random BSTs.
   Height is a max statistic and scatters by about two levels between
   trials, which is why it is averaged rather than sampled once."
  (let ((avg 0d0) (height 0d0))
    (dotimes (i trials)
      (let ((tree (random-bst n)))
        (multiple-value-bind (sum count) (tree-depth-sum tree 1)
          (incf avg (/ (float sum 1d0) (max 1 count))))
        (incf height (float (tree-max-depth tree) 1d0))))
    (values (/ avg trials) (/ height trials))))

(defun depth-report (&key (cardinalities '(1000 10000 100000 1000000))
                          (trials 10))
  "Treap depth statistics for random and sequential keys, against random
   BSTs of the same size. Sequential keys exercise the consecutive-integer
   hash stream, whose 32-bit collision counts looked slightly high; excess
   depth here would mean those collisions cluster enough to hurt balance.
   Depth counts nodes, with the root at 1."
  (format t "~&Treap depth (random-bst rows averaged over ~D trials):~%"
          trials)
  (format t "  ~10@A ~12A ~10A ~10A~%" "n" "keys" "avg" "height")
  (dolist (n cardinalities)
    (dolist (entry
              (list (cons "random" (getf (containers n) :treemap))
                    (cons "sequential"
                          (treemap::from-alist
                            (loop for i below n collect (cons i i))))))
      (multiple-value-bind (sum count) (tree-depth-sum (cdr entry) 1)
        (format t "  ~10:D ~12A ~10,2F ~10,2F~%"
                n
                (car entry)
                (float (/ sum (max 1 count)))
                (float (tree-max-depth (cdr entry))))))
    (multiple-value-bind (avg height) (random-bst-depth-stats n trials)
      (format t "  ~10:D ~12A ~10,2F ~10,2F~%" n "random-bst" avg height)))
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

(defun test-variant-report (classes n)
  "What the specialized :tests buy, as a percentage of the default
   equal. Only classes admitting more than one test appear."
  (format t "~&:test variants, as a percentage of the default equal:~%")
  (format t "  ~12A ~8A ~8A ~12A ~10A~%"
          "class" "op" "test" "median-ns" "vs equal")
  (dolist (kc classes)
    (let ((class (getf kc :name)))
      (when (cdr (getf kc :tests))
        (dolist (op '("lookup" "update"))
          (let ((base (median-of (format nil "treemap-~A-equal" op)
                                 class n)))
            (when (and base (plusp base))
              (dolist (test (getf kc :tests))
                (let ((v (median-of (format nil "treemap-~A-~(~A~)" op test)
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
                       ;; One hit rate for every operation, so lookup,
                       ;; update and delete are all reported on the same
                       ;; footing. Cost is linear in this, so the
                       ;; endpoints are still available by running
                       ;; :in-probs '(0 1).
                       (in-probs '(1/2))
                       (mixed-prob 1/2)
                       (pair-cardinalities '(1000 10000 100000))
                       (overlaps '(0 1/2 1))
                       ;; Ratios m/n for the merge. 1 is the
                       ;; equal-cardinality case; the smaller ratios are
                       ;; where the O(m log(n/m)) bound is supposed to pay.
                       (pair-ratios '(1 1/10 1/100))
                       ;; Key classes for the key-size sweep, run at a
                       ;; single cardinality rather than crossed with the
                       ;; sweep above, which would multiply the runtime.
                       (key-classes nil)
                       (key-class-cardinality 10000)
                       ;; Adds lookup/update rows under each :test a
                       ;; class admits, alongside the default-equal rows.
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
                     (loop for p in in-probs append (lookup-specs n p))
                     (update-specs n mixed-prob)
                     (delete-specs n mixed-prob)))
      (loop for n in pair-cardinalities
            append (loop for ov in overlaps
                         append (loop for r in pair-ratios
                                      append (merge-specs
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
               :out (format nil "results/treemap-bench-~A.csv" stamp)
               :samples-out
               (format nil "results/treemap-bench-~A-samples.csv" stamp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(format t "~&; Running quick smoke suite; use (treemap-bench::run-full) ~
           for the real thing.~%")
(run-quick)
