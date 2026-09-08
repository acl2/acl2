; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The raw-Lisp part of the hash benchmarks. Loaded by benchmark.lsp;
; see the usage comment there. This file is read by the Common Lisp
; reader (via cl:load), not by ld, so it may define and enter its own
; package.

(defpackage "HASH-BENCH"
  (:use "COMMON-LISP" "BENCH")
  (:export "RUN-QUICK" "RUN-FULL" "STRESS-REPORT"))

(in-package "HASH-BENCH")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Input generation. All generators draw from bench's seeded PRNG.

(defun random-u60 ()
  (random (expt 2 60)))

(defun random-bignum (bits)
  "A random natural of exactly the given bit length."
  (logior (ash 1 (1- bits))
          (random (ash 1 (1- bits)))))

(defun random-string (len)
  "A random string over the full 8-bit character range."
  (let ((s (make-string len)))
    (dotimes (i len s)
      (setf (char s i) (code-char (random 256))))))

(defun random-alpha-string (len)
  (let ((s (make-string len)))
    (dotimes (i len s)
      (setf (char s i)
            (code-char (+ (char-code #\A) (random 26)))))))

(defun random-symbol (len)
  (intern (random-alpha-string len) (find-package "ACL2")))

(defun random-tree (nodes)
  "A random cons tree with the given number of conses, with small
   integer leaves."
  (if (<= nodes 0)
      (random 256)
    (let ((left (random nodes)))
      (cons (random-tree left)
            (random-tree (- nodes 1 left))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Specs. Each input class is measured for hash::jenkins and, as a
;; familiar reference point, cl:sxhash. Note that sxhash descends conses
;; only to a small bounded depth, so the cons-tree comparison flatters
;; sxhash and is included only for orientation.

(defparameter *inputs-per-class* 512)

(defun jenkins-op (x) (hash::jenkins x))
(defun sxhash-op (x) (sxhash x))
(defun eqlable-jenkins-op (x) (hash::eqlable-jenkins x))
(defun identity-op (x) x)
(defun to-bytes-op (x) (hash::to-bytes x))
(defun jenkins-bytes-op (bytes) (hash::jenkins-bytes bytes))
(defun layered-jenkins-op (x) (hash::jenkins-bytes (hash::to-bytes x)))

(defun corpus-setup (class size gen &key (inputs *inputs-per-class*))
  "A memoized setup thunk for the corpus keyed by class and size. All
   specs built from one thunk share a single corpus vector; separate
   thunks with the same class and size regenerate identical inputs (see
   bench:corpus), so every spec of a class measures the same inputs."
  (let ((key (format nil "~A/~A" class size))
        (cache nil))
    (lambda ()
      (or cache (setq cache (corpus key inputs gen))))))

(defun class-specs (class size gen &key bytes-per-op (sxhash t)
                                        (inputs *inputs-per-class*))
  (let ((setup (corpus-setup class size gen :inputs inputs)))
    (append
      (list (spec "jenkins" class size setup #'jenkins-op
                  :bytes-per-op bytes-per-op))
      (and sxhash
           (list (spec "sxhash" class size setup #'sxhash-op
                       :bytes-per-op bytes-per-op))))))

(defun baseline-specs ()
  ;; Measures the harness itself: svref, funcall, and the *sink* write.
  ;; That overhead is not subtracted from the other rows; at nanosecond
  ;; scale (e.g. jenkins on fixnums) it is a visible fraction, so quote
  ;; absolute ns/op net of this row.
  (list (spec "baseline-identity" "u60" 60
              (corpus-setup "u60" 60 #'random-u60)
              #'identity-op)))

(defun fixnum-specs ()
  (append
    (class-specs "u60" 60 #'random-u60)
    (list (spec "eqlable-jenkins" "u60" 60
                (corpus-setup "u60" 60 #'random-u60)
                #'eqlable-jenkins-op))))

(defun bignum-specs (bits)
  (class-specs "bignum" bits
               (lambda () (random-bignum bits))
               :bytes-per-op (ceiling bits 8)))

(defun string-specs (len)
  (class-specs "string" len
               (lambda () (random-string len))
               :bytes-per-op len))

(defun symbol-specs (len)
  ;; Symbols are interned during setup, outside the timed region. The
  ;; hash covers the symbol name and the package name.
  (append
    (class-specs "symbol" len (lambda () (random-symbol len)))
    (list (spec "eqlable-jenkins" "symbol" len
                (corpus-setup "symbol" len (lambda () (random-symbol len)))
                #'eqlable-jenkins-op))))

(defun tree-specs (nodes)
  ;; Trees are the memory hog (16 bytes per cons), so cap the corpus at
  ;; roughly 32 MB rather than using *inputs-per-class*.
  (let ((inputs (max 16 (min *inputs-per-class*
                             (floor (ash 1 21) (max 1 nodes))))))
    (class-specs "cons-tree" nodes
                 (lambda () (random-tree nodes))
                 :inputs inputs)))

(defun layered-specs (class size gen &key bytes-per-op
                                          (inputs *inputs-per-class*))
  "Decompose the fused jenkins :exec path on one input class:
     to-bytes        — serialization alone (conses the byte list);
     jenkins-bytes   — mixing alone, over pre-serialized byte lists;
     jenkins-layered — the unfused (jenkins-bytes (to-bytes x)), i.e.
                       what the mbe fusion in jenkins saves.
   The corpus key is class and size, so these rows measure the same
   inputs as the fused jenkins row of that class and size. bytes-per-op
   stays keyed to *input* bytes (not serialized bytes, which include
   tags and LEB128 overhead) so MB/s is comparable with the fused row."
  (let* ((setup (corpus-setup class size gen :inputs inputs))
         (bytes-setup
           (let ((cache nil))
             (lambda ()
               (or cache
                   (setq cache
                         (let* ((v (funcall setup))
                                (w (make-array (length v))))
                           (dotimes (i (length v) w)
                             (setf (svref w i)
                                   (hash::to-bytes (svref v i)))))))))))
    (list (spec "to-bytes" class size setup #'to-bytes-op
                :bytes-per-op bytes-per-op)
          (spec "jenkins-bytes" class size bytes-setup #'jenkins-bytes-op
                :bytes-per-op bytes-per-op)
          (spec "jenkins-layered" class size setup #'layered-jenkins-op
                :bytes-per-op bytes-per-op))))

(defun all-layered-specs ()
  ;; A representative subset: fixnums (atom fast path), a mid bignum
  ;; (the D&C LEB128 encoder), and a small and large string.
  (append
    (layered-specs "u60" 60 #'random-u60)
    (layered-specs "bignum" 1024 (lambda () (random-bignum 1024))
                   :bytes-per-op 128)
    (layered-specs "string" 1024 (lambda () (random-string 1024))
                   :bytes-per-op 1024)
    (layered-specs "string" 65536 (lambda () (random-string 65536))
                   :bytes-per-op 65536)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Hash quality: collision counts against the birthday expectation.
;; These are not timed.

(defun count-collisions (n gen)
  "Hash n inputs from gen; return the number of collisions (n minus the
   number of distinct hash values)."
  (let ((seen (make-hash-table :test #'eql :size (* 2 n)))
        (distinct 0))
    (dotimes (i n)
      (let ((h (hash::jenkins (funcall gen))))
        (unless (gethash h seen)
          (setf (gethash h seen) t)
          (incf distinct))))
    (- n distinct)))

(defun expected-collisions (n)
  ;; Birthday approximation for a uniform 32-bit hash. Inputs drawn from
  ;; a generator may repeat, so treat this as an upper-quality target,
  ;; not an exact expectation.
  (float (/ (* n (1- n)) (expt 2 33))))

(defun collision-report (&key (n 1000000))
  (format t "~&Collision counts for ~:D inputs (expected ~,1F for a ~
             uniform 32-bit hash):~%"
          n (expected-collisions n))
  (let ((counter -1))
    (dolist (entry (list (list "consecutive ints"
                               (lambda () (incf counter)))
                         (list "random u60s" #'random-u60)
                         (list "random strings (len 16)"
                               (lambda () (random-string 16)))))
      (format t "  ~30A ~D~%"
              (first entry)
              (count-collisions n (second entry)))
      (finish-output))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Structural stress.
;;
;; jenkins-acc recurses in tail position on the cdr but not on the car,
;; so its control stack use is proportional to the car-depth of the
;; object, and is constant on lists. And, like any tree walk, it does
;; work proportional to the object's size as a tree, not as a DAG, so
;; shared subobjects are traversed once per occurrence.
;;
;; These probes measure where each of those becomes a problem.

(defun left-nest (depth)
  "An object of the given car-depth: ((..((0 . 0) . 0)..) . 0)."
  (let ((x 0))
    (dotimes (i depth x)
      (setq x (cons x 0)))))

(defun right-nest (depth)
  "A list of the given length, i.e. an object of that cdr-depth."
  (let ((x 0))
    (dotimes (i depth x)
      (setq x (cons 0 x)))))

(defun shared-dag (levels)
  "An object with `levels' conses in memory but 2^levels tree nodes."
  (let ((x 0))
    (dotimes (i levels x)
      (setq x (cons x x)))))

(defun control-stack-bytes ()
  (- (sb-sys:sap-int (sb-sys:int-sap sb-vm:*control-stack-end*))
     (sb-sys:sap-int (sb-sys:int-sap sb-vm:*control-stack-start*))))

(defun try-hash (x)
  "Hash x, catching control stack exhaustion."
  (handler-case (progn (hash::jenkins x) :ok)
    (storage-condition () :stack-overflow)
    (error (e) (declare (ignore e)) :error)))

(defun depth-report (&key (max-log 24))
  "Hash left- and right-nested objects of increasing depth, reporting
   where the control stack is exhausted."
  (format t "~&Recursion depth (control stack ~:D bytes):~%"
          (control-stack-bytes))
  (dolist (kind (list (list "car-depth (left-nested)" #'left-nest)
                      (list "cdr-depth (list)" #'right-nest)))
    (let ((last-ok 0) (first-bad nil))
      (loop for e from 10 to max-log
            for depth = (ash 1 e)
            for obj = (funcall (second kind) depth)
            for status = (try-hash obj)
            do (if (eq status :ok)
                   (setq last-ok depth)
                 (progn (setq first-bad depth) (return)))
               (finish-output))
      (format t "  ~26A ok to ~:D~@[, fails at ~:D~]~%"
              (first kind) last-ok first-bad))))

(defun time-hash (x)
  "Seconds of real time for one hash of x."
  (sb-ext:gc :full t)
  (let ((start (get-internal-real-time)))
    (setf bench:*sink* (hash::jenkins x))
    (/ (- (get-internal-real-time) start)
       (float internal-time-units-per-second))))

(defun sharing-report (&key (max-levels 24))
  "Hash objects whose size as a DAG is linear but whose size as a tree
   is exponential."
  (format t "~&Shared subobjects (conses in memory vs. tree nodes ~
             walked):~%")
  (format t "  ~8A ~14A ~12A~%" "conses" "tree nodes" "time")
  (loop for levels from 10 to max-levels
        for obj = (shared-dag levels)
        for secs = (time-hash obj)
        do (format t "  ~8D ~14:D ~10,3Fs~%" levels (ash 1 levels) secs)
           (finish-output)
        while (< secs 10)))

(defun stress-report (&key (max-log 24) (max-levels 24))
  (depth-report :max-log max-log)
  (terpri)
  (sharing-report :max-levels max-levels))

;; Suites

(defun run-suite (&key (seed 1)
                       (string-lens '(8 64 1024 65536))
                       (bignum-bits '(128 1024 16384 131072))
                       (tree-nodes '(16 1024 65536))
                       (symbol-lens '(16))
                       (layered t)
                       (gc :per-sample)
                       (collisions nil)
                       (collision-n 1000000)
                       (out nil)
                       (samples-out nil)
                       notes)
  (init-random seed)
  (clear-results)
  (run-specs
    (append
      (baseline-specs)
      (fixnum-specs)
      (loop for bits in bignum-bits append (bignum-specs bits))
      (loop for len in string-lens append (string-specs len))
      (loop for len in symbol-lens append (symbol-specs len))
      (loop for nodes in tree-nodes append (tree-specs nodes))
      (and layered (all-layered-specs)))
    :gc gc)
  (print-results)
  (when collisions
    (collision-report :n collision-n))
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
    (run-suite :string-lens '(8 1024)
               :bignum-bits '(128 16384)
               :tree-nodes '(1024)
               :symbol-lens '(16)
               :gc :per-round)))

(defun run-full ()
  (let ((stamp (substitute #\- #\: (bench::timestamp))))
    (run-suite :collisions t
               :out (format nil "results/hash-bench-~A.csv" stamp)
               :samples-out (format nil "results/hash-bench-~A-samples.csv"
                                    stamp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(format t "~&; Running quick smoke suite; use (hash-bench::run-full) for ~
           the real thing.~%")
(run-quick)
