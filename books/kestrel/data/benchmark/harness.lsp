; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A generic micro-benchmark harness, in raw Common Lisp (SBCL).
;
; This file is not a certifiable book. It is intended to be loaded with
; cl:load from within an ACL2 session which has entered raw mode (via a
; trust tag and set-raw-mode), after including the -defs books whose raw
; (:exec) definitions are to be measured.
;
; A benchmark is a plist ("spec") with entries:
;   :name         string; identifies the operation being measured
;   :class        string; input class (e.g. "string", "bignum")
;   :size         integer; input size along whatever axis is natural
;   :setup        thunk returning a simple-vector of inputs
;   :op           function of one input
;   :bytes-per-op optional; input bytes consumed per call, for MB/s
;
; Methodology:
;   - The inner iteration count is calibrated so that one timed region
;     takes roughly *target-region-ms*, and is confirmed by a second
;     region at the same count, so that a single region inflated by
;     system noise cannot end calibration early.
;   - Results are written to a special variable sink so that calls
;     cannot be elided.
;   - Warmup samples are discarded; a full GC precedes each sample (or
;     each round; see run-specs); real time, run time, and bytes consed
;     are recorded per sample. Real time is the primary metric; the OS
;     may quantize run (CPU) time coarsely relative to the region size.
;   - Inputs are cycled from a pre-generated vector, so measurements are
;     cache-hot after the first pass, except for corpora larger than the
;     last-level cache. An operation which conses may trigger GC inside
;     a timed region; for such operations bytes consed per call is the
;     stable metric, and min-ns understates the true cost.
;   - Statistics reported are min, median, and median absolute
;     deviation. Timing distributions are right-skewed, so mean and
;     standard deviation are not reported. Per-sample raw data can be
;     written with write-samples.
;   - When several specs are run together, their samples are interleaved
;     round-robin so that clock frequency and thermal drift do not bias
;     any one spec.
;   - Randomness is seeded explicitly (see init-random), and corpora are
;     generated under sub-seeds keyed by name (see corpus), so runs are
;     reproducible and no corpus depends on what else runs.
;
; Results accumulate in *results* and are written as CSV, prefixed by a
; commented metadata block (seed, git revision, host, CPU, Lisp), by
; write-results.

(defpackage "BENCH"
  (:use "COMMON-LISP")
  (:export "*SINK*"
           "*RESULTS*"
           "*SEED*"
           "*SAMPLES*"
           "*WARMUP*"
           "*TARGET-REGION-MS*"
           "INIT-RANDOM"
           "INPUTS-VECTOR"
           "CORPUS"
           "SPEC"
           "RUN-SPECS"
           "CLEAR-RESULTS"
           "WRITE-RESULTS"
           "WRITE-SAMPLES"
           "PRINT-RESULTS"))

(in-package "BENCH")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Configuration and state

(defvar *sink* nil
  "Dumping ground for operation results, so calls cannot be elided.")

(defvar *results* nil
  "Accumulated result rows, most recent first.")

(defvar *seed* 0
  "Seed of the most recent init-random, recorded in output metadata.")

(defvar *samples* 30)
(defvar *warmup* 3)
(defvar *target-region-ms* 20)

(defun init-random (seed)
  "Seed the PRNG so that input generation is reproducible."
  (setq *seed* seed)
  (setq *random-state* (sb-ext:seed-random-state seed))
  seed)

(defun clear-results ()
  (setq *results* nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Specs

(defun spec (name class size setup op &key bytes-per-op)
  (list :name name
        :class class
        :size size
        :setup setup
        :op op
        :bytes-per-op bytes-per-op))

(defun inputs-vector (n gen)
  "A simple-vector of n inputs drawn from the thunk gen."
  (let ((v (make-array n)))
    (dotimes (i n v)
      (setf (svref v i) (funcall gen)))))

(defun subseed (key)
  "A sub-seed derived from *seed* and a key string (FNV-1a over the
   key, mixed with the seed)."
  (let ((h 2166136261))
    (loop for ch across key
          do (setq h (logand #xFFFFFFFF
                             (* 16777619 (logxor h (char-code ch))))))
    (logxor h *seed*)))

(defun corpus (key n gen)
  "A simple-vector of n inputs drawn from gen under a PRNG state keyed
   by the key string. Two corpora with the same key and n hold identical
   inputs regardless of what else has drawn randomness, so specs which
   should be measured on identical input streams need only agree on the
   key, and adding or removing specs never perturbs the inputs of the
   rest."
  (let ((*random-state* (sb-ext:seed-random-state (subseed key))))
    (inputs-vector n gen)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Measurement

(defun time-region (op inputs iters)
  "Apply op to inputs (cyclically) iters times. Returns (values
   real-ticks run-ticks bytes-consed)."
  (declare (type simple-vector inputs)
           (type fixnum iters)
           (type function op))
  (let ((len (length inputs))
        (j 0))
    (declare (type fixnum len j))
    (let ((b0 (sb-ext:get-bytes-consed))
          (c0 (get-internal-run-time))
          (r0 (get-internal-real-time)))
      (loop repeat iters
            do (setf *sink* (funcall op (svref inputs j)))
               (incf j)
               (when (>= j len) (setq j 0)))
      (let ((r1 (get-internal-real-time))
            (c1 (get-internal-run-time))
            (b1 (sb-ext:get-bytes-consed)))
        (values (- r1 r0) (- c1 c0) (- b1 b0))))))

(defun calibrate (op inputs)
  "Double the iteration count until a timed region meets
   *target-region-ms*, confirmed by a second region at the same count.
   Without the confirmation, a single region inflated by system noise
   would end calibration early and leave every sample undersized."
  (let ((target (ceiling (* *target-region-ms* internal-time-units-per-second)
                         1000)))
    (loop for iters = 1 then (* 2 iters)
          do (when (and (>= (nth-value 0 (time-region op inputs iters))
                            target)
                        (>= (nth-value 0 (time-region op inputs iters))
                            target))
               (return iters)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Statistics (over lists of rationals/floats)

(defun median-of-sorted (sorted)
  (let ((n (length sorted)))
    (if (oddp n)
        (nth (floor n 2) sorted)
      (/ (+ (nth (1- (floor n 2)) sorted)
            (nth (floor n 2) sorted))
         2))))

(defun median (xs)
  (median-of-sorted (sort (copy-list xs) #'<)))

(defun mad (xs)
  "Median absolute deviation."
  (let ((med (median xs)))
    (median (mapcar (lambda (x) (abs (- x med))) xs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Runner

(defstruct runstate spec inputs op iters real-ns run-ns bytes)

(defun ticks-to-ns (ticks iters)
  (/ (* ticks 1000000000)
     internal-time-units-per-second
     iters))

(defun sample-once (st &key record)
  (multiple-value-bind (real run bytes)
      (time-region (runstate-op st) (runstate-inputs st) (runstate-iters st))
    (when record
      (let ((iters (runstate-iters st)))
        (push (ticks-to-ns real iters) (runstate-real-ns st))
        (push (ticks-to-ns run iters) (runstate-run-ns st))
        (push (/ bytes iters) (runstate-bytes st))))))

(defun result-row (st)
  (let* ((spec (runstate-spec st))
         (reals (runstate-real-ns st))
         (median-ns (median reals))
         (bytes-per-op (getf spec :bytes-per-op)))
    (list :name (getf spec :name)
          :class (getf spec :class)
          :size (getf spec :size)
          :iters (runstate-iters st)
          :samples (length reals)
          :min-ns (float (reduce #'min reals))
          :median-ns (float median-ns)
          :mad-ns (float (mad reals))
          :run-median-ns (float (median (runstate-run-ns st)))
          :bytes-per-call (float (median (runstate-bytes st)))
          :mb-per-sec (and bytes-per-op
                           (plusp median-ns)
                           (float (/ (* bytes-per-op 1000)
                                     median-ns)))
          ;; Raw per-sample data, chronological; not written to the
          ;; results CSV (see *columns*) but available to write-samples.
          :raw-real (reverse reals)
          :raw-run (reverse (runstate-run-ns st))
          :raw-bytes (reverse (runstate-bytes st)))))

(defun run-specs (specs &key (samples *samples*) (warmup *warmup*)
                             (gc :per-sample))
  "Calibrate each spec, then collect samples for all specs in an
   interleaved round-robin order. gc is :per-sample (default; a full GC
   before every timed region) or :per-round (one full GC per round-robin
   round — much faster for large suites, at the cost of each spec's
   samples starting from whatever garbage the previous spec left).
   Records and returns one result row per spec."
  (let ((states
          (mapcar (lambda (spec)
                    (let* ((inputs (funcall (getf spec :setup)))
                           (op (getf spec :op))
                           (iters (calibrate op inputs)))
                      (format t "; calibrated ~A/~A/~A: ~:D iters/sample~%"
                              (getf spec :name)
                              (getf spec :class)
                              (getf spec :size)
                              iters)
                      (finish-output)
                      (make-runstate :spec spec :inputs inputs :op op
                                     :iters iters)))
                  specs)))
    (dotimes (s (+ warmup samples))
      (when (eq gc :per-round)
        (sb-ext:gc :full t))
      (dolist (st states)
        (when (eq gc :per-sample)
          (sb-ext:gc :full t))
        (sample-once st :record (>= s warmup))))
    (let ((rows (mapcar #'result-row states)))
      (dolist (row rows)
        (push row *results*))
      rows)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Metadata

(defvar *source-dir*
  (and *load-truename* (directory-namestring *load-truename*))
  "Directory of this file at load time. Git metadata is queried here so
   that it reflects the repository being measured, not the process cwd.")

(defun cpu-model ()
  (ignore-errors
    (with-open-file (s "/proc/cpuinfo" :if-does-not-exist nil)
      (when s
        (loop for line = (read-line s nil)
              while line
              when (and (>= (length line) 10)
                        (string= "model name" line :end2 10))
                do (return (string-trim
                             " "
                             (subseq line (1+ (position #\: line))))))))))

(defun run-git (args)
  "Trimmed stdout of git run in *source-dir*, or nil on failure or
   empty output."
  (ignore-errors
    (let* ((out (with-output-to-string (o)
                  (apply #'sb-ext:run-program "git" args
                         :search t :output o
                         (and *source-dir*
                              (list :directory *source-dir*)))))
           (trimmed (string-trim '(#\Newline #\Space) out)))
      (and (plusp (length trimmed)) trimmed))))

(defun git-rev ()
  (run-git '("rev-parse" "--short" "HEAD")))

(defun git-dirty-p ()
  ;; Untracked files are ignored: the question is whether the measured
  ;; code differs from the recorded revision.
  (and (run-git '("status" "--porcelain" "--untracked-files=no")) t))

(defun first-file-line (path)
  (ignore-errors
    (with-open-file (s path :if-does-not-exist nil)
      (and s (read-line s nil)))))

(defun cpu-governor ()
  (first-file-line
    "/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor"))

(defun acl2-version ()
  ;; The harness is plain CL, but when it is loaded inside an ACL2
  ;; image, the ACL2 version is worth recording. The acl2-version state
  ;; global is represented in raw Lisp as a special variable in the
  ;; ACL2_GLOBAL_ACL2 package.
  (let ((sym (and (find-package "ACL2_GLOBAL_ACL2")
                  (find-symbol "ACL2-VERSION" "ACL2_GLOBAL_ACL2"))))
    (and sym (boundp sym) (symbol-value sym))))

(defun timestamp ()
  (multiple-value-bind (sec min hr day mon yr) (get-decoded-time)
    (format nil "~4,'0D-~2,'0D-~2,'0DT~2,'0D:~2,'0D:~2,'0D"
            yr mon day hr min sec)))

(defun metadata-lines (&key notes)
  (append
    (list (format nil "# date: ~A" (timestamp))
          (format nil "# host: ~A" (machine-instance))
          (format nil "# cpu: ~A" (or (cpu-model) "unknown"))
          (format nil "# governor: ~A" (or (cpu-governor) "unknown"))
          (format nil "# lisp: ~A ~A"
                  (lisp-implementation-type)
                  (lisp-implementation-version))
          (format nil "# acl2: ~A" (or (acl2-version) "unknown"))
          (format nil "# git-rev: ~A~:[~; (dirty)~]"
                  (or (git-rev) "unknown")
                  (git-dirty-p))
          (format nil "# seed: ~A" *seed*)
          (format nil "# samples: ~A, warmup: ~A, target-region-ms: ~A"
                  *samples* *warmup* *target-region-ms*))
    (and notes (list (format nil "# notes: ~A" notes)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Output

(defparameter *columns*
  '(:name :class :size :iters :samples
    :min-ns :median-ns :mad-ns :run-median-ns :bytes-per-call :mb-per-sec))

(defun format-cell (x)
  (typecase x
    (null "")
    (float (format nil "~,2F" x))
    (t (format nil "~A" x))))

(defun write-results (path &key notes)
  "Write accumulated results to path as CSV with a commented metadata
   header. Returns the truename."
  (ensure-directories-exist path)
  (with-open-file (s path :direction :output
                          :if-exists :supersede
                          :if-does-not-exist :create)
    (dolist (line (metadata-lines :notes notes))
      (write-line line s))
    (format s "~{~(~A~)~^,~}~%" (mapcar #'symbol-name *columns*))
    (dolist (row (reverse *results*))
      (format s "~{~A~^,~}~%"
              (mapcar (lambda (col) (format-cell (getf row col)))
                      *columns*))))
  (truename path))

(defun write-samples (path &key notes)
  "Write per-sample raw data for the accumulated results as CSV in long
   format (one row per sample), for when the summary statistics are not
   enough. Returns the truename."
  (ensure-directories-exist path)
  (with-open-file (s path :direction :output
                          :if-exists :supersede
                          :if-does-not-exist :create)
    (dolist (line (metadata-lines :notes notes))
      (write-line line s))
    (write-line "name,class,size,sample,real-ns,run-ns,bytes-per-call" s)
    (dolist (row (reverse *results*))
      (let ((i -1))
        (mapc (lambda (real run bytes)
                (format s "~A,~A,~A,~D,~,2F,~,2F,~,2F~%"
                        (getf row :name)
                        (getf row :class)
                        (getf row :size)
                        (incf i)
                        (float real)
                        (float run)
                        (float bytes)))
              (getf row :raw-real)
              (getf row :raw-run)
              (getf row :raw-bytes)))))
  (truename path))

(defun print-results ()
  "Print accumulated results as an aligned table."
  (format t "~&~30A ~10A ~8A ~12A ~12A ~10A ~12A ~10A~%"
          "name" "class" "size" "min-ns" "median-ns" "mad-ns"
          "bytes/call" "MB/s")
  (dolist (row (reverse *results*))
    (format t "~30A ~10A ~8A ~12A ~12A ~10A ~12A ~10A~%"
            (getf row :name)
            (getf row :class)
            (getf row :size)
            (format-cell (getf row :min-ns))
            (format-cell (getf row :median-ns))
            (format-cell (getf row :mad-ns))
            (format-cell (getf row :bytes-per-call))
            (format-cell (getf row :mb-per-sec)))))
