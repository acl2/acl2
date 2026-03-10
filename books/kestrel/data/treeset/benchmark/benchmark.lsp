; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "../set-defs")
(include-book "../in-defs")
(include-book "../cardinality-defs")
(include-book "../insert-defs")
(include-book "../delete-defs")
(include-book "../union-defs")

(include-book "random")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This file was written with significant input from Claude code.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag :benchmarking)
(set-raw-mode t)

(in-package "COMMON-LISP")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun format-duration (seconds)
  (cond ((>= seconds 1)
         (format nil "~,2Fs" seconds))
        ((>= seconds 1/1000)
         (format nil "~,4Fms" (* seconds 1000)))
        (t
         (format nil "~,4Fµs" (* seconds 1000000)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun mk-random-u-fixnum-set (cardinality)
  (multiple-value-bind
   (set state)
   (treeset::mk-random-u-fixnum-set cardinality acl2::state)
   set))

(defun mk-u-fixnum-list-in-prob (length prob set)
  (multiple-value-bind
   (list state)
   (treeset::mk-u-fixnum-list-in-prob length prob set acl2::state)
   list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun benchmark-u-fixnum-set-in-=
  (cardinality
   &key
   (prob 1/2)
   (batch-size 10000)
   (num-batches 51))
  (let* ((set (mk-random-u-fixnum-set cardinality))
         (times
           (loop repeat num-batches
                 for elems = (mk-u-fixnum-list-in-prob batch-size prob set)
                 do (sb-ext:gc :full t)
                 collect (let ((start (get-internal-real-time)))
                           (loop for elem in elems
                                 do (treeset::in elem set :test =))
                           (/ (- (get-internal-real-time) start)
                              internal-time-units-per-second
                              batch-size))))
         (sorted (sort (copy-list times) #'<))
         (median (nth (floor num-batches 2) sorted))
         (average (/ (reduce #'+ times) num-batches))
         (variance (/ (loop for time in times
                            sum (expt (- time average) 2))
                      num-batches))
         (std-dev (sqrt variance)))
    (format t "Benchmark: in-=, cardinality=~:D, prob=~,2F~%"
            cardinality
            prob)
    ;; (format t "Times: ~{~A~^, ~}~%"
    ;;         (mapcar #'format-duration sorted))
    (format t "Median time: ~A~%"
            (format-duration median))
    (format t "Average time: ~A~%"
            (format-duration average))
    (format t "Std deviation: ~A~%"
            (format-duration std-dev))
    ))

(defun benchmark-u-fixnum-set-in-=-suite ()
  (dolist (cardinality '(1000 10000 100000 1000000))
    (dolist (prob '(0 1/2 1))
      (benchmark-u-fixnum-set-in-= cardinality :prob prob)
      (terpri))
    (format t ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%~%")))

(compile 'benchmark-u-fixnum-set-in-=)
(compile 'benchmark-u-fixnum-set-in-=-suite)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun benchmark-u-fixnum-set-insert-=
  (cardinality
   &key
   (prob 1/2)
   (batch-size 10000)
   (num-batches 51))
  (let* ((set (mk-random-u-fixnum-set cardinality))
         (times
           (loop repeat num-batches
                 for elems = (mk-u-fixnum-list-in-prob batch-size prob set)
                 do (sb-ext:gc :full t)
                 collect (let ((start (get-internal-real-time)))
                           (loop for elem in elems
                                 do (treeset::insert elem set :test =))
                           (/ (- (get-internal-real-time) start)
                              internal-time-units-per-second
                              batch-size))))
         (sorted (sort (copy-list times) #'<))
         (median (nth (floor num-batches 2) sorted))
         (average (/ (reduce #'+ times) num-batches))
         (variance (/ (loop for time in times
                            sum (expt (- time average) 2))
                      num-batches))
         (std-dev (sqrt variance)))
    (format t "Benchmark: insert-=, cardinality=~:D, prob=~,2F~%"
            cardinality
            prob)
    ;; (format t "Times: ~{~A~^, ~}~%"
    ;;         (mapcar #'format-duration sorted))
    (format t "Median time: ~A~%"
            (format-duration median))
    (format t "Average time: ~A~%"
            (format-duration average))
    (format t "Std deviation: ~A~%"
            (format-duration std-dev))
    ))

(defun benchmark-u-fixnum-set-insert-=-suite ()
  (dolist (cardinality '(1000 10000 100000 1000000))
    (dolist (prob '(0 1/2 1))
      (benchmark-u-fixnum-set-insert-= cardinality :prob prob)
      (terpri))
    (format t ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%~%")))

(compile 'benchmark-u-fixnum-set-insert-=)
(compile 'benchmark-u-fixnum-set-insert-=-suite)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun benchmark-u-fixnum-set-delete-=
  (cardinality
   &key
   (prob 1/2)
   (batch-size 10000)
   (num-batches 51))
  (let* ((set (mk-random-u-fixnum-set cardinality))
         (times
           (loop repeat num-batches
                 for elems = (mk-u-fixnum-list-in-prob batch-size prob set)
                 do (sb-ext:gc :full t)
                 collect (let ((start (get-internal-real-time)))
                           (loop for elem in elems
                                 do (treeset::delete elem set :test =))
                           (/ (- (get-internal-real-time) start)
                              internal-time-units-per-second
                              batch-size))))
         (sorted (sort (copy-list times) #'<))
         (median (nth (floor num-batches 2) sorted))
         (average (/ (reduce #'+ times) num-batches))
         (variance (/ (loop for time in times
                            sum (expt (- time average) 2))
                      num-batches))
         (std-dev (sqrt variance)))
    (format t "Benchmark: delete-=, cardinality=~:D, prob=~,2F~%"
            cardinality
            prob)
    ;; (format t "Times: ~{~A~^, ~}~%"
    ;;         (mapcar #'format-duration sorted))
    (format t "Median time: ~A~%"
            (format-duration median))
    (format t "Average time: ~A~%"
            (format-duration average))
    (format t "Std deviation: ~A~%"
            (format-duration std-dev))
    ))

(defun benchmark-u-fixnum-set-delete-=-suite ()
  (dolist (cardinality '(1000 10000 100000 1000000))
    (dolist (prob '(0 1/2 1))
      (benchmark-u-fixnum-set-delete-= cardinality :prob prob)
      (terpri))
    (format t ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%~%")))

(compile 'benchmark-u-fixnum-set-delete-=)
(compile 'benchmark-u-fixnum-set-delete-=-suite)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: This is currently using successive nats instead of random words.
;; Fix that.
;; (The non-overlapping case is misleading quick, because it can be just
;; "inserted")
(defun mk-u-fixnum-set-pair-overlap (cardinality-1 cardinality-2 overlap)
  (let* ((shared-count (floor (* cardinality-2 overlap)))
         (set1-only (- cardinality-1 shared-count))
         (set2-only (- cardinality-2 shared-count))
         ;; Generate disjoint pools of numbers
         (shared (loop for i below shared-count collect i))
         (pool1 (loop for i from shared-count below (+ shared-count set1-only) collect i))
         (pool2 (loop for i from (+ shared-count set1-only)
                      below (+ shared-count set1-only set2-only) collect i))
         (set1 (treeset::from-list (append shared pool1)))
         (set2 (treeset::from-list (append shared pool2))))
    (cons set1 set2)))

(defun benchmark-u-fixnum-set-union-=
  (cardinality-1
   cardinality-2
   &key
   (overlap 0)  ; 0 = disjoint, 1 = identical
   (batch-size 100)
   (num-batches 51))
  (let* ((times
           (loop repeat num-batches
                 for set-pairs = (loop repeat batch-size
                                       collect (mk-u-fixnum-set-pair-overlap
                                                cardinality-1 cardinality-2 overlap))
                 do (sb-ext:gc :full t)
                 collect (let ((start (get-internal-real-time)))
                           (loop for (set1 . set2) in set-pairs
                                 do (treeset::union set1 set2 :test =))
                           (/ (- (get-internal-real-time) start)
                              internal-time-units-per-second
                              batch-size))))
         (sorted (sort (copy-list times) #'<))
         (median (nth (floor num-batches 2) sorted))
         (average (/ (reduce #'+ times) num-batches))
         (variance (/ (loop for time in times
                            sum (expt (- time average) 2))
                      num-batches))
         (std-dev (sqrt variance)))
    (format t "Benchmark: union-=, card1=~:D, card2=~:D, overlap=~,2F~%"
            cardinality-1 cardinality-2 overlap)
    (format t "Median time: ~A~%"
            (format-duration median))
    (format t "Average time: ~A~%"
            (format-duration average))
    (format t "Std deviation: ~A~%"
            (format-duration std-dev))))

(defun benchmark-u-fixnum-set-union-=-suite ()
  (dolist (cardinality '(100 1000 10000
                         ))
    (dolist (overlap '(0 1/2 1))
      (benchmark-u-fixnum-set-union-= cardinality cardinality :overlap overlap)
      (terpri))
    (format t ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%~%")))

(compile 'benchmark-u-fixnum-set-union-=)
(compile 'benchmark-u-fixnum-set-union-=-suite)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun benchmark-suite ()
  (benchmark-u-fixnum-set-in-=-suite)
  (format t ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%~%")
  (benchmark-u-fixnum-set-insert-=-suite)
  (format t ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%~%")
  (benchmark-u-fixnum-set-delete-=-suite)
  (format t ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%~%")
  (benchmark-u-fixnum-set-union-=-suite)
  (format t ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;~%~%"))

(compile 'benchmark-suite)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(benchmark-suite)
