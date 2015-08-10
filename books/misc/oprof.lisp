;; Simple Profiler for OpenMCL -- ACL2 Interface
;;
;; Written in 2008 by Jared Davis <jared@cs.utexas.edu>.  This code
;; is in the public domain and may be freely used and copied without
;; restriction.

;; Basic Usage:
;;
;;   1. Choose the functions to profile:  (oprof.watch '(foo bar baz))
;;   2. Run the code you want to profile over.
;;   3. Print the report: (oprof.report)
;;
;; You may also find these functions useful:
;;
;;   (oprof.clear)              -- resets all times to zero, but keeps profiling
;;                                 the current functions.
;;
;;   (oprof.stop)               -- turns off profiling for all functions
;;
;;   (oprof.unwatch '(foo bar)) -- turns off profiling for foo, bar.
;;
;; See below for some examples.  Also note:
;;
;;   1. fast-running functions may have their times unreported since we just
;;      use the get-internal-real-time function, which is not very precise.
;;
;;   2. recursive calls are often inlined in OpenMCL and will not affect the
;;      call count.
;;

(in-package "ACL2")

(defun oprof.watch (fns)
  (declare (xargs :guard t) (ignore fns))
  #+openmcl
  (cw "Error: oprof.watch has not been redefined.~%")
  #-openmcl
  (cw "Error: oprof is only available on OpenMCL.~%"))

(defun oprof.unwatch (fns)
  (declare (xargs :guard t) (ignore fns))
  #+openmcl
  (cw "Error: oprof.unwatch has not been redefined.~%")
  #-openmcl
  (cw "Error: oprof is only available on OpenMCL.~%"))

(defun oprof.clear ()
  (declare (xargs :guard t))
  #+openmcl
  (cw "Error: oprof.clear has not been redefined.~%")
  #-openmcl
  (cw "Error: oprof is only available on OpenMCL.~%"))

(defun oprof.report ()
  (declare (xargs :guard t))
  #+openmcl
  (cw "Error: oprof.report has not been redefined.~%")
  #-openmcl
  (cw "Error: oprof is only available on OpenMCL.~%"))

(defun oprof.stop ()
  (declare (xargs :guard t))
  #+openmcl
  (cw "Error: oprof.stop has not been redefined.~%")
  #-openmcl
  (cw "Error: oprof is only available on OpenMCL.~%"))

(defttag oprof)

#+openmcl
(progn!
 (set-raw-mode t)
 (load (extend-pathname (cbd-fn *the-live-state*) "oprof-raw.lsp" *the-live-state*)))



#|

;; Some examples.

(include-book
 "oprof"
 :ttags '(oprof))

(defun fib (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      1
    (if (= n 1)
        1
      (+ (fib (- n 1)) (fib (- n 2))))))

(defun fib2 (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      1
    (if (= n 1)
        1
      (+ (fib2 (- n 1)) (fib2 (- n 2))))))

:q

(oprof.watch '(fib fib2))

;; Example 1.  There is some time loss when executing very fast functions.  This
;; is because oprof does not measure time very precisely.  Note also that OpenMCL
;; has optimized away the interior, recursive calls of fib, so you only see the
;; number of times it was called externally.

(time$ (loop for i fixnum from 1 to 100000 do (fib 5)))  ;; time$ says 0.329 seconds
(oprof.report)                                           ;; oprof says 0.17  seconds
(oprof.clear)


;; Example 2.  The time loss is not so severe on slower-executing functions.

(time$ (loop for i fixnum from 1 to 100000 do (fib 20))) ;; time$ says 30.07 seconds
(oprof.report)                                           ;; oprof says 29.92 seconds
(oprof.clear)

;; Example 3.  You can profile more than one function at a time.

(time$ (loop for i from 1 to 100000 do  ;; time$ says 41.76 seconds
             (fib 20)                   ;; oprof says 29.91 seconds for fib
             (fib2 18)))                ;; oprof says 11.50 seconds for fib2

(oprof.stop)

|#