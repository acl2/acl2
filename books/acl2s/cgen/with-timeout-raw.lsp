;Author: Harsh Raju Chamarthi, Matt Kaufmann
;Acknowledgements: Thanks to Gary Byers, Gary Warren King, Bob Boyer,
;David Rager
;

(in-package "ACL2")


;; ;Taken from memoize-raw.lisp 
;; #+Clozure
;; (defun make-watchdog (duration)
;; ;   Thanks to Gary Byers for this!

;;    (let* ((done (ccl:make-semaphore))
;;           (current ccl:*current-process*))
;;       (ccl::process-run-function "watchdog"
;;         (lambda ()
;;           (or (ccl:timed-wait-on-semaphore done duration)
;;               (ccl:process-interrupt
;;                current #'timeout-hard-error 'with-timeout
;;                                  '"Time exceeded"
;;                                  'nil *the-live-state*))))
;;       done)) 

;; (defmacro with-timeout-raw (duration body) ;duration in seconds
;; #+Clozure
;; `(let* ((semaphore (make-watchdog ,duration)))
;;    (unwind-protect
;;        ,body
;;      (ccl:signal-semaphore semaphore)))

;; #+sb-thread ;Thanks to Gary Warren King for this!
;;   `(handler-case 
;;     (sb-ext:with-timeout ,duration ,body)
;;     (sb-ext::timeout (c)
;;                      (declare (ignore c))
;;                      (timeout-hard-error 'with-timeout
;;                              '"Time exceeded"
;;                              'nil *the-live-state*)))

;;)

;harshrc: Thanks to Matt for the following email snippet whose ideas
;I used to implement nested timeouts.

;; I think you know how to write a function (timer n) that causes an
;; error after n seconds.  Presumably you could write it so that instead
;; of (er hard ...), it does (throw 'timeout-tag *timeout-val*).

;i need `throw' to be be a function to be used in process-interrupt,
;so had to define the following. Does that screw the semantics of
;usage of macro throw?
(defun throw1 (tag form)
  (throw tag form))

#+Clozure
(defun make-watchdog (duration id)
;   Thanks to Gary Byers for this! --adapted from memoize-raw.lisp

   (let* ((done (ccl:make-semaphore))
          (current ccl:*current-process*))
      (ccl::process-run-function "watchdog"
        (lambda ()
          (or (ccl:timed-wait-on-semaphore done duration)
              (ccl:process-interrupt
               current #'throw1 id id))))
      done))

(defmacro with-timeout-raw (duration id body) ;duration

; Note: all args are expressions that are expected to be evaluated.

  ;; duration in seconds with
  ;; id which is a unique timeout identifier
  #+Clozure
  `(let ((semaphore (make-watchdog ,duration ',id))
;close the environment
         ;(closure #'(lambda () ,body))
         )
     (unwind-protect
         ;(funcall closure)
         ,body
       (ccl:signal-semaphore semaphore)))

  #+sb-thread ;Thanks to Gary Warren King for this!
  `(handler-case 
    (sb-ext:with-timeout ,duration ,body)
    (sb-ext::timeout (c)
                     (declare (ignore c))
                     (throw1 ',id ',id)))

  #-(or Clozure sb-thread)
  '(error "Unsupported host Lisp for CGEN (only CCL and multi-threaded SBCL ~
           are supported)."))

; For debugging
#||
(defmacro catch1 (tag arg)
  `(progn (format t "Set up catcher: ~s~%" '(,tag ,arg))
          (let ((vals (catch ,tag (multiple-value-list ,arg))))
            (format t "Catcher worked:~%~s~%" vals)
            vals)))
||#

(defmacro catch1 (tag arg)
  `(catch ,tag (multiple-value-list ,arg)))

#|

  Pete note on with-timeout-aux-raw.

  I added the (handler-case ... (error (c) ',timeout-id)) code.

  This change allows us to hide any errors that may be generated
  during the counterexample generation process. The idea of
  counterexample generation is to look for errors in the form of
  counterexamples and to report such errors to users of the theorem
  prover, but to otherwise introduce minimal disruptions in the
  theorem proving process.

  Why might counterexample generation disrupt the theorem proving
  process? Well, consider evaluating a function that is exponential
  time, say fib, on large numbers. We do not want this process to use
  significant resources, such as time and space. The use of timeouts
  helps to ameliorate this issue. But, it will not help if we exhaust
  memory or if common lisp throws an error. Here is an example from
  ACL2 built using SBCL. First, some trivial theorems.

  (defthm foo (implies (natp  x) (natp (expt 2 x))))
  (in-theory (disable natp))
  (defthm bar (implies (natp  x) (natp (expt 2 (expt 2 x)))))

  Now, since bar is a theorem, what we might expect is that evaluating
  the body of bar, after replacing the variables by any constant will
  evaluate to t. Let's try it.

  (let ((x 1000000)) (implies (natp  x) (natp (expt 2 (expt 2 x)))))

  That leads to an error. Here is what SBCL reports.

  ************ ABORTING from raw Lisp ***********
  ********** (see :DOC raw-lisp-error) **********
  Error:  can't represent result of left shift
  ***********************************************

  The issue is that SBCL, in the process of evaluating expt evaluates
  bignum-ashift-left, which checks that we are not shifting by a very
  large number, since that will lead to a number not representable
  with existing memory. That check leads to the above error. Note that
  the following thm leads to a similar error:

  (thm (natp (expt 2 (expt 2 1000000))))

  As does the following.

  (test? (natp (expt 2 (expt 2 1000000))))

  This is the kind of thing that can happen when we are generating
  counterexamples. 

  Note that we can prove the above and bypass evaluation, eg, with this:

  (thm (natp (expt 2 (expt 2 1000000)))
    :hints (("Goal" :use (:instance bar (x 1000000)))))

  Anyway, the current implementation will catch such errors, but it is
  still possible for fatal, non-recoverable errors to occur. An
  example is discussed below.

  Potential improvements include the following.

  1. Add support for tracking other resources such as space. To this
  end, the oracle-timelimit book in [books]/tools/ might be
  useful. The motivation for this is that some code can very quickly
  exhaust available memory, before timeouts kick in. I've seen cases
  where this just leads SBCL errors such as:

  fatal error encountered in SBCL pid 36112 pthread 0xaaf5600:
  Heap exhausted, game over.

  This error causes ACL2 to die, so it is not great. If you see this,
  limit the number of counterexamples, time for counterexamples,
  etc. using (acl2s-defaults :set num-witnesses/ cgen-local-timeout/
  cgen-timeout ...) forms. A better approach may be to use definec and
  defdata to define the right types. If that is not a viable option,
  one can use different enumerators, which can be attached
  dynamically. 

  2. Collect information and statistics on the types of errors that
  occur. Then analyze it and provide useful info to users.


|#


(defmacro with-timeout-aux-raw (&whole whole duration/timeout-form body)
  (case-match duration/timeout-form
    (('quote (duration timeout-form))
     (let ((timeout-id (acl2-gentemp "WITH-TIMEOUT$")))
       `(let ((vals (handler-case 
                        (catch1 ',timeout-id
                                (with-timeout-raw ,duration
                                                  ,timeout-id
                                                  ,body))
                      (error (c) ',timeout-id))))
          (cond ((eq vals ',timeout-id)
                 ,timeout-form)
                (t (values-list vals))))))
    (& (error "Illegal call in with-timeout-aux-raw:~%~s~%" whole))))

#|

Previous version.

(defmacro with-timeout-aux-raw (&whole whole duration/timeout-form body)
  (case-match duration/timeout-form
    (('quote (duration timeout-form))
     (let ((timeout-id (acl2-gentemp "WITH-TIMEOUT$")))
       `(let ((vals (catch1 ',timeout-id
                            (with-timeout-raw ,duration
                                              ,timeout-id
                                              ,body))))
          (cond ((eq vals ',timeout-id)
                 ,timeout-form)
                (t (values-list vals))))))
    (& (error "Illegal call in with-timeout-aux-raw:~%~s~%" whole))))
|#
