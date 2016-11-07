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
