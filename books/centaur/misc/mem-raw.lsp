; Low level memory management utilities
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")



(defun mem-do-run-gc-hook ()
  (mem-gc-hook *the-live-state*)
  nil)

#+Clozure
(ccl::add-gc-hook
 #'(lambda ()
     (ccl::process-interrupt
      (slot-value ccl:*application* 'ccl::initial-listener-process)
      #'mem-do-run-gc-hook))
 :post-gc)


(defun mem-get-used-bytes (state)
  ;; Logic: Returns (MV ER BYTES STATE)
  ;;  - ER must be a Boolean
  ;;  - BYTES must be a Natural
  (unless (live-state-p state)
    (er hard? 'mem-get-used-bytes "Live state required"))

  #+Clozure
  (let ((ret (ccl::%usedbytes)))
    (if (natp ret)
        (mv nil ret state)
      (er hard? 'mem-get-used-bytes
          "ccl::%usedbytes didn't return a natural?")))

  #-Clozure
  (prog2$
   (cw "; Note: mem-get-used-bytes not implemented on this Lisp.~%")
   (mv nil 0 state)))


(defun mem-get-free-bytes (state)
  ;; Logic: Returns (MV ER BYTES STATE)
  ;;  - ER must be a Boolean
  ;;  - BYTES must be a Natural
  (unless (live-state-p state)
    (er hard? 'mem-get-free-bytes "Live state required"))

  #+Clozure
  (let ((ret (ccl::%freebytes)))
    (if (natp ret)
        (mv nil ret state)
      (er hard? 'mem-get-free-bytes
          "ccl::%freebytes didn't return a natural?")))

  #-Clozure
  (prog2$
   (cw "; Note: mem-get-free-bytes not implemented on this Lisp.~%")
   (mv nil 0 state)))


(defun mem-get-gc-threshold (state)
  ;; Logic: Returns (MV ER BYTES STATE)
  ;;  - ER must be a Boolean
  ;;  - BYTES must be a Natural
  (unless (live-state-p state)
    (er hard? 'mem-get-gc-threshold "Live state required"))

  #+Clozure
  (let ((ret (ccl::lisp-heap-gc-threshold)))
    (if (natp ret)
        (mv nil ret state)
      (er hard? 'mem-get-gc-threshold
          "ccl::lisp-heap-gc-threshold didn't return a natural?")))

  #-Clozure
  (prog2$
   (cw "; Note: mem-get-gc-threshold not implemented on this Lisp.~%")
   (mv nil 0 state)))


(defun mem-set-gc-threshold (threshold)
  ;; Logic: Returns NIL

  #+Clozure
  (ccl::set-lisp-heap-gc-threshold threshold)

  #-Clozure
  (cw "; Note: mem-set-gc-threshold not implemented on this Lisp.~%")

  nil)


(defun mem-use-gc-threshold ()
  ;; Logic: Returns NIL

  #+Clozure
  (ccl::use-lisp-heap-gc-threshold)

  #-Clozure
  (cw "; Note: mem-use-gc-threshold not implemented on this Lisp.~%")

  nil)


(defun mem-get-egc (state)
  ;; Logic: Returns (MV ER ENABLED-P STATE)
  ;;  - ER must be Boolean
  ;;  - ENABLED-P must be Boolean
  (unless (live-state-p state)
    (er hard? 'mem-get-egc "Live state required"))

  #+Clozure
  (let ((ret (ccl::egc-enabled-p)))
    (if (booleanp ret)
        (mv nil ret state)
      (er hard? 'mem-get-egc
          "ccl::egc-enabled-p didn't return a Boolean?")))

  #-Clozure
  (progn
    (cw "; Note: mem-get-egc not implemented on this Lisp.~%")
    (mv nil nil state)))


(defun mem-set-egc (enabled-p)
  ;; Logic: Returns NIL

  #+Clozure
  (ccl::egc enabled-p)

  #-Clozure
  (cw "; Note: mem-set-egc not implemented on this Lisp.~%")

  nil)




