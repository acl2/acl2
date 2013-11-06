(defvar *sneaky-state*
  (make-hash-table))

;; (defun sneaky-save (name what)
;;   (setf (gethash name *sneaky-load-table*) what)
;;   nil)

;; (defun sneaky-push (name what)
;;   (let ((val (gethash name *sneaky-load-table*)))
;;     (setf (gethash name *sneaky-load-table*)
;;           (cons what val)))
;;   nil)

;; (defun sneaky-incf-fn (name amount)
;;   (setf (gethash name *sneaky-load-table*)
;;         (+ (fix (gethash name *sneaky-load-table*))
;;            amount))
;;   nil)

(defun sneaky-load (name state)
  (unless (live-state-p state)
    (er hard? 'sneaky-load "sneaky-load should only be used on live states"))
  (let ((val (gethash name *sneaky-state*)))
    (mv val state)))

(defun sneaky-alist (state)
  (unless (live-state-p state)
    (er hard? 'sneaky-load "sneaky-load should only be used on live states"))
  (let (al)
    (maphash (lambda (k v)
               (push (cons k v) al))
             *sneaky-state*)
    (mv al state)))


(defun sneaky-mutate (fnname get-keys user-arg)
  (b* ((st *the-live-state*)
       (world (w st))
       (stobjs-in (fgetprop fnname 'stobjs-in :none world))
       (stobjs-out (fgetprop fnname 'stobjs-out :none world))
       ((when (not (equal stobjs-in '(nil nil))))
        (er hard 'sneaky-mutate
            "FNNAME must be an ACL2 function symbol of 2 non-stobj args; ~x0 is not~%"
            fnname))
       ((when (not (equal stobjs-out '(nil))))
        (er hard 'sneaky-mutate
            "FNNAME must be an ACL2 function symbol that returns a single value; ~x0 is not~%"
            fnname))
       (get-ins (loop for key in get-keys collect
                      (gethash key *sneaky-state*)))
       (starfn (*1*-symbol fnname))
       (result (funcall starfn get-ins user-arg)))
    (loop while (consp result) do
          (b* ((head (car result)))
            (when (consp head)
              (setf (gethash (car head) *sneaky-state*) (cdr head)))
            (setq result (cdr result))))
    nil))
