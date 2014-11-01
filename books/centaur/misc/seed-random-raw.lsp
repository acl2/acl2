

(defparameter *random-seeds* nil)

(defun seed-random$-fn (name freshp)
  (let ((look (assoc-equal name *random-seeds*)))
    (cond (look
           ;;(format t "Restoring *random-state* to ~a.~%" (cdr look))
           (setq *random-state* (make-random-state (cdr look))))
          (freshp
           (let* ((new-st (make-random-state t)))
             ;;(format t "Fresh seed ~a: ~a.~%" name new-st)
             (setq *random-seeds* (acons name new-st *random-seeds*))
             (setq *random-state* (make-random-state new-st))))
          (t
           (let ((new-st (make-random-state nil)))
             ;;(format t "Copy seed to ~a: ~a.~%" name new-st)
             (setq *random-seeds* (acons name new-st *random-seeds*))))))
  nil)
