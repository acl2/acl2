
(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)

(defun untrans-defabsstobj-missing-defthms (forms state)
  (declare (xargs :mode :program :stobjs state))
  (if (atom forms)
      nil
    (cons `(defthm ,(caar forms)
             ,(untranslate (cadar forms) t (w state))
             :rule-classes nil)
          (untrans-defabsstobj-missing-defthms (cdr forms) state))))


(defmacro defabsstobj-events (&rest args)
  `(progn
     (local
      (make-event
       (er-let* ((events (defabsstobj-missing-events . ,args)))
                (let ((thms (untrans-defabsstobj-missing-defthms events state)))
                  (value (cons 'progn thms))))))
     (defabsstobj . ,args)))


