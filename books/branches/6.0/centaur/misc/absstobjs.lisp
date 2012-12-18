
(in-package "ACL2")

(include-book "tools/bstar" :dir :system)

(defun defabsstobj-missing-defthms-untrans (forms state)
  (declare (xargs :mode :program :stobjs state))
  (if (atom forms)
      nil
    (cons `(defthm ,(caar forms)
             ,(untranslate (cadar forms) t (w state))
             :rule-classes nil)
          (defabsstobj-missing-defthms-untrans (cdr forms) state))))

(defun defabsstobj-missing-defthms-fn (st-name st$c recognizer creator corr-fn
                                               exports protect-default
                                               congruent-to doc event-form
                                               state)
  (declare (xargs :mode :program :stobjs state))
  (b* (((er &) (set-ld-redefinition-action '(:doit . :overwrite) state))
       ((er forms) (defabsstobj-fn1
                     st-name st$c recognizer creator corr-fn exports
                     protect-default congruent-to t doc
                     (msg "( DEFABSSTOBJ-MISSING-DEFTHMS ~x0 ...)" st-name)
                     state event-form))
       (defthms (defabsstobj-missing-defthms-untrans forms state)))
    (value (cons 'progn defthms))))
      
(defmacro defabsstobj-missing-defthms 
  (&whole event-form
          name
          &key
          concrete recognizer creator
          corr-fn exports protect-default congruent-to doc)
  (list 'make-event
        (list 'defabsstobj-missing-defthms-fn
              (list 'quote name)
              (list 'quote concrete)
              (list 'quote recognizer)
              (list 'quote creator)
              (list 'quote corr-fn)
              (list 'quote exports)
              (list 'quote protect-default)
              (list 'quote congruent-to)
              (list 'quote doc)
              (list 'quote event-form)
              'state)))

(defmacro defabsstobj-events (&rest args)
  `(progn (local (defabsstobj-missing-defthms . ,args))
          (defabsstobj . ,args)))
