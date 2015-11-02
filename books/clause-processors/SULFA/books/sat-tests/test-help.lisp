
(in-package "ACL2")

(include-book "../clause-processors/sat-clause-processor" :ttags (sat sat-cl))
(include-book "../clause-processors/sym-str" :ttags (sat sat-cl))
(set-state-ok t)

(defun sat-status-valid (name property hint-arg $sat state)
  (declare (xargs :stobjs $sat :mode :program))
  (mv-let
   (erp val state)
   (thm-fn property
           state
           `(("Goal" :clause-processor (:function sat :hint ,hint-arg)))
           NIL)
   (declare (ignore erp val))
   (if (eq 'valid (sat-cl-property-status $sat))
       (prog2$ (if name (cw "~x0 is valid~%" name) nil)
               (mv nil `(value-triple 'valid) state))
     (if name
         (mv (msg "ERROR: The property named ~x0 ~
                   was not proven valid by the SAT system.~%"
                  name)
             nil
             state)
       (mv (msg (concat-str "ERROR: The following property was not "
                             "proven valid by the SAT system:~%~x0 ~%")
                property)
           nil
           state)))))

(defun sat-status-invalid (name property hint-arg $sat state)
  (declare (xargs :stobjs $sat :mode :program))
  (mv-let
   (erp val state)
   (thm-fn property
           state
           `(("Goal" :clause-processor (:function sat :hint ,hint-arg)))
           NIL)
   (declare (ignore erp val))
   (if (eq 'invalid (sat-cl-property-status $sat))
       (prog2$ (if name (cw "~x0 is invalid~%" name) nil)
               (mv nil `(value-triple 'invalid) state))
     (if name
         (mv (msg (concat-str "ERROR: The property named ~x0 "
                                "was not proven invalid by the SAT system.~%")
                        name)
             nil
             state)
       (mv (msg (concat-str "ERROR: The following property was not "
                              "proven invalid by the SAT system:~%~x0 ~%")
                      property)
           nil
           state)))))

(defun sat-status-unknown (name property hint-arg $sat state)
  (declare (xargs :stobjs $sat :mode :program))
  (mv-let
   (erp val state)
   (thm-fn property
           state
           `(("Goal" :clause-processor (:function sat :hint ,hint-arg)))
           NIL)
   (declare (ignore erp val))
   (if (eq 'unknown (sat-cl-property-status $sat))
       (prog2$ (if name (cw "~x0 is unknown~%" name) nil)
               (mv nil `(value-triple 'unknown) state))
     (if name
         (mv (msg (concat-str "ERROR: The property named ~x0 "
                              "did not result in UKNOWN status.~%")
                  name)
             nil
             state)
       (mv (msg (concat-str "ERROR: The following property did not result "
                            "in UNKNOWN status:~%~x0 ~%")
                property)
           nil
           state)))))

;; These macros are for proving or disproving a property at
;; the top level.

(defmacro thm-sat-valid (property &key name hint-arg)
  `(make-event
    (sat-status-valid (quote ,name) (quote ,property) (quote ,hint-arg)
                      $sat state)))

(defmacro thm-sat-invalid (property &key name hint-arg)
  `(make-event (sat-status-invalid (quote ,name) (quote ,property)
                                   (quote ,hint-arg) $sat state)))

(defmacro thm-sat-unknown (property &key name hint-arg)
  `(make-event (sat-status-unknown (quote ,name) (quote ,property)
                                   (quote ,hint-arg) $sat state)))

