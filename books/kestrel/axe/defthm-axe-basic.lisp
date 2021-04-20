; A simple variant of defthm-axe
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "prover-basic-clause-processor")

;; Returns an event.
(defun defthm-axe-basic-fn (name term rules rule-lists remove-rules rule-classes print state)
  (declare (xargs :guard (and (rule-item-listp rules)
                              (rule-item-list-listp rule-lists)
                              (symbol-listp remove-rules)
                              ;; print
                              )
                  :stobjs state))
  (b* (((when (and rules rule-lists))
        (er hard? 'defthm-axe-basic-fn "Both :rules and :rule-lists were given for ~x0." name))
       (rule-lists (if rules
                       (list (elaborate-rule-items rules nil state))
                     (elaborate-rule-item-lists rule-lists state)))
       (rule-lists (remove-from-all rule-lists remove-rules)))
    `(defthm ,name
       ,term
       :hints (("Goal" :clause-processor (basic-prover-clause-processor clause
                                                                      '((:must-prove . t)
                                                                        (:rule-lists . ,rule-lists)
                                                                        (:print . ,print))
                                                                      state)))
       ,@(if (eq :auto rule-classes)
             nil
           `(:rule-classes ,rule-classes)))))

;; Prove a theorem with the Axe Prover, throwing an error if it fails.
(defmacro defthm-axe-basic (name term
                           &key
                           (rules 'nil)
                           (rule-lists 'nil)
                           (remove-rules 'nil)
                           (rule-classes ':auto)
                           (print 'nil))
  (if (and (consp term)
           (eq :eval (car term)))
      ;; Evaluate TERM:
      `(make-event (defthm-axe-basic-fn ',name ,(cadr term) ',rules ',rule-lists ',remove-rules ',rule-classes ',print state))
    ;; Don't evaluate TERM:
    `(make-event (defthm-axe-basic-fn ',name ',term ',rules ',rule-lists ',remove-rules ',rule-classes ',print state))))
