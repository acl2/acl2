; A tool to make a clause processor that uses an Axe Prover
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Rename this book, since the clause processor function itself must already exist.  Should make-prover-simple (optionally) just do this stuff?

;; This machinery requires a TTAG, due to the use of define-trusted-clause-processor.

(include-book "kestrel/utilities/pack" :dir :system)

;; Returns an event
(defun make-clause-processor-simple-fn (suffix ;; gets added to generated names
                                        )
  (declare (xargs :guard (symbolp suffix)))
  (let* ((clause-processor-name (pack$ 'prover- suffix '-clause-processor)) ; should already be defined
         (defthm-with-clause-processor-fn-name (pack$ 'defthm-with- clause-processor-name '-fn))
         (defthm-with-clause-processor-name (pack$ 'defthm-with- clause-processor-name)))

    `(encapsulate ()

       ;; See also the define-trusted-clause-processor in prover2.lisp.
       (define-trusted-clause-processor
         ,clause-processor-name
         nil ;supporters ; todo: Think about this (I don't understand what :doc define-trusted-clause-processor says about "supporters")
         :ttag ,clause-processor-name)

       ;; Returns a defthm event.
       (defun ,defthm-with-clause-processor-fn-name (name term tactic rules rule-lists remove-rules use no-splitp rule-classes count-hits print state)
         (declare (xargs :guard (and (symbolp name)
                                     ;; term need not be translated
                                     (or (null tactic)
                                         (simple-prover-tacticp tactic))
                                     (rule-item-listp rules)
                                     (rule-item-list-listp rule-lists)
                                     (symbol-listp remove-rules) ;allow rule-items?
                                     (axe-use-hintp use)
                                     (booleanp no-splitp)
                                     ;; todo: rule-classes
                                     (booleanp count-hits)
                                     (print-levelp print))
                         :stobjs state))
         (b* (((when (and rules rule-lists))
               (er hard? ',defthm-with-clause-processor-fn-name "Both :rules and :rule-lists were given for ~x0." name))
              (rule-lists (if rules
                              (list (elaborate-rule-items rules state))
                            (elaborate-rule-item-lists rule-lists state)))
              (rule-lists (remove-from-all rule-lists remove-rules)))
           `(defthm ,name
              ,term
              :hints (("Goal" :clause-processor (,',clause-processor-name clause
                                                                          '((:must-prove . t)
                                                                            (:tactic . ,tactic)
                                                                            ;; no rules, only rule-lists
                                                                            (:rule-lists . ,rule-lists)
                                                                            (:no-splitp . ,no-splitp)
                                                                            ;; todo print-as-clausesp
                                                                            ;; todo no-print-fns
                                                                            ;; todo monitor
                                                                            (:use . ,use)
                                                                            (:print . ,print)
                                                                            ;; todo var-ordering
                                                                            (:count-hits . ,count-hits))
                                                                          state)))
              ,@(if (eq :auto rule-classes)
                    nil
                  `(:rule-classes ,rule-classes)))))

       ;; Submit a defthm that uses the clause-processor:
       (defmacro ,defthm-with-clause-processor-name (name
                                                     term
                                                     &key
                                                     (tactic '(:rep :rewrite :subst))
                                                     (rules 'nil)
                                                     (rule-lists 'nil)
                                                     (remove-rules 'nil)
                                                     (no-splitp 'nil) ; whether to prevent splitting into cases
                                                     (use 'nil)
                                                     (print 'nil)
                                                     (count-hits 'nil)
                                                     (rule-classes ':auto))
         (if (and (consp term)
                  (eq :eval (car term)))
             ;; Evaluate TERM:
             `(make-event (,',defthm-with-clause-processor-fn-name ',name ,(cadr term) ',tactic ',rules ',rule-lists ',remove-rules ',use ',no-splitp ',rule-classes ',count-hits ',print state))
           ;; Don't evaluate TERM:
           `(make-event (,',defthm-with-clause-processor-fn-name ',name ',term ',tactic ',rules ',rule-lists ',remove-rules ',use ',no-splitp ',rule-classes ',count-hits ',print state))))

       )))

(defmacro make-clause-processor-simple (suffix)
  (make-clause-processor-simple-fn suffix))
