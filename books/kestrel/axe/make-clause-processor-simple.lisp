; A tool to make a clause processor that uses an Axe Prover
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

(include-book "kestrel/utilities/pack" :dir :system)

;; Returns an event
(defun make-clause-processor-simple-fn (suffix ;; gets added to generated names
                                        )
  (declare (xargs :guard (symbolp suffix)))
  (let* ((clause-processor-name (pack$ suffix '-prover-clause-processor)) ; should already be defined
         (defthm-with-clause-processor-name (pack$ 'defthm-with- clause-processor-name))
         (defthm-with-clause-processor-fn-name (pack$ 'defthm-with- clause-processor-name '-fn)))

    `(encapsulate ()

       ;; (local (include-book "kestrel/lists-light/nth" :dir :system))
       ;; (local (include-book "kestrel/lists-light/remove-equal" :dir :system))
       ;; (local (include-book "kestrel/lists-light/len" :dir :system))
       ;; (local (include-book "kestrel/lists-light/reverse" :dir :system))
       ;; (local (include-book "kestrel/lists-light/last" :dir :system))
       ;; (local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
       ;; (local (include-book "kestrel/lists-light/take" :dir :system))
       ;; (local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
       ;; (local (include-book "kestrel/lists-light/cons" :dir :system)) ; for true-listp-of-cons
       ;; (local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
       ;; (local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
       ;; (local (include-book "kestrel/arithmetic-light/plus" :dir :system))
       ;; (local (include-book "kestrel/utilities/acl2-count" :dir :system))
       ;; (local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
       ;; (local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

       ;; See also the define-trusted-clause-processor in prover2.lisp.
       (define-trusted-clause-processor
         ,clause-processor-name
         nil ;supporters ; todo: Think about this (I don't understand what :doc define-trusted-clause-processor says about "supporters")
         :ttag ,clause-processor-name)

       ;; Returns a defthm event.
       (defun ,defthm-with-clause-processor-fn-name (name term tactic rules rule-lists remove-rules no-splitp rule-classes print state)
         (declare (xargs :guard (and (symbolp name)
                                     ;; term need not be a pseudo-term
                                     (rule-item-listp rules)
                                     (rule-item-list-listp rule-lists)
                                     (symbol-listp remove-rules) ;allow rule-items?
                                     ;; todo: rule-classes
                                     (booleanp no-splitp)
                                     ;; print
                                     )
                         :stobjs state))
         (b* (((when (and rules rule-lists))
               (er hard? ',defthm-with-clause-processor-fn-name "Both :rules and :rule-lists were given for ~x0." name))
              (rule-lists (if rules
                              (list (elaborate-rule-items rules nil state))
                            (elaborate-rule-item-lists rule-lists state)))
              (rule-lists (remove-from-all rule-lists remove-rules)))
           `(defthm ,name
              ,term
              :hints (("Goal" :clause-processor (,',clause-processor-name clause
                                                                          '((:must-prove . t)
                                                                            (:rule-lists . ,rule-lists)
                                                                            (:no-splitp . ,no-splitp)
                                                                            (:print . ,print)
                                                                            (:tactic . ,tactic))
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
                                                     (rule-classes ':auto)
                                                     (print 'nil))
         (if (and (consp term)
                  (eq :eval (car term)))
             ;; Evaluate TERM:
             `(make-event (,',defthm-with-clause-processor-fn-name ',name ,(cadr term) ',tactic ',rules ',rule-lists ',remove-rules ',no-splitp ',rule-classes ',print state))
           ;; Don't evaluate TERM:
           `(make-event (,',defthm-with-clause-processor-fn-name ',name ',term ',tactic ',rules ',rule-lists ',remove-rules ',no-splitp ',rule-classes ',print state))))

       )))

(defmacro make-clause-processor-simple (suffix)
  (make-clause-processor-simple-fn suffix))
