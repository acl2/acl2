; Applicability Conditions -- Tests
;
; Copyright (C) 2015-2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests for the utilities in applicability-conditions.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "applicability-conditions")
(include-book "testing")
(include-book "world-queries")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (applicability-condition-p (make-applicability-condition
                                     :name 'appcond
                                     :formula '(equal x x)
                                     :hints nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (applicability-condition-listp nil))

(assert! (applicability-condition-listp (list (make-applicability-condition
                                               :name 'appcond
                                               :formula '(equal x x)
                                               :hints nil))))

(assert! (not (applicability-condition-listp '(1 2 3))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((mv success & state)
       (prove-applicability-condition (make-applicability-condition
                                       :name 'false
                                       :formula '(equal x y)
                                       :hints nil)
                                      nil ; verbose
                                      state)))
   (value (not success))))

(must-eval-to-t
 (b* (((mv success & state)
       (prove-applicability-condition (make-applicability-condition
                                       :name 'false
                                       :formula '(equal x y)
                                       :hints nil)
                                      t ; verbose
                                      state)))
   (value (not success))))

(must-succeed*
 (defund f (x) x)
 (must-eval-to-t
  (b* (((mv success & state)
        (prove-applicability-condition (make-applicability-condition
                                        :name 'need-hints
                                        :formula '(equal (f x) x)
                                        :hints nil)
                                       nil ; verbose
                                       state)))
    (value (not success)))))

(must-succeed*
 (defund f (x) x)
 (must-eval-to-t
  (b* (((mv success & state)
        (prove-applicability-condition (make-applicability-condition
                                        :name 'need-hints
                                        :formula '(equal (f x) x)
                                        :hints nil)
                                       t ; verbose
                                       state)))
    (value (not success)))))

(must-eval-to-t
 (b* (((mv success & state)
       (prove-applicability-condition (make-applicability-condition
                                       :name 'true
                                       :formula '(equal x x)
                                       :hints nil)
                                      nil ; verbose
                                      state)))
   (value success)))

(must-eval-to-t
 (b* (((mv success & state)
       (prove-applicability-condition (make-applicability-condition
                                       :name 'true
                                       :formula '(equal x x)
                                       :hints nil)
                                      t ; verbose
                                      state)))
   (value success)))

(must-succeed*
 (defund f (x) x)
 (must-eval-to-t
  (b* (((mv success & state)
        (prove-applicability-condition
         (make-applicability-condition
          :name 'true
          :formula '(equal (f x) x)
          :hints '(("Goal" :in-theory (enable f))))
         nil ; verbose
         state)))
    (value success))))

(must-succeed*
 (defund f (x) x)
 (must-eval-to-t
  (b* (((mv success & state)
        (prove-applicability-condition
         (make-applicability-condition
          :name 'true
          :formula '(equal (f x) x)
          :hints '(("Goal" :in-theory (enable f))))
         t ; verbose
         state)))
    (value success))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((mv success & state)
       (prove-applicability-conditions
        (list (make-applicability-condition
               :name 'true
               :formula '(equal x x)
               :hints nil)
              (make-applicability-condition
               :name 'false
               :formula '(equal x y)
               :hints nil))
        nil ; verbose
        state)))
   (value (not success))))

(must-eval-to-t
 (b* (((mv success & state)
       (prove-applicability-conditions nil
                                       nil ; verbose
                                       state)))
   (value success)))

(must-succeed*
 (defund f (x) x)
 (must-eval-to-t
  (b* (((mv success & state)
        (prove-applicability-conditions
         (list (make-applicability-condition
                :name 'true
                :formula '(equal x x)
                :hints nil)
               (make-applicability-condition
                :name 'need-hints
                :formula '(equal (f x) x)
                :hints '(("Goal" :in-theory (enable f)))))
         nil ; verbose
         state)))
    (value success))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail-local
 (ensure-applicability-conditions
  (list (make-applicability-condition
         :name 'true
         :formula '(equal x x)
         :hints nil)
        (make-applicability-condition
         :name 'false
         :formula '(equal x y)
         :hints nil))
  nil ; verbose
  'top ; ctx
  state))

(must-succeed*
 (defund f (x) x)
 (must-succeed
  (ensure-applicability-conditions
   (list (make-applicability-condition
          :name 'true
          :formula '(equal x x)
          :hints nil)
         (make-applicability-condition
          :name 'need-hints
          :formula '(equal (f x) x)
          :hints '(("Goal" :in-theory (enable f)))))
   nil ; verbose
   'top ; ctx
   state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun f (state)
   (declare (xargs :stobjs state :mode :program))
   (mv-let (name event)
     (applicability-condition-event
      (make-applicability-condition :name 'appcond
                                    :formula '(acl2-numberp (+ x y))
                                    :hints nil)
      nil ; local
      nil ; enabled
      '(:type-prescription)
      nil ; names-to-avoid
      (w state))
     `(progn
        (encapsulate () ,event)
        (assert! (rune-disabledp '(:type-prescription ,name) state)))))
 (make-event (f state)))

(must-succeed*
 (defun f (state)
   (declare (xargs :stobjs state :mode :program))
   (mv-let (name event)
     (applicability-condition-event
      (make-applicability-condition :name 'appcond
                                    :formula '(acl2-numberp (+ x y))
                                    :hints nil)
      t ; local
      nil ; enabled
      '(:type-prescription)
      nil ; names-to-avoid
      (w state))
     `(progn
        (encapsulate () ,event)
        (assert! (not (runep '(:type-prescription ,name) (w state)))))))
 (make-event (f state)))

(must-succeed*
 (defun f (state)
   (declare (xargs :stobjs state :mode :program))
   (mv-let (name event)
     (applicability-condition-event
      (make-applicability-condition :name 'appcond
                                    :formula '(acl2-numberp (+ x y))
                                    :hints nil)
      nil ; local
      t ; enabled
      '(:type-prescription)
      nil ; names to avoid
      (w state))
     `(progn
        (encapsulate () ,event)
        (assert! (rune-enabledp '(:type-prescription ,name) state)))))
 (make-event (f state)))

(must-succeed*
 (defun f (state)
   (declare (xargs :stobjs state :mode :program))
   (mv-let (name event)
     (applicability-condition-event
      (make-applicability-condition :name 'appcond
                                    :formula '(acl2-numberp (+ x y))
                                    :hints nil)
      nil ; local
      nil ; enabled
      '(:type-prescription)
      '(appcond appcond$)
      (w state))
     `(progn
        (encapsulate () ,event)
        (assert! (rune-disabledp '(:type-prescription ,name) state)))))
 (make-event (f state)))

(must-succeed*
 (defun f (state)
   (declare (xargs :stobjs state :mode :program))
   (mv-let (name event)
     (applicability-condition-event
      (make-applicability-condition :name 'cons
                                    :formula '(acl2-numberp (+ x y))
                                    :hints nil)
      nil ; local
      nil ; enabled
      '(:type-prescription)
      nil ; names-to-avoid
      (w state))
     `(progn
        (encapsulate () ,event)
        (assert! (rune-disabledp '(:type-prescription ,name) state)))))
 (make-event (f state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun f (state)
   (declare (xargs :stobjs state :mode :program))
   (mv-let (names-to-thms events)
     (applicability-condition-events nil nil nil nil nil (w state))
     `(progn
        ,@events
        (assert-equal ,names-to-thms nil))))
 (make-event (f state)))

(must-succeed*
 (defund h (x) x)
 (defun f (state)
   (declare (xargs :stobjs state :mode :program))
   (mv-let (names-to-thms events)
     (applicability-condition-events
      (list (make-applicability-condition :name 'appcond
                                          :formula '(acl2-numberp (+ x y))
                                          :hints nil)
            (make-applicability-condition :name 'cons
                                          :formula '(equal (h x) x)
                                          :hints '(("Goal"
                                                    :in-theory (enable h))))
            (make-applicability-condition :name 'th
                                          :formula '(acl2-numberp (- x))
                                          :hints nil))
      '(nil t nil) ; locals
      '(t t nil) ; enableds
      '((:type-prescription :rewrite)
        (:rewrite)
        (:rewrite))
      '(th)
      (w state))
     (let ((appcond-thm (cdr (assoc-eq 'appcond names-to-thms)))
           (cons-thm (cdr (assoc-eq 'cons names-to-thms)))
           (th-thm (cdr (assoc-eq 'th names-to-thms))))
       `(progn
          (encapsulate () ,@events)
          (assert! (rune-enabledp '(:type-prescription ,appcond-thm) state))
          (assert! (not (runep '(:rewrite ,cons-thm) (w state))))
          (assert! (rune-disabledp '(:rewrite ,th-thm) state))))))
 (make-event (f state)))
