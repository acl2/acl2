; System Utilities -- Named Formulas -- Tests
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "named-formulas")
(include-book "world-queries")
(include-book "kestrel/utilities/testing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((mv success & state)
       (prove-named-formula 'false
                            '(equal x y)
                            nil ; hints
                            nil ; verbose
                            state)))
   (value (not success))))

(must-eval-to-t
 (b* (((mv success & state)
       (prove-named-formula 'false
                            '(equal x y)
                            nil ; hints
                            t ; verbose
                            state)))
   (value (not success))))

(must-succeed*
 (defund f (x) x)
 (must-eval-to-t
  (b* (((mv success & state)
        (prove-named-formula 'need-hints
                             '(equal (f x) x)
                             nil ; hints
                             nil ; verbose
                             state)))
    (value (not success)))))

(must-succeed*
 (defund f (x) x)
 (must-eval-to-t
  (b* (((mv success & state)
        (prove-named-formula 'need-hints
                             '(equal (f x) x)
                             nil ; hints
                             t ; verbose
                             state)))
    (value (not success)))))

(must-eval-to-t
 (b* (((mv success & state)
       (prove-named-formula 'true
                            '(equal x x)
                            nil ; hints
                            nil ; verbose
                            state)))
   (value success)))

(must-eval-to-t
 (b* (((mv success & state)
       (prove-named-formula 'true
                            '(equal x x)
                            nil ; hints
                            t ; verbose
                            state)))
   (value success)))

(must-succeed*
 (defund f (x) x)
 (must-eval-to-t
  (b* (((mv success & state)
        (prove-named-formula 'need-hints
                             '(equal (f x) x)
                             '(("Goal" :in-theory (enable f)))
                             nil ; verbose
                             state)))
    (value success))))

(must-succeed*
 (defund f (x) x)
 (must-eval-to-t
  (b* (((mv success & state)
        (prove-named-formula 'need-hints
                             '(equal (f x) x)
                             '(("Goal" :in-theory (enable f)))
                             t ; verbose
                             state)))
    (value success))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((mv success & state)
       (prove-named-formulas '((true . (equal x x))
                               (false . (equal x y)))
                             nil ; named-hints
                             nil ; verbose
                             state)))
   (value (not success))))

(must-eval-to-t
 (b* (((mv success & state)
       (prove-named-formulas nil ; named-formulas
                             nil ; named-hints
                             nil ; verbose
                             state)))
   (value success)))

(must-succeed*
 (defund f (x) x)
 (must-eval-to-t
  (b* (((mv success & state)
        (prove-named-formulas '((true . (equal x x))
                                (need-hints . (equal (f x) x)))
                              '((need-hints . (("Goal" :in-theory (enable f)))))
                              nil ; verbose
                              state)))
    (value success))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail-local
 (ensure-named-formulas '((true . (equal x x))
                          (false . (equal x y)))
                        nil ; named-hints
                        nil ; verbose
                        t ; error-erp
                        nil ; error-val
                        'top ; ctx
                        state))

(must-succeed*
 (defund f (x) x)
 (must-succeed
  (ensure-named-formulas '((true . (equal x x))
                           (need-hints . (equal (f x) x)))
                         '((need-hints . (("Goal" :in-theory (enable f)))))
                         nil ; verbose
                         t ; error-erp
                         nil ; error-val
                         'top ; ctx
                         state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (encapsulate
   ()
   (make-event
    (b* (((mv event &)
          (named-formula-to-thm-event 'mythm
                                      '(acl2-numberp (+ x y))
                                      nil ; hints
                                      :type-prescription
                                      nil ; enabled
                                      nil ; local
                                      nil ; named-to-avoid
                                      (w state))))
      event))
   (assert! (runep '(:type-prescription mythm) (w state)))
   (assert! (rune-disabledp '(:type-prescription mythm) state)))
 (assert! (runep '(:type-prescription mythm) (w state)))
 (assert! (rune-disabledp '(:type-prescription mythm) state)))

(must-succeed*
 (encapsulate
   ()
   (make-event
    (b* (((mv event &)
          (named-formula-to-thm-event 'mythm
                                      '(acl2-numberp (+ x y))
                                      nil ; hints
                                      :type-prescription
                                      nil ; enabled
                                      t ; local
                                      nil ; named-to-avoid
                                      (w state))))
      event))
   (assert! (runep '(:type-prescription mythm) (w state)))
   (assert! (rune-disabledp '(:type-prescription mythm) state)))
 (assert! (not (runep '(:type-prescription mythm) (w state)))))

(must-succeed*
 (encapsulate
   ()
   (make-event
    (b* (((mv event &)
          (named-formula-to-thm-event 'mythm
                                      '(acl2-numberp (+ x y))
                                      nil ; hints
                                      :type-prescription
                                      t ; enabled
                                      nil ; local
                                      nil ; named-to-avoid
                                      (w state))))
      event))
   (assert! (runep '(:type-prescription mythm) (w state)))
   (assert! (rune-enabledp '(:type-prescription mythm) state)))
 (assert! (runep '(:type-prescription mythm) (w state)))
 (assert! (rune-enabledp '(:type-prescription mythm) state)))

(must-succeed*
 (encapsulate
   ()
   (make-event
    (b* (((mv event &)
          (named-formula-to-thm-event 'mythm
                                      '(acl2-numberp (+ x y))
                                      nil ; hints
                                      :type-prescription
                                      nil ; enabled
                                      nil ; local
                                      '(mythm mythm$) ; named-to-avoid
                                      (w state))))
      event))
   (assert! (runep '(:type-prescription mythm$$) (w state)))
   (assert! (rune-disabledp '(:type-prescription mythm$$) state)))
 (assert! (runep '(:type-prescription mythm$$) (w state)))
 (assert! (rune-disabledp '(:type-prescription mythm$$) state)))

(must-succeed*
 (encapsulate
   ()
   (make-event
    (b* (((mv event &)
          (named-formula-to-thm-event 'cons
                                      '(acl2-numberp (+ x y))
                                      nil ; hints
                                      :type-prescription
                                      nil ; enabled
                                      nil ; local
                                      nil ; named-to-avoid
                                      (w state))))
      event))
   (assert! (runep '(:type-prescription common-lisp::cons$) (w state)))
   (assert! (rune-disabledp '(:type-prescription common-lisp::cons$) state)))
 (assert! (runep '(:type-prescription common-lisp::cons$) (w state)))
 (assert! (rune-disabledp '(:type-prescription common-lisp::cons$) state)))

(must-succeed*
 (encapsulate
   ()
   (make-event
    (b* (((mv event &)
          (named-formula-to-thm-event :mythm ; keyword
                                      '(acl2-numberp (+ x y))
                                      nil ; hints
                                      :type-prescription
                                      nil ; enabled
                                      nil ; local
                                      nil ; named-to-avoid
                                      (w state))))
      event))
   (assert! (runep '(:type-prescription mythm) (w state)))
   (assert! (rune-disabledp '(:type-prescription mythm) state)))
 (assert! (runep '(:type-prescription mythm) (w state)))
 (assert! (rune-disabledp '(:type-prescription mythm) state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (make-event
  (b* (((mv events &)
        (named-formulas-to-thm-events nil ; named-formulas
                                      nil ; named-hints
                                      nil ; named-rule-classes
                                      nil ; enableds
                                      nil ; locals
                                      nil ; named-to-avoid
                                      (w state))))
    `(progn ,@events))))

(must-succeed*
 (defund h (x) x)
 (encapsulate
   ()
   (make-event
    (b* (((mv events &)
          (named-formulas-to-thm-events
           '((mythm . (acl2-numberp (+ x y)))
             (cons . (equal (h x) x))
             (th . (acl2-numberp (- x))))
           '((cons . (("Goal" :in-theory (enable h)))))
           '((mythm . (:type-prescription :rewrite))
             (cons . :rewrite)
             (th . (:rewrite)))
           '(mythm cons) ; enableds
           '(cons) ; locals
           '(th) ; names-to-avoid
           (w state))))
      `(progn ,@events)))
   (assert! (runep '(:type-prescription mythm) (w state)))
   (assert! (runep '(:rewrite mythm) (w state)))
   (assert! (runep '(:rewrite common-lisp::cons$) (w state)))
   (assert! (runep '(:rewrite th$) (w state)))
   (assert! (rune-enabledp '(:type-prescription mythm) state))
   (assert! (rune-enabledp '(:rewrite mythm) state))
   (assert! (rune-enabledp '(:rewrite common-lisp::cons$) state))
   (assert! (rune-disabledp '(:rewrite th$) state)))
 (assert! (runep '(:type-prescription mythm) (w state)))
 (assert! (runep '(:rewrite mythm) (w state)))
 (assert! (not (runep '(:rewrite cons$) (w state))))
 (assert! (runep '(:rewrite th$) (w state))))
