; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "parteval")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-title (str)
  `(cw-event (concatenate 'string "~%~%~%********** " ,str "~%~%")))

(defmacro parteval (&rest args)
  `(apt::parteval ,@args))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Template non-recursive function with n = m = 1.")

 ;; cf. parteval-template.lisp

 (defstub e-guard (* *) => *)

 (encapsulate
   (((e * *) => * :formals (x y) :guard (e-guard x y)))
   (local (defun e (x y) (list x y))))

 (encapsulate
   (((f-guard-guard * *) => *))
   (local (defun f-guard-guard (x y) (cons x y)))
   (defthm f-guard-guard-always-holds (f-guard-guard x y)))

 (encapsulate
   (((f-guard * *) => * :formals (x y) :guard (f-guard-guard x y)))
   (local (defun f-guard (x y) (e-guard x y)))
   (defthm f-guard-verified (implies (f-guard x y) (e-guard x y))))

 (defund f (x y)
   (declare
    (xargs :guard (f-guard x y)
           :guard-hints (("Goal"
                          :in-theory nil
                          :use (f-guard-guard-always-holds f-guard-verified)))))
   (e x y))

 (defstub y~ () => *)

 (parteval f ((y (y~))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Template non-recursive function with n = 2 and m = 1.")

 ;; cf. parteval-template.lisp

 (defstub e-guard (* * *) => *)

 (encapsulate
   (((e * * *) => * :formals (x1 x2 y) :guard (e-guard x1 x2 y)))
   (local (defun e (x1 x2 y) (list x1 x2 y))))

 (encapsulate
   (((f-guard-guard * * *) => *))
   (local (defun f-guard-guard (x1 x2 y) (list x1 x2 y)))
   (defthm f-guard-guard-always-holds (f-guard-guard x1 x2 y)))

 (encapsulate
   (((f-guard * * *) => * :formals (x1 x2 y) :guard (f-guard-guard x1 x2 y)))
   (local (defun f-guard (x1 x2 y) (e-guard x1 x2 y)))
   (defthm f-guard-verified (implies (f-guard x1 x2 y) (e-guard x1 x2 y))))

 (defund f (x1 x2 y)
   (declare
    (xargs :guard (f-guard x1 x2 y)
           :guard-hints (("Goal"
                          :in-theory nil
                          :use (f-guard-guard-always-holds f-guard-verified)))))
   (e x1 x2 y))

 (defstub y~ () => *)

 (parteval f ((y (y~))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Template non-recursive function with n = 1 and m = 2.")

 ;; cf. parteval-template.lisp

 (defstub e-guard (* * *) => *)

 (encapsulate
   (((e * * *) => * :formals (x y1 y2) :guard (e-guard x y1 y2)))
   (local (defun e (x y1 y2) (list x y1 y2))))

 (encapsulate
   (((f-guard-guard * * *) => *))
   (local (defun f-guard-guard (x y1 y2) (list x y1 y2)))
   (defthm f-guard-guard-always-holds (f-guard-guard x y1 y2)))

 (encapsulate
   (((f-guard * * *) => * :formals (x y1 y2) :guard (f-guard-guard x y1 y2)))
   (local (defun f-guard (x y1 y2) (e-guard x y1 y2)))
   (defthm f-guard-verified (implies (f-guard x y1 y2) (e-guard x y1 y2))))

 (defund f (x y1 y2)
   (declare
    (xargs :guard (f-guard x y1 y2)
           :guard-hints (("Goal"
                          :in-theory nil
                          :use (f-guard-guard-always-holds f-guard-verified)))))
   (e x y1 y2))

 (defstub y1~ () => *)

 (defstub y2~ () => *)

 (parteval f ((y1 (y1~)) (y2 (y2~))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Template non-recursive function with n = 3 and m = 2.")

 ;; cf. parteval-template.lisp

 (defstub e-guard (* * * * *) => *)

 (encapsulate
   (((e * * * * *) => *
     :formals (x1 x2 x3 y1 y2) :guard (e-guard x1 x2 x3 y1 y2)))
   (local (defun e (x1 x2 x3 y1 y2) (list x1 x2 x3 y1 y2))))

 (encapsulate
   (((f-guard-guard * * * * *) => *))
   (local (defun f-guard-guard (x1 x2 x3 y1 y2) (list x1 x2 x3 y1 y2)))
   (defthm f-guard-guard-always-holds (f-guard-guard x1 x2 x3 y1 y2)))

 (encapsulate
   (((f-guard * * * * *) => *
     :formals (x1 x2 x3 y1 y2) :guard (f-guard-guard x1 x2 x3 y1 y2)))
   (local (defun f-guard (x1 x2 x3 y1 y2) (e-guard x1 x2 x3 y1 y2)))
   (defthm f-guard-verified
     (implies (f-guard x1 x2 x3 y1 y2) (e-guard x1 x2 x3 y1 y2))))

 (defund f (x1 x2 x3 y1 y2)
   (declare
    (xargs :guard (f-guard x1 x2 x3 y1 y2)
           :guard-hints (("Goal"
                          :in-theory nil
                          :use (f-guard-guard-always-holds f-guard-verified)))))
   (e x1 x2 x3 y1 y2))

 (defstub y1~ () => *)

 (defstub y2~ () => *)

 (parteval f ((y1 (y1~)) (y2 (y2~))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Template non-recursive function with n = 2 and m = 2 ~
              and intermixed arguments.")

 ;; cf. parteval-template.lisp

 (defstub e-guard (* * * *) => *)

 (encapsulate
   (((e * * * *) => *
     :formals (x y z w) :guard (e-guard x y z w)))
   (local (defun e (x y z w) (list x y z w))))

 (encapsulate
   (((f-guard-guard * * * *) => *))
   (local (defun f-guard-guard (x y z w) (list x y z w)))
   (defthm f-guard-guard-always-holds (f-guard-guard x y z w)))

 (encapsulate
   (((f-guard * * * *) => *
     :formals (x y z w) :guard (f-guard-guard x y z w)))
   (local (defun f-guard (x y z w) (e-guard x y z w)))
   (defthm f-guard-verified
     (implies (f-guard x y z w) (e-guard x y z w))))

 (defund f (x y z w)
   (declare
    (xargs :guard (f-guard x y z w)
           :guard-hints (("Goal"
                          :in-theory nil
                          :use (f-guard-guard-always-holds f-guard-verified)))))
   (e x y z w))

 (defstub x~ () => *)

 (defstub z~ () => *)

 (parteval f ((z (z~)) (x (x~))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Template recursive function with unchanging static argument ~
              and n = 1 and m = 1.")

 ;; cf. parteval-template.lisp

 (encapsulate

   (((a * *) => *)
    ((b * *) => *)
    ((c * * *) => *)
    ((d * *) => *)
    ((mu *) => *))

   (local (defun a (x y) (declare (ignore y)) (zp x)))
   (local (defun b (x y) (declare (ignore x y)) nil))
   (local (defun c (x y z) (declare (ignore x y z)) nil))
   (local (defun d (x y) (declare (ignore y)) (1- x)))
   (local (defun mu (x) (acl2-count x)))

   (defthm tau
     (and (o-p (mu x))
          (implies (not (a x y))
                   (o< (mu (d x y))
                       (mu x))))
     :rule-classes nil)) ; end of ENCAPSULATE

 (defund f (x y)
   (declare (xargs :measure (mu x)
                   :hints (("Goal" :in-theory nil :use tau))))
   (if (a x y)
       (b x y)
     (c x y (f (d x y) y))))

 (defstub y~ () => *)

 (parteval f ((y (y~))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the OLD input.")

 ;; not a symbol:
 (must-fail (parteval 5 ()) :with-output-off nil)
 (must-fail (parteval "fun" ()) :with-output-off nil)
 (must-fail (parteval (f x) ()) :with-output-off nil)
 ;; not existing:
 (must-fail (parteval xxxxxxxxxxxxxxxxxxxx ()) :with-output-off nil)

 ;; not a function:
 (must-fail (parteval car-cdr-elim ()) :with-output-off nil)

 ;; not resolving to a function:
 (must-fail (parteval yyyyyyyyyyyyy{*} ()) :with-output-off nil)

 ;; program mode:
 (must-succeed*
  (defun f (x y) (declare (xargs :mode :program)) (list x y))
  (must-fail (parteval f ()) :with-output-off nil)
  :with-output-off nil)

 ;; resolves to program-mode function:
 (must-succeed*
  (defun f{11} (x y) (declare (xargs :mode :program)) (list x y))
  (add-numbered-name-in-use f{11})
  (must-fail (parteval f{*} ()) :with-output-off nil)
  :with-output-off nil)

 ;; not defined:
 (must-succeed*
  (defstub f (* *) => *)
  (must-fail (parteval f ()) :with-output-off nil)
  :with-output-off nil)

 ;; multiple values:
 (must-succeed*
  (defun f (x y) (mv x y))
  (must-fail (parteval f ()) :with-output-off nil)
  :with-output-off nil)

 ;; input stobjs (state):
 (must-succeed*
  (defun f (x state)
    (declare (xargs :stobjs state))
    (declare (ignore state))
    x)
  (must-fail (parteval f ()) :with-output-off nil)
  :with-output-off nil)

 ;; input stobjs (user-defined):
 (must-succeed*
  (defstobj st)
  (defun f (x st)
    (declare (xargs :stobjs st))
    (declare (ignore st))
    x)
  (must-fail (parteval f ()) :with-output-off nil)
  :with-output-off nil)

 ;; input and output stobjs:
 (must-succeed*
  (defun f (state) (declare (xargs :stobjs state)) state)
  (must-fail (parteval f ()) :with-output-off nil)
  :with-output-off nil)

 ;; not guard-verified:
 (must-succeed*
  (defun f (x y) (list x y))
  (must-fail (parteval f () :verify-guards t) :with-output-off nil)
  :with-output-off nil)

 ;; valid function:
 (must-succeed*
  (defund f (x y) (list x y))
  (parteval f ((y 0))))

 ;; resolves to valid function:
 (must-succeed*
  (defund f{4} (x y) (list x y))
  (add-numbered-name-in-use f{4})
  (parteval f{*} ((y 0))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the STATIC input.")

 (defund f (x y) (declare (xargs :guard t)) (list x y))

 ;; not a doublet list:
 (must-fail (parteval f #\8) :with-output-off nil)
 (must-fail (parteval f (4/5 "t")) :with-output-off nil)
 (must-fail (parteval f ((x 0) 77)) :with-output-off nil)

 ;; duplicate arguments:
 (must-fail (parteval f ((x 0) (x 0))) :with-output-off nil)
 (must-fail (parteval f ((x 0) (x 1))) :with-output-off nil)

 ;; empty list:
 (must-fail (parteval f ()) :with-output-off nil)

 ;; not symbol arguments:
 (must-fail (parteval f (("x" 0))) :with-output-off nil)
 (must-fail (parteval f ((x 0) (#\y 1))) :with-output-off nil)

 ;; not subset of parameters:
 (must-fail (parteval f ((z 0))) :with-output-off nil)
 (must-fail (parteval f ((z 0) (x 10))) :with-output-off nil)

 ;; not valid terms:
 (must-fail (parteval f ((x (len 1 2)))) :with-output-off nil)
 (must-fail (parteval f ((x 0) (y (lambda (u) (1+ u))))) :with-output-off nil)

 ;; non-ground terms:
 (must-fail (parteval f ((x (len a)))) :with-output-off nil)

 ;; not logic-mode terms:
 (must-succeed*
  (defun g (x) (declare (xargs :mode :program)) x)
  (must-fail (parteval f ((x (g 0)))) :with-output-off nil)
  :with-output-off nil)

 ;; not single-valued terms:
 (must-succeed*
  (defun g (u v) (declare (xargs :guard t)) (mv u v))
  (must-fail (parteval f ((x (g 1 2)))) :with-output-off nil)
  :with-output-off nil)

 ;; not guard-verified terms:
 (must-succeed*
  (defun g (x) x)
  (must-fail (parteval f ((x (g 0)))) :with-output-off nil)
  :with-output-off nil)

 ;; terms calling the target function:
 (must-fail (parteval f ((y (f #\a #\b)))) :with-output-off nil)

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :NEW-NAME input.")

 (defund f (x y) (declare (xargs :guard t)) (list x y))

 ;; not a symbol:
 (must-fail (parteval f ((x 0)) :new-name "f'") :with-output-off nil)

 ;; in the main Lisp package:
 (must-fail (parteval f ((x 0)) :new-name atom) :with-output-off nil)

 ;; keyword (other than :AUTO):
 (must-fail (parteval f ((x 0)) :new-name :fff) :with-output-off nil)

 ;; already existing:
 (must-fail (parteval f ((x 0)) :new-name len) :with-output-off nil)

 ;; default:
 (must-succeed*
  (parteval f ((x 0)))
  (assert! (function-namep 'f{1} (w state))))

 ;; automatic:
 (must-succeed*
  (parteval f ((x 0)) :new-name :auto)
  (assert! (function-namep 'f{1} (w state))))

 ;; specified:
 (must-succeed*
  (parteval f ((x 0)) :new-name f^)
  (assert! (function-namep 'f^ (w state))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :NEW-ENABLE input.")

 (defun f (x y) (declare (xargs :guard t)) (list x y))

 ;; not T, NIL, or :AUTO:
 (must-fail (parteval f ((y 1)) :new-enable #\u) :with-output-off nil)

 ;; default, with target function enabled:
 (must-succeed*
  (parteval f ((y 1)) :thm-enable nil)
  (assert! (fundef-enabledp 'f{1} state))
  :with-output-off nil)

 ;; default, with target function disabled:
 (must-succeed*
  (in-theory (disable f))
  (parteval f ((y 1)))
  (assert! (fundef-disabledp 'f{1} state))
  :with-output-off nil)

 ;; automatic, with target function enabled:
 (must-succeed*
  (parteval f ((y 1)) :new-enable :auto :thm-enable nil)
  (assert! (fundef-enabledp 'f{1} state))
  :with-output-off nil)

 ;; automatic, with target function disabled:
 (must-succeed*
  (in-theory (disable f))
  (parteval f ((y 1)) :new-enable :auto)
  (assert! (fundef-disabledp 'f{1} state))
  :with-output-off nil)

 ;; enable, with target function enabled:
 (must-succeed*
  (parteval f ((y 1)) :new-enable t :thm-enable nil)
  (assert! (fundef-enabledp 'f{1} state))
  :with-output-off nil)

 ;; enable, with target function disabled:
 (must-succeed*
  (in-theory (disable f))
  (parteval f ((y 1)) :new-enable t :thm-enable nil)
  (assert! (fundef-enabledp 'f{1} state))
  :with-output-off nil)

 ;; disable, with target function enabled:
 (must-succeed*
  (parteval f ((y 1)) :new-enable nil)
  (assert! (fundef-disabledp 'f{1} state))
  :with-output-off nil)

 ;; disable, with target function disabled:
 (must-succeed*
  (in-theory (disable f))
  (parteval f ((y 1)) :new-enable nil)
  (assert! (fundef-disabledp 'f{1} state))
  :with-output-off nil)

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :THM-NAME input.")

 (defund f (x y) (declare (xargs :guard t)) (list x y))

 ;; not a symbol:
 (must-fail (parteval f ((x 0)) :thm-name "thm") :with-output-off nil)

 ;; in the main Lisp package:
 (must-fail (parteval f ((x 0)) :thm-name atom) :with-output-off nil)

 ;; keyword (other than :AUTO):
 (must-fail (parteval f ((x 0)) :thm-name :fff) :with-output-off nil)

 ;; already existing:
 (must-fail (parteval f ((x 0)) :thm-name len) :with-output-off nil)

 ;; default:
 (must-succeed*
  (parteval f ((x 0)))
  (assert! (theorem-namep 'f-~>-f{1} (w state))))

 ;; automatic:
 (must-succeed*
  (parteval f ((x 0)) :thm-name :auto)
  (assert! (theorem-namep 'f-~>-f{1} (w state))))

 ;; specified:
 (must-succeed*
  (parteval f ((x 0)) :thm-name f-thm)
  (assert! (theorem-namep 'f-thm (w state))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :THM-ENABLE input.")

 (defund f (x y) (declare (xargs :guard t)) (list x y))

 (defund r (x y) (declare (xargs :guard t)) (if (atom x) y (r (cdr x) y)))

 ;; not T or NIL:
 (must-fail (parteval f ((x 0)) :thm-enable 9) :with-output-off nil)
 (must-fail (parteval r ((x 0)) :thm-enable "yes") :with-output-off nil)

 ;; default:
 (must-succeed*
  (parteval f ((x 0)))
  (assert! (rune-enabledp '(:rewrite f-~>-f{1}) state)))
 (must-succeed*
  (parteval r ((x 0)))
  (assert! (rune-enabledp '(:rewrite r-~>-r{1}) state)))

 ;; enable:
 (must-succeed*
  (parteval f ((x 0)) :thm-enable t)
  (assert! (rune-enabledp '(:rewrite f-~>-f{1}) state)))
 (must-succeed*
  (parteval r ((x 0)) :thm-enable t)
  (assert! (rune-enabledp '(:rewrite r-~>-r{1}) state)))

 ;; disable:
 (must-succeed*
  (parteval f ((x 0)) :thm-enable nil)
  (assert! (not (rune-enabledp '(:rewrite f-~>-f{1}) state))))
 (must-succeed*
  (parteval r ((x 0)) :thm-enable nil)
  (assert! (not (rune-enabledp '(:rewrite r-~>-r{1}) state))))

 ;; default, with new function enabled:
 (must-succeed*
  (in-theory (enable f))
  (parteval f ((x 0)))
  (assert! (rune-enabledp '(:rewrite f-~>-f{1}) state))
  :with-output-off nil)
 (must-succeed*
  (in-theory (enable r))
  (must-fail (parteval r ((x 0))) :with-output-off nil)
  :with-output-off nil)

 ;; enable, with new function enabled
 (must-succeed*
  (in-theory (enable f))
  (parteval f ((x 0)) :thm-enable t)
  (assert! (rune-enabledp '(:rewrite f-~>-f{1}) state)))
 (must-succeed*
  (in-theory (enable r))
  (must-fail (parteval r ((x 0)) :thm-enable t) :with-output-off nil)
  :with-output-off nil)

 ;; disable, with new function enabled
 (must-succeed*
  (in-theory (enable f))
  (parteval f ((x 0)) :thm-enable nil)
  (assert! (not (rune-enabledp '(:rewrite f-~>-f{1}) state)))
  :with-output-off nil)
 (must-succeed*
  (in-theory (enable r))
  (parteval r ((x 0)) :thm-enable nil)
  (assert! (not (rune-enabledp '(:rewrite r-~>-r{1}) state)))
  :with-output-off nil)

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :VERIFY-GUARDS input.")

 (defund f (x y) (list x y))

 ;; not T, NIL, or :AUTO:
 (must-fail (parteval f ((x nil)) :verify-guards do-it) :with-output-off nil)

 ;; default, with target function guard-verified:
 (must-succeed*
  (verify-guards f)
  (parteval f ((x nil)))
  (assert! (guard-verified-p 'f{1} (w state))))

 ;; default, with target function not guard-verified:
 (must-succeed*
  (parteval f ((x nil)))
  (assert! (not (guard-verified-p 'f{1} (w state)))))

 ;; automatic, with target function guard-verified:
 (must-succeed*
  (verify-guards f)
  (parteval f ((x nil)) :verify-guards :auto)
  (assert! (guard-verified-p 'f{1} (w state))))

 ;; default, with target function not guard-verified:
 (must-succeed*
  (parteval f ((x nil)) :verify-guards :auto)
  (assert! (not (guard-verified-p 'f{1} (w state)))))

 ;; verify guards, with target function guard-verified:
 (must-succeed*
  (verify-guards f)
  (parteval f ((x nil)) :verify-guards t)
  (assert! (guard-verified-p 'f{1} (w state))))

 ;; verify guards, with target function not guard-verified:
 (must-fail (parteval f ((x nil)) :verify-guards t) :with-output-off nil)

 ;; do not verify guards, with target function guard-verified:
 (must-succeed*
  (verify-guards f)
  (parteval f ((x nil)) :verify-guards nil)
  (assert! (not (guard-verified-p 'f{1} (w state)))))

 ;; do not verify guards, with target function not guard-verified:
 (must-succeed*
  (parteval f ((x nil)) :verify-guards nil)
  (assert! (not (guard-verified-p 'f{1} (w state)))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :PRINT input.")

 (defund f (x y) (list x y))

 ;; not a print specifier:
 (must-fail (parteval f ((y nil)) :print 3/4) :with-output-off nil)

 ;; default output:
 (must-succeed (parteval f ((y nil))) :with-output-off nil)

 ;; no output:
 (must-succeed (parteval f ((y nil)) :print nil) :with-output-off nil)

 ;; error output:
 (must-succeed (parteval f ((y nil)) :print :error) :with-output-off nil)

 ;; result output:
 (must-succeed (parteval f ((y nil)) :print :result) :with-output-off nil)

 ;; information output:
 (must-succeed (parteval f ((y nil)) :print :info) :with-output-off nil)

 ;; all output:
 (must-succeed (parteval f ((y nil)) :print :all) :with-output-off nil)

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :SHOW-ONLY input.")

 (defund f (x y) (list x y))

 ;; not T or NIL:
 (must-fail (parteval f ((x #\a)) :show-only :never) :with-output-off nil)

 ;; default
 (must-succeed (parteval f ((x #\a))))

 ;; show-only
 (must-succeed*
  (parteval f ((x #\a)) :show-only t)
  (parteval f ((x #\a)) :show-only t :print nil)
  (parteval f ((x #\a)) :show-only t :print :error)
  (parteval f ((x #\a)) :show-only t :print :result)
  (parteval f ((x #\a)) :show-only t :print :info)
  (parteval f ((x #\a)) :show-only t :print :all)
  (assert! (not (function-namep 'f{1} (w state))))
  :with-output-off nil)

 ;; submit events:
 (must-succeed*
  (parteval f ((x #\a)) :show-only nil)
  (assert! (function-namep 'f{1} (w state))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test redundancy.")

 (defund f (x y) (list x y))

 ;; initial call without :PRINT and without :SHOW-ONLY:
 (must-succeed*
  (parteval f ((y "y")))
  (must-be-redundant (parteval f ((y "y"))))
  (must-be-redundant (parteval f ((y "y")) :print :all))
  (must-be-redundant (parteval f ((y "y")) :print nil))
  (must-be-redundant (parteval f ((y "y")) :show-only t))
  (must-be-redundant (parteval f ((y "y")) :show-only nil))
  (must-be-redundant (parteval f ((y "y")) :print :all :show-only t))
  (must-be-redundant (parteval f ((y "y")) :print nil :show-only t))
  (must-be-redundant (parteval f ((y "y")) :print :all :show-only nil))
  (must-be-redundant (parteval f ((y "y")) :print nil :show-only nil)))

 ;; initial call with :PRINT :ALL and without :SHOW-ONLY:
 (must-succeed*
  (parteval f ((y "y")) :print :all)
  (must-be-redundant (parteval f ((y "y"))))
  (must-be-redundant (parteval f ((y "y")) :print :all))
  (must-be-redundant (parteval f ((y "y")) :print nil))
  (must-be-redundant (parteval f ((y "y")) :show-only t))
  (must-be-redundant (parteval f ((y "y")) :show-only nil))
  (must-be-redundant (parteval f ((y "y")) :print :all :show-only t))
  (must-be-redundant (parteval f ((y "y")) :print nil :show-only t))
  (must-be-redundant (parteval f ((y "y")) :print :all :show-only nil))
  (must-be-redundant (parteval f ((y "y")) :print nil :show-only nil)))

 ;; initial call with :PRINT NIL and without :SHOW-ONLY:
 (must-succeed*
  (parteval f ((y "y")) :print nil)
  (must-be-redundant (parteval f ((y "y"))))
  (must-be-redundant (parteval f ((y "y")) :print :all))
  (must-be-redundant (parteval f ((y "y")) :print nil))
  (must-be-redundant (parteval f ((y "y")) :show-only t))
  (must-be-redundant (parteval f ((y "y")) :show-only nil))
  (must-be-redundant (parteval f ((y "y")) :print :all :show-only t))
  (must-be-redundant (parteval f ((y "y")) :print nil :show-only t))
  (must-be-redundant (parteval f ((y "y")) :print :all :show-only nil))
  (must-be-redundant (parteval f ((y "y")) :print nil :show-only nil)))

 ;; initial call without :PRINT and with :SHOW-ONLY T:
 (must-succeed*
  (parteval f ((y "y")) :show-only t)
  (must-fail-local (must-be-redundant (parteval f ((y "y"))))))

 ;; initial call without :PRINT and with :SHOW-ONLY NIL:
 (must-succeed*
  (parteval f ((y "y")) :show-only nil)
  (must-be-redundant (parteval f ((y "y"))))
  (must-be-redundant (parteval f ((y "y")) :print :all))
  (must-be-redundant (parteval f ((y "y")) :print nil))
  (must-be-redundant (parteval f ((y "y")) :show-only t))
  (must-be-redundant (parteval f ((y "y")) :show-only nil))
  (must-be-redundant (parteval f ((y "y")) :print :all :show-only t))
  (must-be-redundant (parteval f ((y "y")) :print nil :show-only t))
  (must-be-redundant (parteval f ((y "y")) :print :all :show-only nil))
  (must-be-redundant (parteval f ((y "y")) :print nil :show-only nil)))

 ;; initial call with :PRINT :ALL and with :SHOW-ONLY T:
 (must-succeed*
  (parteval f ((y "y")) :print :all :show-only t)
  (must-fail-local (must-be-redundant (parteval f ((y "y"))))))

 ;; initial call with :PRINT :ALL and with :SHOW-ONLY NIL:
 (must-succeed*
  (parteval f ((y "y")) :print :all :show-only nil)
  (must-be-redundant (parteval f ((y "y"))))
  (must-be-redundant (parteval f ((y "y")) :print :all))
  (must-be-redundant (parteval f ((y "y")) :print nil))
  (must-be-redundant (parteval f ((y "y")) :show-only t))
  (must-be-redundant (parteval f ((y "y")) :show-only nil))
  (must-be-redundant (parteval f ((y "y")) :print :all :show-only t))
  (must-be-redundant (parteval f ((y "y")) :print nil :show-only t))
  (must-be-redundant (parteval f ((y "y")) :print :all :show-only nil))
  (must-be-redundant (parteval f ((y "y")) :print nil :show-only nil)))

 ;; initial call with :PRINT NIL and with :SHOW-ONLY T:
 (must-succeed*
  (parteval f ((y "y")) :print nil :show-only t)
  (must-fail-local (must-be-redundant (parteval f ((y "y"))))))

 ;; initial call with :PRINT NIL and with :SHOW-ONLY NIL:
 (must-succeed*
  (parteval f ((y "y")) :print nil :show-only nil)
  (must-be-redundant (parteval f ((y "y"))))
  (must-be-redundant (parteval f ((y "y")) :print :all))
  (must-be-redundant (parteval f ((y "y")) :print nil))
  (must-be-redundant (parteval f ((y "y")) :show-only t))
  (must-be-redundant (parteval f ((y "y")) :show-only nil))
  (must-be-redundant (parteval f ((y "y")) :print :all :show-only t))
  (must-be-redundant (parteval f ((y "y")) :print nil :show-only t))
  (must-be-redundant (parteval f ((y "y")) :print :all :show-only nil))
  (must-be-redundant (parteval f ((y "y")) :print nil :show-only nil)))

 ;; non-redundant calls:
 (must-succeed*
  (parteval f ((y "y")))
  ;; different target:
  (must-fail-local (must-be-redundant (restrict len (true-listp x))))
  ;; different restriction:
  (must-fail-local (must-be-redundant (restrict nfix (integerp x))))
  ;; different options:
  (must-fail-local
   (must-be-redundant (parteval f ((y "y")) :verify-guards nil)))
  (must-fail-local
   (must-be-redundant (parteval f ((y "y")) :new-name nfix-new))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the exponential function with static exponent.")

 (parteval expt ((i 5)) :new-name expt5 :thm-enable nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test a recursive function with unchanging static argument.")

 (defun f (x y)
   (declare (xargs :guard (and (true-listp x) (natp y))))
   (if (endp x)
       (1+ y)
     (f (cdr x) y)))

 (parteval f ((y 0))))
