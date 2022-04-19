; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Thanks to Eric Smith for the idea leading to this tool.

(in-package "ACL2")

; For magic-ev:
(include-book "clause-processors/meta-extract-user" :dir :system)

(include-book "system/bind-macro-args" :dir :system)

(include-book "xdoc/top" :dir :system)

(defxdoc magic-macroexpand
  :parents (macros kestrel-utilities)
  :short "A macroexpansion utility for @(see logic)-mode code"
  :long "@({
 General Form:
 (magic-macroexpand form ctx wrld state)
  })

 <p>where @('form') is a user-level @(see term), @('ctx') is a context (see
 @(see ctx)), @('wrld') is an ACL2 logical @('world'), and @('state') is the
 ACL2 @(see state).  If @('form') is a macro call then that call is expanded to
 produce another form, which is recursively macroexpanded.  The result is
 @('(mv erp val)'), where if @('erp') is @('nil') then @('val') is the desired
 macroexpansion, and otherwise @('val') is a message (see @(see msg)).</p>

 <p>For each macro expanded in the process described above, its body must
 consist of @(see logic)-mode code.  Also note that the utility
 @('magic-macroexpand') is in @(see logic) mode.</p>

 <p>Here is a simple example.</p>

 @({
 ACL2 !>(defmacro my-mac (a b) `(* ,a ,b))

 Summary
 Form:  ( DEFMACRO MY-MAC ...)
 Rules: NIL
 Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
  MY-MAC
 ACL2 !>(set-guard-checking :nowarn)

 Leaving guard checking on, but changing value to :NOWARN.

 ACL2 !>(magic-macroexpand '(my-mac x y) 'top (w state) state)
 (NIL (BINARY-* X Y))
 ACL2 !>
 })

 <p>Notice the use of @('(set-guard-checking :nowarn)').  This is optional, but
 without it there may be warnings printed.  Indeed, those warnings suggest
 using either this method of inhibiting warnings or
 @('(set-guard-checking :all)').  Such warnings may be eliminated in the
 future.</p>")

(defun magic-macro-guard-er-msg (x ctx wrld)

; This is a simpler version of ACL2 source function macro-guard-er-msg.  It
; avoids generating a custom error message based on the guard-msg-table.

  (declare (xargs :guard (plist-worldp wrld)))
  (cond
   ((and (consp x) (symbolp (car x))) ; always true?
    (let ((name (car x)))
      (er-cmp ctx
              "In the attempt to macroexpand the form ~x0 the guard, ~x1, for ~
               ~x2 failed."
              x
              (getpropc name 'guard *t* wrld)
              name)))
   (t (er-cmp ctx
              "Ill-formed call for magic-macroexpand: ~x0"
              x))))

(defun magic-ev-safe (x alist state hard-errp aokp)
  (declare (xargs :stobjs state :guard t))
  (cond ((and (pseudo-termp x)
              (symbol-alistp alist))
         (magic-ev x alist state hard-errp aokp))
        (t (er-cmp "Found magic-ev guard violation for the call:~|~%~x0"
                   `(magic-ev-safe ,x ,alist state ,hard-errp ,aokp)))))

(defun magic-macroexpand1 (x macro-body ctx wrld state-vars state)

; This logic-mode function is based on ACL2 source function macroexpand1-cmp.

  (declare (xargs :stobjs state
                  :guard-hints (("Goal" :do-not-induct t))
                  :guard (and (true-listp x)
                              (symbolp (car x))
                              (plist-worldp wrld)
                              (pseudo-termp (fgetprop (car x) 'guard *t*
                                                      wrld)))))
  (er-let*-cmp
   ((alist
; The ec-call wrapper below could probably be eliminated if we add to the
; :guard above to reflect the guard on bind-macro-args.
     (ec-call (bind-macro-args (macro-args (car x) wrld) x wrld state-vars))))
   (cond
    ((not (symbol-alistp alist)) ; impossible
     (er-cmp ctx
             "Impossible case in magic-macroexpand1 (not a symbol-alistp)."))
    (t
     (mv-let (erp guard-val)
       (magic-ev (getpropc (car x) 'guard *t* wrld)
                 alist
                 state
                 nil   ; hard-error-returns-nilp
                 nil   ; aokp
                 )
       (cond
        (erp (er-cmp ctx
                     "In the attempt to macroexpand the form ~x0 evaluation ~
                        of the guard for ~x2 caused the following ~
                        error:~|~%~@1"
                     x
                     guard-val
                     (car x)))
        ((null guard-val)
         (magic-macro-guard-er-msg x ctx wrld))
        (t (mv-let (erp expansion)
             (magic-ev-safe macro-body alist state nil nil)
             (cond (erp
                    (er-cmp ctx
                            "In the attempt to macroexpand the form ~x0, ~
                               evaluation of the macro body caused the ~
                               following error:~|~%~@1"
                            x
                            expansion))
                   (t (value-cmp expansion)))))))))))

(defun magic-macroexpand-rec (form ctx wrld state bound)

; This logic-mode function is based on ACL2 source function macroexpand1-cmp.

  (declare (xargs :stobjs state
                  :measure (nfix bound)
                  :guard-hints (("Goal" :in-theory (enable state-p1)))
                  :guard (and (plist-worldp wrld)
                              (natp bound))))
  (cond ((zp bound)
         (er-cmp ctx
                 "The attempt to macroexpand the form ~x0 seems to have led ~
                  to an infinite loop."
                 form))
        ((not (true-listp form))
         (er-cmp ctx
                 "The attempt to macroexpand the form ~x0 has failed because ~
                  it is not a true list."
                 form))
        ((not (symbolp (car form))) ; could be a lambda; just return
         (value-cmp form))
        ((not (pseudo-termp (fgetprop (car form) 'guard *t* wrld)))
         (er-cmp ctx
                 "The attempt to macroexpand the form ~x0 has failed --
                  SURPRISINGLY -- because ~x1
                  has a guard, ~x2, that is not a pseudo-termp."
                 form
                 (car form)
                 (fgetprop (car form) 'guard *t* wrld)))
        (t (let ((macro-body (getpropc (car form) 'macro-body nil wrld)))
             (cond (macro-body
                    (er-let*-cmp
                     ((new-form
                       (magic-macroexpand1 form macro-body ctx wrld
                                           (default-state-vars t)
                                           state)))
                     (magic-macroexpand-rec new-form ctx wrld state
                                            (1- bound))))
                   (t (value-cmp form)))))))

(defun magic-macroexpand (form ctx wrld state)
  (declare (xargs :stobjs state
                  :guard (plist-worldp wrld)))
  (magic-macroexpand-rec form ctx wrld state
; arbitrary recursion limit
                         1000))

; A little test

(local
 (encapsulate
   ()
   (defmacro my-mac (a b) `(* ,a ,b))
   (assert-event
    (mv-let (erp val)
      (magic-macroexpand '(my-mac x y) 'top (w state) state)
      (and (null erp)
           (equal val
                  '(BINARY-* X Y)))))))

