#|$ACL2s-Preamble$;
;; hacker.lisp
;;
;; Functions for extending ACL2 in ways that are potentially unsound
;;
;; By Peter C. Dillinger with contributions by Matt Kaufmann
;;
;; Last modified:


(ld ;; Newline to fool dependency scanner
  "hacker-pkg.lsp")

(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2-HACKER")

(program)
(set-state-ok t)

;=========== some auxiliary definitions ===========

; the special progn! support for doing state-global bindings was changed between
; 3.2 and 3.2.1.  We define progn!-with-bindings to use the right one.
(make-event
 (if (earlier-acl2-versionp "ACL2 Version 3.2" (@ acl2-version)) ; >= 3.2.1
   (value
    '(defmacro progn!-with-bindings (bindings &rest rst)
       `(progn! :state-global-bindings ,bindings . ,rst)))
   (value
    '(defmacro progn!-with-bindings (bindings &rest rst)
       `(progn! (state-global-let* ,bindings (progn! . ,rst)))))))

; read a state global or return a default value (defaulting to nil) if unbound
(defmacro @opt (var &optional deflt)
  `(if (boundp-global ',var state)
     (f-get-global ',var state)
     ,deflt))

; like common lisp WHEN, but uses ACL2 error triples
(defmacro er-when (test form &rest more-forms)
  `(if ,test
     (er-progn ,form . ,more-forms)
     (value :invisible)))

; to enable definition of macros that use keyword arguments at the beginning
(defun transpose-keyword-args1 (args-rest kargs-sofar)
  (if (and (consp args-rest)
           (keywordp (car args-rest))
           (consp (cdr args-rest)))
    (transpose-keyword-args1 (cddr args-rest)
                            (list* (car args-rest)
                                   (cadr args-rest)
                                   kargs-sofar))
    (cons args-rest kargs-sofar)))

(defun transpose-keyword-args (args)
  (transpose-keyword-args1 args nil))



;=========== begin touchable stuff ===========

; union in the specification language of temp-untouchable-{vars,fns}
(defun union-eq-with-top (a b)
  (if (or (eq a t) (eq b t))
    t
    (union-eq a b)))

; used for temp-touchable specifications
(defun add-temp-touchable-aliases (spec sofar fn-p)
  (declare (xargs :guard (booleanp fn-p)))
  (if (null spec)
    sofar
    (let ((sym (if (consp spec) (car spec) spec))
          (rest (if (consp spec) (cdr spec) nil)))
      (add-temp-touchable-aliases
       rest
       (union-eq-with-top
        (cond ((eq sym :all)
               t)
              ((eq sym :initial)
               (if fn-p
                 acl2::*initial-untouchable-fns*
                 acl2::*initial-untouchable-vars*))
              (t
               (list sym)))
        sofar)
       fn-p))))

#|; flawed in terms of undoing

; defines a stack of saved untouchables
(defun push-temp-touchables (state)
  (f-put-global 'saved-temp-touchables
                (cons (cons (@ temp-touchable-vars)
                            (@ temp-touchable-fns))
                      (@opt saved-temp-touchables))
                state))

(defun pop-temp-touchables (state)
  (if (and (boundp-global 'saved-temp-touchables state)
           (consp (@ saved-temp-touchables)))
    (let ((result (car (@ saved-temp-touchables))))
      (pprogn (f-put-global 'saved-temp-touchables
                            (cdr (@ saved-temp-touchables))
                            state)
              (value result)))
    (er soft 'pop-temp-touchables
        "Stack of temp-touchables is empty.")))

(push-untouchable saved-temp-touchables nil)

;for export
(defmacro push+touchable (&key vars fns)

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file dillinger-et-al-xdoc.lisp.

; ":Doc-Section hacker
;
; add some fns/vars to those temporarily touchable, remembering previous setting.~/

; ~bv[]
; Examples:
; (push+touchable :fns :all :vars :all)  ; like push-all-touchable
; (push+touchable :fns set-w :vars :initial)
; (push+touchable :vars (foo :initial bar))
; ~ev[] ~/
;
; This event first pushes the previous temporary touchable settings
; (functions and variables) onto a stack (stored in a global variable)
; and then adds all those that meet the specification passed in.
;
; ~ilc[pop-touchable] reinstates the previous setting.
;
; An active ttag is required to use this form (~l[defttag]) because it
; can render ACL2 unsound (~l[remove-untouchable]).
; ~/"
  `(progn! (push-temp-touchables state)
           (set-temp-touchable-vars
            (add-temp-touchable-aliases ',vars (@ temp-touchable-vars) nil)
            state)
           (set-temp-touchable-fns
            (add-temp-touchable-aliases ',fns (@ temp-touchable-fns) t)
            state)))

;for export
(defmacro push=touchable (&key vars fns)

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file dillinger-et-al-xdoc.lisp.

; ":Doc-Section hacker
;
; set which fns/vars are temporarily touchable, remembering previous setting.~/

; ~bv[]
; Examples:
; (push=touchable :fns :all :vars :all)  ; like push-all-touchable
; (push=touchable :fns set-w :vars :initial)
; (push=touchable :vars (foo :initial bar)) ;``:fns ()'' default
; ~ev[] ~/
;
; This event first pushes the previous temporary touchable settings
; (functions and variables) onto a stack (stored in a global variable)
; and then sets them to the specification passed in.
;
; ~ilc[pop-touchable] reinstates the previous setting.
;
; An active ttag is required to use this form (~l[defttag]) because it
; can render ACL2 unsound (~l[remove-untouchable]).
; ~/"
  `(progn! (push-temp-touchables state)
           (set-temp-touchable-vars
            (add-temp-touchable-aliases ',vars nil nil)
            state)
           (set-temp-touchable-fns
            (add-temp-touchable-aliases ',fns nil t)
            state)))

;for export
(defmacro push-all-touchable ()

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file dillinger-et-al-xdoc.lisp.

; ":Doc-Section hacker
;
; make all fns/vars temporarily touchable, remembering previous setting.~/

; ~bv[]
; Usage:
; (push-all-touchable)
; ~ev[] ~/
;
; This event first pushes the previous temporary touchable settings
; (functions and variables) onto a stack (stored in a global variable)
; and then sets them to make everything temporarily touchable.
;
; ~ilc[pop-touchable] reinstates the previous setting.  ~ilc[push+touchable]
; and ~ilc[push=touchable] allow more more specification of what should be
; permitted.
;
; An active ttag is required to use this form (~l[defttag]) because it
; can render ACL2 unsound (~l[remove-untouchable]).
; ~/"
  `(progn! (push-temp-touchables state)
           (set-temp-touchable-vars t state)
           (set-temp-touchable-fns t state)))

;for export
(defmacro pop-touchable ()

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file dillinger-et-al-xdoc.lisp.

; ":Doc-Section hacker
;
; revert the effect of a push+touchable, push=touchable, or push-all-touchable.~/

; ~bv[]
; Usage:
; (pop-touchable)
; ~ev[] ~/
;
; This event pops of the stack of saved temporary touchable settings,
; reverting the effect of a ~ilc[push+touchable], ~ilc[push=touchable], or
; ~ilc[push-all-touchable].
;
; An active ttag is required to use this form (~l[defttag]) because it
; can render ACL2 unsound (~l[remove-untouchable]).
; ~/"
  `(progn! (er-let*
        ((to-restore (pop-temp-touchables state)))
        (pprogn (set-temp-touchable-vars (car to-restore) state)
            (set-temp-touchable-fns  (cdr to-restore) state)
            (value ':invisible)))))
;|#

;helper for progn+touchable and progn=touchable
(defmacro progn-touchable-keyword (bangp addp form-lst &key vars fns)
  (declare (xargs :guard form-lst))
  `(progn!-with-bindings
            ((temp-touchable-vars
              (add-temp-touchable-aliases ',vars
                                          ,(if addp
                                             '(@ temp-touchable-vars)
                                             'nil)
                                          nil)
              set-temp-touchable-vars)
             (temp-touchable-fns
              (add-temp-touchable-aliases ',fns
                                          ,(if addp
                                             '(@ temp-touchable-fns)
                                             'nil)
                                          't)
              set-temp-touchable-fns))
            . ,(if bangp
                 form-lst
                 `((progn . ,form-lst)))))

;for export
(defmacro progn+touchable (&rest args)

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file dillinger-et-al-xdoc.lisp.

; ":Doc-Section hacker
;
; execute some events with some additional fns and/or vars made temporarily touchable.~/

; ~bv[]
; Examples:
; (progn+touchable :all ; same as :fns :all :vars :all
;   (defun foo ...)
;   (defun bar ...))
; (progn+touchable :vars (current-package ld-skip-proofsp)
;   ...)
; (progn+touchable :fns :all
;   ...)
; (progn+touchable :fns set-w :vars :all
;   ...)
; ~ev[] ~/

; This is like ~ilc[progn] except that it surrounds the events with code to
; add certain fns and/or vars to those that are temporarily touchable.
;
; Related to ~ilc[progn=touchable].
;
; An active ttag is required to use this form (~l[defttag]) because it
; can render ACL2 unsound (~l[remove-untouchable]).
;
; Note that the syntax for this macro is not quite like traditional
; keyword arguments, which would come at the end of the argument list.
; ~/"
  (declare (xargs :guard (and (consp args)
                              (keywordp (car args)))))
  (if (not (member-eq (car args) '(:vars :fns)))
    `(progn-touchable-keyword nil t ,(cdr args)
                              :vars ,(car args)
                              :fns ,(car args))
    `(progn-touchable-keyword nil t . ,(transpose-keyword-args args))))

(defmacro progn=touchable (&rest args)

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file dillinger-et-al-xdoc.lisp.

; ":Doc-Section hacker
;
; execute some events with only the specified fns and/or vars temporarily touchable.~/

; ~bv[]
; Examples:
; (progn=touchable :all ; same as :fns :all :vars :all
;   (defun foo ...)
;   (defun bar ...))
; (progn=touchable :vars (current-package ld-skip-proofsp) ; :fns ()  implied
;   ...)
; (progn=touchable :fns :all    ; :vars ()  implied
;   ...)
; (progn=touchable :fns set-w :vars :all
;   ...)
; ~ev[] ~/

; This is like ~ilc[progn] except that it surrounds the events with code to
; set only certain fns and/or vars as temporarily touchable.
;
; Related to ~ilc[progn+touchable].
;
; An active ttag is required to use this form (~l[defttag]) because it
; can render ACL2 unsound (~l[remove-untouchable]).
;
; Note that the syntax for this macro is not quite like traditional
; keyword arguments, which would come at the end of the argument list.
; ~/"
  (declare (xargs :guard (and (consp args)
                              (keywordp (car args)))))
  (if (not (member-eq (car args) '(:vars :fns)))
    `(progn-touchable-keyword nil nil ,(cdr args)
                              :vars ,(car args)
                              :fns ,(car args))
    `(progn-touchable-keyword nil nil . ,(transpose-keyword-args args))))

; for export
(defmacro progn!+touchable (&rest args)
  (declare (xargs :guard (and (consp args)
                              (keywordp (car args)))))
  (if (not (member-eq (car args) '(:vars :fns)))
    `(progn-touchable-keyword t t ,(cdr args)
                              :vars ,(car args)
                              :fns ,(car args))
    `(progn-touchable-keyword t t . ,(transpose-keyword-args args))))

; for export
(defmacro progn!=touchable (&rest args)
  (declare (xargs :guard (and (consp args)
                              (keywordp (car args)))))
  (if (not (member-eq (car args) '(:vars :fns)))
    `(progn-touchable-keyword t nil ,(cdr args)
                              :vars ,(car args)
                              :fns ,(car args))
    `(progn-touchable-keyword t nil . ,(transpose-keyword-args args))))

; for export
(defmacro with-touchable (&rest args)

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file dillinger-et-al-xdoc.lisp.

; ":Doc-Section hacker
;
; execute some events but with certain untouchables removed.
; ~/~/
; Same as ~c[progn+touchable]. ~l[progn+touchable]."
  `(progn+touchable . ,args))



;=========== begin redef stuff ===========

(defun put-ld-redefinition-action (v state)
  (mv-let (erp v state)
      (set-ld-redefinition-action v state)
      (declare (ignore v))
      (prog2$
       (and erp
        (hard-error 'put-ld-redefinition-action
                "~x0 returned an error."
                '((#\0 . set-ld-redefinition-action))))
       state)))

(defun expand-redef-action-aliases (spec)
  (cond ((equal spec t)
         '(:doit! . :overwrite))
        (t
         spec)))

(defmacro progn+redef-action (spec &rest form-lst)
  (declare (xargs :guard form-lst))
  `(progn!-with-bindings
    ((ld-redefinition-action
      ,(if (eq spec :unspecified)
         '(@ ld-redefinition-action)
         `(expand-redef-action-aliases ',spec))
      put-ld-redefinition-action))
    (progn . ,form-lst)))

; for export
(defmacro progn+redef (&rest args)

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file dillinger-et-al-xdoc.lisp.

; ":Doc-Section hacker
;
; execute some events but with redefinition enabled.~/

; ~bv[]
; Examples (all equivalent):
; (progn+redef
;   (defun foo ...)
;   (defun bar ...))
; (progn+redef :action t
;   ...)
; (progn+redef :action (:doit! . :overwrite)
;   ...)
; ~ev[] ~/
;
; This is like ~ilc[progn] except that it sets the
; ~ilc[ld-redefinition-action] as (optionally) specified for the
; given events.  An ~c[:action] of ~c[t] is a shortcut for
; ~c[(:doit! . :overwrite)].  ~ilc[make-event] is used to save and restore
; the old value of ~ilc[ld-redefinition-action].
;
; An active ttag is required to use this form (~l[defttag]).
;
; Note that the syntax for this macro is not quite like traditional
; keyword arguments, which would come at the end of the argument list.
; ~/"
  (declare (xargs :guard (consp args)))
  (if (and (equal (car args) :action)
           (consp (cdr args)))
    `(progn+redef-action ,(cadr args) . ,(cddr args))
    `(progn+redef-action t . ,args)))

; for export
(defmacro with-redef-allowed (&rest args)

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file dillinger-et-al-xdoc.lisp.

; ":Doc-Section hacker
;
; execute some events but with redefinition enabled.
; ~/~/
; Same as ~c[progn+redef]. ~l[progn+redef]."
  `(progn+redef . ,args))

; for export
; this is a wart from an older version of hacker.lisp
(defmacro acl2::temporary-redef (&rest forms)
  (declare (ignore forms))
  (hard-error 'acl2::temporary-redef "Old implementation of ~x0 was flawed.  Adapt solution to use ~x1 (See :DOC ~x1)."
              '((#\0 . acl2::temporary-redef)
                (#\1 . progn+redef))))



;=========== begin raw mode stuff ===========

; for export
(defmacro in-raw-mode (&rest form-lst)

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file dillinger-et-al-xdoc.lisp.

; ":Doc-Section hacker
;
; embed some raw lisp code as an event.~/

; ~bv[]
; Example Form:
; (in-raw-mode
;   (format t \"Preparing to load file...~~%\")
;   (load \"my-file.lisp\"))~/

; General Form:
; (in-raw-mode form1 form2 ... formk)
; ~ev[]
; where each ~c[formi] is processed as though all the forms are preceded by
; ~c[:]~ilc[set-raw-mode]~c[ t].  Thus, the forms need not be ~il[events]; they
; need not even be legal ACL2 forms.  ~l[set-raw-mode] for a discussion of the
; so-called ``raw mode'' under which the forms are evaluated ~-[] unless raw
; mode is disabled by one of the forms, for example, ~c[(set-raw-mode nil)], in
; which case evaluation resumes in non-raw mode.

; WARNING: Thus, an ~c[in-raw-mode] form is potentially very dangerous!  For
; example, you can use it to call the Common Lisp ~c[load] function to load
; arbitrary Common Lisp code, perhaps even overwriting definitions of ACL2
; system functions!  Thus, as with ~ilc[set-raw-mode], ~ilc[in-raw-mode] may
; not be evaluated unless there is an active trust tag in effect.  ~l[defttag].

; Note that the normal undoing mechanism (~pl[ubt]) is not supported when raw
; mode is used.
; ~/"
  `(progn! (with-output :off observation (set-raw-mode-on state))
           (progn
             ,@form-lst
             nil)
           ;;acl2-raw-mode-p is restored by progn!-fn
           ))

; for export
(defmacro with-raw-mode (&rest args)

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file dillinger-et-al-xdoc.lisp.

; ":Doc-Section hacker
;
; embed some raw lisp code as an event.
; ~/~/
; Same as ~c[in-raw-mode]. ~l[in-raw-mode]."
  `(in-raw-mode . ,args))


;=========== begin program-only stuff ===========

; for export
(defmacro ensure-program-only-flag (&rest fn-lst)

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file dillinger-et-al-xdoc.lisp.

; ":Doc-Section hacker
;
; ensure that given function names remain in :PROGRAM mode.~/

; ~bv[]
; Example Form:
; (ensure-program-only-flag my-fn your-fn)~/

; General Form:
; (ensure-program-only-flag fn1 fn2 ... fnk)
; ~ev[]
; where each ~c[fni] is a literal symbol which should have a ~ilc[program] mode
; definition. Each ~c[fni] not already flagged as \"program only\" is flagged
; as such.  This prevents it from being migrated to ~ilc[logic] mode or being
; used in a macro.
;
; This is a pseudo-event, meaning it can be used in an event context but does
; not (ever) change the world.
;
; Note that the normal undoing mechanism (~pl[ubt]) does not undo the effects
; of this pseudo-event.
; ~/"
  (declare (xargs :guard (and fn-lst
                              (symbol-listp fn-lst))))
  `(progn!=touchable :vars program-fns-with-raw-code
     (assign program-fns-with-raw-code
       (union-eq (@ program-fns-with-raw-code) ',fn-lst))))

; test whether a function is in :PROGRAM mode
(defun program-mode-p (fn wrld)
  (eq ':program
      (getprop fn 'symbol-class nil 'current-acl2-world wrld)))

; test whether all functions in a list are in :PROGRAM mode
(defun program-mode-p-lst (fn-lst wrld)
  (or (endp fn-lst)
      (and (program-mode-p     (car fn-lst) wrld)
           (program-mode-p-lst (cdr fn-lst) wrld))))

; for export
(defmacro assert-program-mode (&rest fn-lst)

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file dillinger-et-al-xdoc.lisp.

; ":Doc-Section hacker
;
; assert that given symbols name :PROGRAM mode functions.~/

; ~bv[]
; Example Form:
; (assert-program-mode my-fn your-fn)~/

; General Form:
; (assert-program-mode fn1 fn2 ... fnk)
; ~ev[]
; where each ~c[fni] is a literal symbol which should have a ~ilc[program] mode
; definition. An error is raised if any ~c[fni] is not a program mode function.
;
; This is a pseudo-event, meaning it can be used in an event context but does
; not (ever) change the world.
; ~/"
  (declare (xargs :guard (and fn-lst
                              (symbol-listp fn-lst))))
  `(assert-event
    (program-mode-p-lst ',fn-lst (w state))
    :msg (msg "Assertion failed.  At least one not :program mode:~%~x0"
              ',fn-lst)
    :on-skip-proofs t))

; for export
(defmacro ensure-program-only (&rest fn-lst)

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file dillinger-et-al-xdoc.lisp.

; ":Doc-Section hacker
;
; ensure that named functions are and remain in :PROGRAM mode.~/

; ~bv[]
; Example Form:
; (ensure-program-only my-fn your-fn)~/

; General Form:
; (ensure-program-only fn1 fn2 ... fnk)
; ~ev[]
; where each ~c[fni] is a literal symbol which should have a ~ilc[program] mode
; definition. An error is raised if any ~c[fni] is not a program mode function.
; Also, each ~c[fni] not already flagged as \"program only\" is flagged
; as such.  This prevents it from being migrated to ~ilc[logic] mode or being
; used in a macro.
;
; This is actually a combination of ~ilc[assert-program-mode] and
; ~ilc[ensure-program-only-flag].
;
; This is a pseudo-event, meaning it can be used in an event context but does
; not (ever) change the world.
;
; Note that the normal undoing mechanism (~pl[ubt]) does not undo the effects
; of this pseudo-event.
; ~/"
  (declare (xargs :guard (and fn-lst
                              (symbol-listp fn-lst))))
  `(progn (assert-program-mode . ,fn-lst)
          (ensure-program-only-flag . ,fn-lst)))



;=========== begin special-raw-definition stuff ===========

; Here we introduce the notion of a "special raw definition",
; which is somewhat related to the notion of "program only" but
; importantly different.  The intended difference is this:
; - A function should be "program only" if bad things could happen as
;   a result of it migrating to logic mode (with verify-termination)
;   or by use in macro expansion.
; - A function should be considered to have a "special raw definition"
;   if bad things could happen as a result of replacing its raw
;   definition with the raw counterpart of its "loop" definition.
;TODO: more

(defconst *bootstrap-special-raw-definitions*
  '(
    ;;-- from axioms.lisp --
    ;;len         #|not special, just fast|#
    ;;strip-cars  #|not special, just fast|#
    ;;strip-cdrs  #|not special, just fast|#
    acl2::complex-rationalp
    acl2::must-be-equal
    acl2::zp
    acl2::zip
    acl2::prog2$
    acl2::time$
    acl2::hard-error
    acl2::intern-in-package-of-symbol
    acl2::pkg-witness
    acl2::with-output
    acl2::value-triple-fn
    acl2::value-triple
    acl2::pprogn
    acl2::acl2-unwind-protect
    acl2::defund
    acl2::plist-worldp
    acl2::getprop-default
    acl2::fgetprop
    acl2::sgetprop
    acl2::getprops
    acl2::has-propsp
    acl2::extend-world
    acl2::retract-world
    acl2::array-1p
    acl2::array-2pz
    acl2::header
    acl2::aref1
    acl2::compress1
    acl2::aset1
    acl2::aref2
    acl2::compress2
    acl2::aset2
    acl2::flush-compress
    acl2::state-p1
    acl2::global-table-cars1
    acl2::boundp-global1
    acl2::fboundp-global
    acl2::makunbound-global
    acl2::get-global
    acl2::f-get-global
    acl2::put-global
    acl2::f-put-global
    acl2::zpf
    acl2::open-input-channel-p1
    acl2::open-output-channel-p1
    acl2::princ$
    acl2::write-byte$
    acl2::print-object$-fn ; Matt K. change shortly after v4-3 and again 7/2021
    acl2::open-input-channel
    acl2::close-input-channel
    acl2::open-output-channel
    acl2::close-output-channel
    acl2::read-char$
    acl2::peek-char$
    acl2::read-byte$
    acl2::read-object
    acl2::prin1-with-slashes
    acl2::may-need-slashes
    acl2::t-stack-length1
    acl2::extend-t-stack
    acl2::shrink-t-stack
    acl2::aref-t-stack
    acl2::aset-t-stack
    acl2::32-bit-integer-stack-length1
    acl2::extend-32-bit-integer-stack
    acl2::shrink-32-bit-integer-stack
    acl2::aref-32-bit-integer-stack
    acl2::aset-32-bit-integer-stack
    acl2::f-big-clock-negative-p
    acl2::f-decrement-big-clock
    acl2::big-clock-negative-p
    acl2::decrement-big-clock
    acl2::list-all-package-names
    acl2::user-stobj-alist
    acl2::update-user-stobj-alist
    acl2::read-idate
    acl2::read-run-time
    acl2::read-acl2-oracle
    acl2::getenv$
    acl2::setenv$
    acl2::prin1$
    acl2::the-mv
    acl2::set-enforce-redundancy
    acl2::set-verify-guards-eagerness
    acl2::set-compile-fns
    acl2::set-measure-function
    acl2::set-well-founded-relation
    acl2::logic
    acl2::program
    acl2::set-bogus-mutual-recursion-ok
    acl2::set-irrelevant-formals-ok
    acl2::set-ignore-ok
    acl2::set-inhibit-warnings
    acl2::set-inhibit-output-lst
    acl2::set-state-ok
    acl2::set-let*-abstractionp
    acl2::set-backchain-limit
    acl2::set-default-backchain-limit
    acl2::set-rewrite-stack-limit
    acl2::set-case-split-limitations
    acl2::set-match-free-default
    acl2::add-match-free-override
    acl2::add-include-book-dir
    acl2::delete-include-book-dir
    acl2::set-non-linearp
    acl2::defttag
    acl2::set-default-hints!
    acl2::add-default-hints!
    acl2::remove-default-hints!
    acl2::with-prover-time-limit
    acl2::catch-time-limit4
    acl2::time-limit4-reached-p
    acl2::wormhole1
    acl2::wormhole-p
    acl2::abort!
    acl2::er
    acl2::mfc-clause
    acl2::mfc-rdepth
    acl2::mfc-type-alist
    acl2::mfc-ancestors
    acl2::bad-atom<=
    acl2::alphorder

    ;;-- from translate.lisp --
    acl2::latch-stobjs1
    acl2::big-n
    acl2::decrement-big-n
    acl2::zp-big-n
    acl2::w-of-any-state
    acl2::ev-fncall-rec
    acl2::ev-rec
    acl2::ev-rec-acl2-unwind-protect
    acl2::ev-fncall
    acl2::ev
    acl2::ev-lst
    acl2::ev-fncall-w
    acl2::untranslate
    acl2::untranslate-lst
    acl2::ev-w
    acl2::ev-w-lst
    acl2::user-stobj-alist-safe

    ;;-- from history-management.lisp --
    acl2::start-proof-tree
    acl2::initialize-summary-accumulators
    acl2::print-summary
    acl2::set-w
    acl2::longest-common-tail-length-rec
    acl2::chk-virgin

    ;;-- from other-events.lisp --
    in-package
    defpkg
    defchoose
    defun
    defuns
    verify-termination
    verify-guards
    defmacro
    defconst
    defstobj
    defthm
    defaxiom
    deflabel
    defdoc
    deftheory
    in-theory
    in-arithmetic-theory
    push-untouchable
    reset-prehistory
    set-body
    table
    progn
    encapsulate
    include-book
    local

    acl2::chk-package-reincarnation-import-restrictions
    acl2::theory-invariant
    acl2::acl2-raw-eval
    acl2::protected-eval-with-proofs
    acl2::include-book-fn
    acl2::write-expansion-file
    acl2::certify-book-fn
    acl2::defstobj-field-fns-raw-defs
    acl2::open-trace-file-fn
    acl2::close-trace-file-fn
    acl2::with-error-trace-fn
    acl2::trace$-fn-general
    acl2::trace$-fn-simple
    acl2::untrace$-fn
    acl2::break-on-error-fn

    ;;-- from ld.lisp --
    acl2::ld-print-results
    acl2::print-newline-for-time$
    acl2::good-bye-fn
    acl2::ld-loop
    acl2::ld-fn-body
    acl2::ld-fn
    acl2::compile-function
    acl2::comp-fn
    acl2::comp
    acl2::break$
    acl2::set-debugger-enable-fn
    acl2::mfc-ts
    acl2::mfc-rw
    acl2::mfc-rw+
    acl2::mfc-relieve-hyp
    acl2::mfc-ap
    acl2::save-exec

    ))

#|| Removed by Matt K. after ACL2 Version 3.6.1 in favor of the defmacro just
    below,  because make-event expansion does not take place during (early)
    loading of compiled files.
(make-event ; used here like progn! without a ttag
 (er-progn
  (if (member-eq 'has-special-raw-definition
                 (global-val 'untouchable-vars (w state)))
    (value nil) ; assume we're already good
    (assign has-special-raw-definition
      (union-eq (@opt has-special-raw-definition)
                *bootstrap-special-raw-definitions*)))
  (value '(value-triple 'has-special-raw-definition)))
 :check-expansion t)
||#

(defmacro update-has-special-raw-definition (fn-lst)
  `(pprogn (if (boundp-global 'has-special-raw-definition state)
               state
             (f-put-global 'has-special-raw-definition
                           *bootstrap-special-raw-definitions*
                           state))
           (assign has-special-raw-definition
                   (union-eq (@ has-special-raw-definition)
                             ,fn-lst))))

(push-untouchable has-special-raw-definition nil)

; for export
(defmacro ensure-special-raw-definition-flag (&rest fn-lst)

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file dillinger-et-al-xdoc.lisp.

; ":Doc-Section hacker
;
; ensure that named functions are flagged as having special raw definitions.~/

; ~bv[]
; Example Form:
; (ensure-special-raw-definition-flag my-fn your-fn)~/

; General Form:
; (ensure-special-raw-definition-flag fn1 fn2 ... fnk)
; ~ev[]
; where each ~c[fni] is a literal symbol which should have a function
; definition. Each ~c[fni] not already flagged as having a special raw
; definition is flagged as such.  This idicates to interested parties that
; the \"loop\" definition of the function doesn't fully characterize the
; effects it has in raw lisp.
;
; This is a pseudo-event, meaning it can be used in an event context but does
; not (ever) change the world.
;
; Note that the normal undoing mechanism (~pl[ubt]) does not undo the effects
; of this pseudo-event.
; ~/"
  (declare (xargs :guard (and fn-lst
                              (symbol-listp fn-lst))))
  `(progn!=touchable :vars has-special-raw-definition
     (update-has-special-raw-definition ',fn-lst)))

; for export
(defmacro assert-no-special-raw-definition (&rest fn-lst)

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file dillinger-et-al-xdoc.lisp.

; ":Doc-Section hacker
;
; assert that given symbols do not have a special raw function definition.~/

; ~bv[]
; Example Form:
; (assert-no-special-raw-definition my-fn your-fn)~/

; General Form:
; (assert-no-special-raw-definition fn1 fn2 ... fnk)
; ~ev[]
; where each ~c[fni] is a literal symbol.  An error is raised if any ~c[fni]
; is is flagged as having a special raw definition.
; ~l[ensure-special-raw-definition-flag].
;
; This is a pseudo-event, meaning it can be used in an event context but does
; not (ever) change the world.
; ~/"
  (declare (xargs :guard (and fn-lst
                              (symbol-listp fn-lst))))
  `(assert-event
    (not (intersectp-eq (@opt has-special-raw-definition)
                        ',fn-lst))
    :msg (msg "Assertion failed.  Flagged as having special raw definition:~%~x0"
              (intersection-eq (@opt has-special-raw-definition)
                               ',fn-lst))
    :on-skip-proofs t))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; modify-raw-defun-permanent
;
; for permanently installing some changes (supporting defcode)
;

; for export
(defmacro modify-raw-defun-permanent
  (name name-for-old ll &rest decls-and-body)
  (declare (xargs :guard (and (symbolp name)
                              (symbolp name-for-old)
                              (symbol-listp ll)
                              (consp decls-and-body))))
  `(progn
    (in-raw-mode
     (unless (fboundp ',name-for-old)
             ; if the name-for-old already has a definition, we don't override
             ; it. this provides idempotency for modify-raw-defun-permanent
             ; but means this code doesn't know the first time whether
             ; name-for-old is fresh/unused.
             (setf (symbol-function ',name-for-old)
                   (symbol-function ',name)))
     (defun ,name ,ll
       ,@ (and ll `((declare (ignorable . ,ll))))
       . ,decls-and-body))
    (ensure-special-raw-definition-flag ,name)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; deflabels
;
; for stubbing out ACL2 names
;

(defun build-deflabels (names)
  (if (endp names)
    nil
    (cons (list 'deflabel (car names))
          (build-deflabels (cdr names)))))

; for export
(defmacro deflabels (&rest names)
  `(progn
     (with-output :off summary
                  (progn . ,(build-deflabels names)))
     (value-triple ',names)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; allow other ttags
;
; this should only be used in subsuming hacker stuff, like so:
;
#|
(include-book
 "hacker/hacker")
(progn+all-ttags-allowed
 (include-book
  "hacker/all" :ttags ((defcode) (table-guard))))
(subsume-ttags-since-defttag) ; see subsumption.lisp
|#
;
; this is a work-around for subsuming before progn+subsume-ttags is available.
;

; for export
(defmacro progn+all-ttags-allowed (&rest form-lst)
  `(progn!-with-bindings
    ((temp-touchable-vars (if (eq (@ temp-touchable-vars) t)
                            t
                            (cons 'acl2::ttags-allowed (@ temp-touchable-vars)))
                          set-temp-touchable-vars))
    (progn!-with-bindings
     ((acl2::ttags-allowed :all))
     (progn!-with-bindings
      ((temp-touchable-vars (if (eq (@ temp-touchable-vars) t)
                              t
                              (cdr (@ temp-touchable-vars)))
                            set-temp-touchable-vars))
      (progn . ,form-lst)))))


#|; some tests
(defttag test1)
(progn+allow-ttags
 :all
 (defttag test2)
 (progn+touchable :all
                  (defun foo (x) (1+ x)))
 (progn! (cw "Hi!~%")))
(progn+allow-ttags
 nil
 (defttag test3)
 (progn+touchable :all
                  (defun foo (x) (1+ x)))
 (progn! (cw "Hi!~%")))
;|#


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; ttag-skip-proofs
;
; uses a ttag to skip proofs without the ordinary record that
; proofs were skipped.
;

(defun put-ld-skip-proofsp (v state)
  (mv-let (erp v state)
      (set-ld-skip-proofsp v state)
      (declare (ignore v))
      (prog2$
       (and erp
        (hard-error 'set-ld-skip-proofsp
                "~x0 returned an error."
                '((#\0 . set-ld-skip-proofsp))))
       state)))

; for export
(defmacro ttag-skip-proofs (x)
  `(progn!-with-bindings
    ((ld-skip-proofsp 'include-book put-ld-skip-proofsp))
    (progn ,x)))

; for export
(defmacro progn+ttag-skip-proofs (&rest args)
  `(progn!-with-bindings
    ((ld-skip-proofsp 'include-book put-ld-skip-proofsp))
    (progn . ,args)))
