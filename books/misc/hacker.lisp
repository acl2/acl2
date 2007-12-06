;; hacker.lisp
;;
;; Functions for extending ACL2 in ways that are potentially unsound
;;
;; By Peter C. Dillinger with contributions by Matt Kaufmann
;;
;; Last modified: 17 April 2007


#|
(defpkg "ACL2-HACKER"
 (append
  '(; things we want from ACL2 package that aren't in *acl2-exports*:
    value set-w!
    ld-evisc-tuple connected-book-directory guard-checking-on
    inhibit-output-lst print-clause-ids acl2-raw-mode-p 
    raw-mode-restore-lst saved-output-token-lst tainted-okp
    in-package-fn defpkg-fn pe! trans! pso pso! value-triple
    default-evisc-tuple

    progn! untouchable-fns untouchable-vars ld-redefinition-action
    set-ld-skip-proofsp set-ld-redefinition-action set-ld-prompt
    set-ld-keyword-aliases set-ld-pre-eval-filter set-ld-error-triples
    set-ld-error-action set-ld-query-control-alist set-cbd-fn
    set-raw-mode set-raw-mode-fn set-tainted-okp
    push-untouchable-fn remove-untouchable-fn
    set-raw-mode-on set-raw-mode-off temp-touchable-vars temp-touchable-fns
    set-temp-touchable-vars set-temp-touchable-fns
    
    global-value current-acl2-world ld-level *wormholep* raw-mode-p
    max-absolute-event-number getprop er-let* *valid-output-names*
    state-global-let* extension absolute-to-relative-command-number
    access-command-tuple-number global-set-lst command-number-baseline
    event-number-baseline next-absolute-command-number add-command-landmark
    next-absolute-event-number add-event-landmark scan-to-command
    certify-book-fn f-get-global f-put-global f-boundp-global
    checkpoint-processors global-val)
    
  '(; defined here and "exported" to ACL2 package:
    hacker ; documentation topic
    push+touchable
    push=touchable
    push-all-touchable
    pop-touchable
    progn+touchable
    with-touchable ; alias
    progn+redef
    with-redef-allowed ; alias
    in-raw-mode
    with-raw-mode ; alias
    hacker-defun
    modify-raw-defun
    copy-defun
    redef-rewrite)
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)))

|#

(in-package "ACL2-HACKER")

(defdoc hacker
  ":Doc-Section hacker
  
  functions for extending ACL2 in ways that are potentially unsound.~/
  
  These functions typically require an active ttag (~l[defttag]) to work.~/
  ~/")

(program)
(set-state-ok t)

;=========== some auxiliary definitions ===========

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
  (declare (xargs :mode :program))
  (if (and (consp args-rest)
           (keywordp (car args-rest))
           (consp (cdr args-rest)))
    (transpose-keyword-args1 (cddr args-rest)
                            (list* (car args-rest)
                                   (cadr args-rest)
                                   kargs-sofar))
    (cons args-rest kargs-sofar)))

(defun transpose-keyword-args (args)
  (declare (xargs :mode :program))
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
  ":Doc-Section hacker
  
  add some fns/vars to those temporarily touchable, remembering previous setting.~/

  ~bv[]
  Examples:
  (push+touchable :fns :all :vars :all)  ; like push-all-touchable
  (push+touchable :fns set-w :vars :initial)
  (push+touchable :vars (foo :initial bar))
  ~ev[] ~/
  
  This event first pushes the previous temporary touchable settings
  (functions and variables) onto a stack (stored in a global variable)
  and then adds all those that meet the specification passed in.
  
  ~ilc[pop-touchable] reinstates the previous setting.
  
  An active ttag is required to use this form (~l[defttag]) because it
  can render ACL2 unsound (~l[remove-untouchable]).
  ~/"
  `(progn! (push-temp-touchables state)
           (set-temp-touchable-vars
            (add-temp-touchable-aliases ',vars (@ temp-touchable-vars) nil)
            state)
           (set-temp-touchable-fns
            (add-temp-touchable-aliases ',fns (@ temp-touchable-fns) t)
            state)))

;for export
(defmacro push=touchable (&key vars fns)
  ":Doc-Section hacker
  
  set which fns/vars are temporarily touchable, remembering previous setting.~/

  ~bv[]
  Examples:
  (push=touchable :fns :all :vars :all)  ; like push-all-touchable
  (push=touchable :fns set-w :vars :initial)
  (push=touchable :vars (foo :initial bar)) ;``:fns ()'' default
  ~ev[] ~/
  
  This event first pushes the previous temporary touchable settings
  (functions and variables) onto a stack (stored in a global variable)
  and then sets them to the specification passed in.
  
  ~ilc[pop-touchable] reinstates the previous setting.
  
  An active ttag is required to use this form (~l[defttag]) because it
  can render ACL2 unsound (~l[remove-untouchable]).
  ~/"
  `(progn! (push-temp-touchables state)
           (set-temp-touchable-vars
            (add-temp-touchable-aliases ',vars nil nil)
            state)
           (set-temp-touchable-fns
            (add-temp-touchable-aliases ',fns nil t)
            state)))

;for export
(defmacro push-all-touchable ()
  ":Doc-Section hacker
  
  make all fns/vars temporarily touchable, remembering previous setting.~/

  ~bv[]
  Usage:
  (push-all-touchable)
  ~ev[] ~/
  
  This event first pushes the previous temporary touchable settings
  (functions and variables) onto a stack (stored in a global variable)
  and then sets them to make everything temporarily touchable.
  
  ~ilc[pop-touchable] reinstates the previous setting.  ~ilc[push+touchable]
  and ~ilc[push=touchable] allow more more specification of what should be
  permitted.
  
  An active ttag is required to use this form (~l[defttag]) because it
  can render ACL2 unsound (~l[remove-untouchable]).
  ~/"
  `(progn! (push-temp-touchables state)
           (set-temp-touchable-vars t state)
           (set-temp-touchable-fns t state)))

;for export
(defmacro pop-touchable ()
  ":Doc-Section hacker
  
  revert the effect of a push+touchable, push=touchable, or push-all-touchable.~/

  ~bv[]
  Usage:
  (pop-touchable)
  ~ev[] ~/
  
  This event pops of the stack of saved temporary touchable settings,
  reverting the effect of a ~ilc[push+touchable], ~ilc[push=touchable], or
  ~ilc[push-all-touchable].
  
  An active ttag is required to use this form (~l[defttag]) because it
  can render ACL2 unsound (~l[remove-untouchable]).
  ~/"
  `(progn! (er-let*
        ((to-restore (pop-temp-touchables state)))
        (pprogn (set-temp-touchable-vars (car to-restore) state)
            (set-temp-touchable-fns  (cdr to-restore) state)
            (value ':invisible)))))

;helper for progn+touchable and progn=touchable
(defmacro progn-touchable-keyword (addp form-lst &key vars fns)
  (declare (xargs :guard form-lst))
  `(progn! :state-global-bindings
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
           (progn . ,form-lst)))

;for export
(defmacro progn+touchable (&rest args)
  ":Doc-Section hacker
  
  execute some events with some additional fns and/or vars made temporarily touchable.~/

  ~bv[]
  Examples:
  (progn+touchable :all ; same as :fns :all :vars :all
    (defun foo ...)
    (defun bar ...))
  (progn+touchable :vars (current-package ld-skip-proofsp)
    ...)
  (progn+touchable :fns :all
    ...)
  (progn+touchable :fns set-w :vars :all
    ...)
  ~ev[] ~/

  This is like ~ilc[progn] except that it surrounds the events with code to
  add certain fns and/or vars to those that are temporarily touchable.
  
  Related to ~ilc[progn=touchable].
  
  An active ttag is required to use this form (~l[defttag]) because it
  can render ACL2 unsound (~l[remove-untouchable]).
  
  Note that the syntax for this macro is not quite like traditional
  keyword arguments, which would come at the end of the argument list.
  ~/"
  (declare (xargs :guard (and (consp args)
                              (keywordp (car args)))))
  (if (not (member-eq (car args) '(:vars :fns)))
    `(progn-touchable-keyword t ,(cdr args)
                              :vars ,(car args)
                              :fns ,(car args))
    `(progn-touchable-keyword t . ,(transpose-keyword-args args))))

(defmacro progn=touchable (&rest args)
  ":Doc-Section hacker
  
  execute some events with only the specified fns and/or vars temporarily touchable.~/

  ~bv[]
  Examples:
  (progn=touchable :all ; same as :fns :all :vars :all
    (defun foo ...)
    (defun bar ...))
  (progn=touchable :vars (current-package ld-skip-proofsp) ; :fns ()  implied
    ...)  
  (progn=touchable :fns :all    ; :vars ()  implied
    ...)
  (progn=touchable :fns set-w :vars :all
    ...)
  ~ev[] ~/

  This is like ~ilc[progn] except that it surrounds the events with code to
  set only certain fns and/or vars as temporarily touchable.
  
  Related to ~ilc[progn+touchable].
  
  An active ttag is required to use this form (~l[defttag]) because it
  can render ACL2 unsound (~l[remove-untouchable]).
  
  Note that the syntax for this macro is not quite like traditional
  keyword arguments, which would come at the end of the argument list.
  ~/"
  (declare (xargs :guard (and (consp args)
                              (keywordp (car args)))))
  (if (not (member-eq (car args) '(:vars :fns)))
    `(progn-touchable-keyword nil ,(cdr args)
                              :vars ,(car args)
                              :fns ,(car args))
    `(progn-touchable-keyword nil . ,(transpose-keyword-args args))))

; for export
(defmacro with-touchable (&rest args)
  ":Doc-Section hacker
  
  execute some events but with certain untouchables removed.
  ~/~/
  Same as ~c[progn+touchable]. ~l[progn+touchable]."
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
  `(progn! :state-global-bindings
           ((ld-redefinition-action
             ,(if (eq spec :unspecified)
                  '(@ ld-redefinition-action)
                `(expand-redef-action-aliases ',spec))
             put-ld-redefinition-action))
           (progn . ,form-lst)))

; for export
(defmacro progn+redef (&rest args)
  ":Doc-Section hacker
  
  execute some events but with redefinition enabled.~/

  ~bv[]
  Examples (all equivalent):
  (progn+redef
    (defun foo ...)
    (defun bar ...))
  (progn+touchable :action t 
    ...)
  (progn+touchable :action (:doit! . :overwrite)
    ...)
  ~ev[] ~/
  
  This is like ~ilc[progn] except that it sets the
  ~ilc[ld-redefinition-action] as (optionally) specified for the
  given events.  An ~c[:action] of ~c[t] is a shortcut for
  ~c[(:doit! . :overwrite)].  ~ilc[make-event] is used to save and restore
  the old value of ~ilc[ld-redefinition-action].
  
  An active ttag is required to use this form (~l[defttag]).
  
  Note that the syntax for this macro is not quite like traditional
  keyword arguments, which would come at the end of the argument list.
  ~/"
  (declare (xargs :guard (consp args)))
  (if (and (equal (car args) :action)
           (consp (cdr args)))
    `(progn+redef-action ,(cadr args) . ,(cddr args))
    `(progn+redef-action t . ,args)))

; for export
(defmacro with-redef-allowed (&rest args)
  ":Doc-Section hacker
  
  execute some events but with redefinition enabled.
  ~/~/
  Same as ~c[progn+redef]. ~l[progn+redef]."
  `(progn+redef . ,args))

; for export
(defmacro acl2::temporary-redef (&rest forms)
  (declare (ignore forms))
  (hard-error 'acl2::temporary-redef "Old implementation of ~x0 was flawed.  Adapt solution to use ~x1 (See :DOC ~x1)."
              '((#\0 . acl2::temporary-redef)
                (#\1 . progn+redef))))



;=========== begin raw mode stuff ===========

; for export
(defmacro in-raw-mode (&rest form-lst)
  ":Doc-Section hacker
  
  embed some raw lisp code as an event.~/

  ~bv[]
  Example Form:
  (in-raw-mode
    (format t \"Preparing to load file...~~%\")
    (load \"my-file.lisp\"))~/

  General Form:
  (in-raw-mode form1 form2 ... formk)
  ~ev[]
  where each ~c[formi] is processed as though all the forms are preceded by
  ~c[:]~ilc[set-raw-mode]~c[ t].  Thus, the forms need not be ~il[events]; they
  need not even be legal ACL2 forms.  ~l[set-raw-mode] for a discussion of the
  so-called ``raw mode'' under which the forms are evaluated ~-[] unless raw
  mode is disabled by one of the forms, for example, ~c[(set-raw-mode nil)], in
  which case evaluation resumes in non-raw mode.

  WARNING: Thus, an ~c[in-raw-mode] form is potentially very dangerous!  For
  example, you can use it to call the Common Lisp ~c[load] function to load
  arbitrary Common Lisp code, perhaps even overwriting definitions of ACL2
  system functions!  Thus, as with ~ilc[set-raw-mode], ~ilc[in-raw-mode] may
  not be evaluated unless there is an active trust tag in effect.  ~l[defttag].

  Note that the normal undoing mechanism (~pl[ubt]) is not supported when raw
  mode is used.
  ~/"
  `(progn! (set-raw-mode-on state)
           ,@form-lst
           ;;acl2-raw-mode-p is restored by progn!-fn
           ))

; for export
(defmacro with-raw-mode (&rest args)
  ":Doc-Section hacker
  
  embed some raw lisp code as an event.
  ~/~/
  Same as ~c[in-raw-mode]. ~l[in-raw-mode]."
  `(in-raw-mode . ,args))

