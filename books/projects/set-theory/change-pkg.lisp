; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; The utility repkg-expr was originally used during development of the book
; schroeder-bernstein-support.lisp, as indicated in comments therein.  The idea
; of (repkg-expr x wit) is to change packages of variables, not function
; symbols, of x into the package of the symbol, wit.  It's not perfect, since
; macros can mess things up.  But it worked for my purpose, so I'll keep this
; book around in case it is useful for something else, either directly or as
; inspiration for a related tool.  The utility (make-repkg-events names pkg)
; obtains events from names and applies (repkg-expr x wit) as appropriate, more
; or less, using a symbol in pkg for wit.

(program)

(defun repkg-sym (x wit)
  (declare (xargs :guard (and (symbolp x)
                              (symbolp wit))))
  (intern-in-package-of-symbol (symbol-name x) wit))

(mutual-recursion

(defun repkg-expr (x wit)
  (declare (xargs :guard (symbolp wit)))
  (cond ((atom x)
         x)
        ((not (true-listp x)) ; for guard proof
         (er hard? 'repkg-expr
             "Unexpected non-true-list: ~x0"
             x))
        ((eq (car x) 'record-expansion)
         (repkg-expr (caddr x) wit))
        ((member-eq (car x) '(define defrule throw-nonexec-error))
         (cons (car x)
               (repkg-expr-lst (cdr x) wit)))
        ((member-eq (car x) '(let let*))
         `(,(car x)
           ,(let ((bindings (cadr x)))
              (pairlis$ (strip-cars bindings)
                        (pairlis$ (repkg-expr-lst (strip-cadrs bindings) wit)
                                  nil)))
           ,@(repkg-expr-lst (cddr x) wit)))
        ((not (symbolp (car x)))
         (er hard? 'repkg-expr
             "Unexpected non-symbol in car: ~x0"
             x))
        (t ; (consp x)
         (cons (repkg-sym (car x) wit)
               (repkg-expr-lst (cdr x) wit)))
        (t x)))

(defun repkg-expr-lst (x wit)
  (declare (xargs :guard (and (true-listp x)
                              (symbolp wit))))
  (cond ((endp x) nil)
        (t (cons (repkg-expr (car x) wit)
                 (repkg-expr-lst (cdr x) wit)))))
)

(defun repkg-event (name wit ctx state)
  (declare (xargs :guard (and (symbolp name)
                              (symbolp wit)
                              (error1-state-p state))
                  :mode :program ; because of get-event
                  :stobjs state))
  (let* ((wrld (w state))
         (ev (get-event name wrld)))
    (cond (ev (case-match ev
                (('defun name formals . rest)
                 (value `(defun ,(repkg-sym name wit) ,formals
                           ;; drop declare forms
                           ,(repkg-expr (car (last rest)) wit))))
                (('defchoose name bound-vars free-vars body . rest)
                 (value `(defchoose ,(repkg-sym name wit)
                           ,bound-vars
                           ,free-vars
                           ,(repkg-expr body wit)
                           ,@rest)))
                (& (er soft ctx
                       "Unhandled event type, ~x0"
                       ev))))
          (t (er soft ctx
                 "No event was found for the name, ~x0"
                 name)))))

(defun repkg-event-lst (names wit ctx state)
  (declare (xargs :guard (and (symbol-listp names)
                              (symbolp wit))
                  :mode :program
                  :stobjs state))
  (cond ((endp names) (value nil))
        (t (er-let* ((ev (repkg-event (car names) wit ctx state))
                     (evs (repkg-event-lst (cdr names) wit ctx state)))
             (value (cons ev evs))))))

(defmacro make-repkg-events (names pkg)
  (declare (xargs :guard (and (symbol-listp names)
                              (stringp pkg))))
  `(make-event
    (er-let* ((evs (repkg-event-lst ',names
                                    (pkg-witness ,pkg)
                                    'make-repkg-events
                                    state)))
      (value (cons 'progn evs)))))

