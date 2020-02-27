; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "STD")
(include-book "support")
(set-state-ok t)
(program)

(defxdoc defredundant
  :parents (std/util)
  :short "A macro for automatically introducing @(see acl2::redundant-events),
which is useful for developing \"interface\" books and otherwise avoiding
copying and pasting code.")

(defun get-event-tuple (name world)
  (b* ((?__function__ 'get-event-tuple)
       (ev-world (acl2::decode-logical-name name world))
       ((unless (consp ev-world))
        (raise "Not a logical name: ~x0." name))
       (landmark (car ev-world))
       ((unless (and (consp landmark)
                     (eq (first landmark) 'acl2::event-landmark)
                     (eq (second landmark) 'acl2::global-value)))
        (raise "Expected (EVENT-LANDMARK GLOBAL-VALUE . <event-tuple>) but found ~x0."
               landmark))
       (tuple (cddr landmark))
       (form (acl2::access-event-tuple-form tuple)))
      (cond ((and (consp form)
                  (eq (car form) 'acl2::verify-termination-boot-strap))
; Check added by Matt K.  (Without it, the check below involving
;   (get-event-tuple 'binary-append world)
; was failing after a 3/20/2015 modification to ACL2 source file axioms.lisp.
             (get-event-tuple name (acl2::scan-to-event (cdr ev-world))))
            (t tuple))))

(defun runes-to-e/ds (runes enables disables state)
  ;; Returns (mv enables disables)
  (b* (((when (atom runes))
        (mv enables disables))
       (rune1     (car runes))
       (acl2::ens (acl2::ens state))
       (enabled1  (acl2::active-runep rune1))
       ((when enabled1)
        (runes-to-e/ds (cdr runes) (cons rune1 enables) disables state)))
    (runes-to-e/ds (cdr runes) enables (cons rune1 disables) state)))

(defun name-to-e/ds (name state)
  ;; Returns (mv enables disables)
  (b* ((runic-mapping-pairs
        (getprop name 'acl2::runic-mapping-pairs
                 nil 'acl2::current-acl2-world (acl2::w state)))
       (runes (strip-cdrs runic-mapping-pairs)))
    (runes-to-e/ds runes nil nil state)))

(defun names-to-e/ds (names state)
  ;; Returns (mv enables disables)
  (b* (((when (atom names))
        (mv nil nil))
       ((mv es1 ds1) (name-to-e/ds (car names) state))
       ((mv es2 ds2) (names-to-e/ds (cdr names) state)))
    (mv (append es1 es2)
        (append ds1 ds2))))



(defun redundant-clean-up-xargs
  (x ;; e.g., (:guard (natp x) :measure (acl2-count x) ...)
   )
  ;; strip out various mode/guard/measure/hint related stuff
  (b* ((?__function__ 'redundant-clean-up-xargs)
       ((when (atom x))
        nil)
       ((when (atom (cdr x)))
        (raise "Invalid xargs... ~x0" x))
       ((list* kwd val rest) x)
       ((when (member kwd '(:measure :mode :verify-guards :guard-debug
                            :guard-hints :hints :otf-flg)))
        (redundant-clean-up-xargs rest)))
    (list* kwd val (redundant-clean-up-xargs rest))))

(defun redundant-clean-up-decl-args
  (x ;; the "..." part of a (declare . ...); i.e., ((type ...) (xargs ...) (ignore ...))
   )
  ;; strip out any measure/mode declarations
  (b* ((?__function__ 'redundant-clean-up-decl-args)
       ((when (atom x))
        nil)
       ((cons arg1 rest) x)
       ((unless (consp arg1))
        (raise "Bad form in declare: ~x0" x))
       ((when (or (eq (car arg1) 'type)
                  (eq (car arg1) 'ignore)
                  (eq (car arg1) 'ignorable)))
        (cons arg1 (redundant-clean-up-decl-args rest)))
       ((when (eq (car arg1) 'xargs))
        (cons (cons 'xargs (redundant-clean-up-xargs (cdr arg1)))
              (redundant-clean-up-decl-args rest))))
    (raise "Bad form in declare: ~x0" x)))

(defun redundant-clean-up-decls
  (x ;; list of traditional doc strings and (declare ...) forms
   )
  ;; strip out all measure/mode decls and doc strings
  (b* ((?__function__ 'redundant-clean-up-decls)
       ((when (atom x))
        nil)
       ((cons decl1 rest) x)
       ((when (stringp decl1))
        ;; Drop any documentation strings since they may refer to doc sections
        ;; that aren't going to be present anymore.
        (redundant-clean-up-decls rest))
       ((unless (and (consp decl1)
                     (eq (car decl1) 'declare)))
        (raise "Bad declaration ~x0" x))
       (decl1-args (cdr decl1)))
    (cons (cons 'declare (redundant-clean-up-decl-args decl1-args))
          (redundant-clean-up-decls rest))))

(defun redundant-clean-up-defun (form force-programp state)
  ;; Returns a cleaned up (defun ...) form.
  (b* ((__function__ 'redundant-rewrite-defun)
       (world (w state))
       ((unless (and (consp form)
                     (or (eq (car form) 'defun)
                         ;; we might see defund's within mutual recursions.
                         (eq (car form) 'defund))))
        (raise "Called redundant-rewrite-defun on ~x0?" form))
       (fn      (second form))
       (formals (third form))
       (decls   (redundant-clean-up-decls (butlast (cdddr form) 1)))
       (body    (car (last form)))
       (world-formals (getprop fn 'acl2::formals :bad 'acl2::current-acl2-world world))
       ((unless (equal world-formals formals))
        (raise "Problem with formals for ~x0: ~x1 vs ~x2?" fn formals world-formals))
       ;; elide measure in case it's not been redundantly introduced
       (just (getprop fn 'acl2::justification nil 'acl2::current-acl2-world world))
       (decls (if (not just)
                  decls
                (cons `(declare (xargs :measure (:? . ,(acl2::access acl2::justification just :subset))))
                      decls)))
       ;; figure out the correct :mode and :verify-guards, based on current state
       (symbol-class (getprop fn 'acl2::symbol-class nil 'acl2::current-acl2-world world))
       (decls (cond ((or force-programp
                         (eq symbol-class :program))
                     (cons `(declare (xargs :mode :program))
                           decls))
                    ((eq symbol-class :ideal)
                     (cons `(declare (xargs :mode :logic :verify-guards nil))
                           decls))
                    ((eq symbol-class :common-lisp-compliant)
                     (cons `(declare (xargs :mode :logic :verify-guards t))
                           decls))
                    (t
                     (raise "Expected valid symbol-class for ~x0, found ~x1." fn symbol-class)))))
    ;; Note: we use DEFUN even if it was a DEFUND; any enabling/disabling will
    ;; happen separately.
    `(defun ,fn ,formals ,@decls ,body)))

(defun redundant-clean-up-defuns (forms force-programp state)
  ;; Returns a list of cleaned up (defun ...) forms.
  (if (atom forms)
      nil
    (cons (redundant-clean-up-defun (car forms) force-programp state)
          (redundant-clean-up-defuns (cdr forms) force-programp state))))

(defun redundant-defun (event-tuple force-programp state)
  (b* ((?__function__ 'redundant-defun)
       (form            (acl2::access-event-tuple-form event-tuple))
       (cleaned-up-form (redundant-clean-up-defun form force-programp state))
       (fn              (second form))
       ;; figure out if the function and its executable-counterpart are
       ;; enabled.  we won't do anything with type-prescriptions since they're
       ;; completely broken anyway (e.g., the TP you get is based on your
       ;; current theory, not the theory at the DEFUN time anyway.)
       ((mv enables disables) (if force-programp
                                  (mv nil nil)
                                (name-to-e/ds fn state))))
    `((value-triple (cw "Defun: ~x0.~%" ',fn))
      ,cleaned-up-form
      (in-theory (e/d ,enables ,disables)))))

(defun redundant-mutrec (event-tuple force-programp state)
  (b* ((?__function__ 'redundant-mutual-recursion)
       (form  (acl2::access-event-tuple-form event-tuple))
       ((unless (and (consp form)
                     (eq (car form) 'mutual-recursion)))
        (raise "Called redundant-mutual-recursion on ~x0?" event-tuple))
       (defuns (cdr form))
       (cleaned-up-defuns (redundant-clean-up-defuns defuns force-programp state))
       ((mv enables disables) (if force-programp
                                  (mv nil nil)
                                (names-to-e/ds (strip-cadrs defuns) state)))
       (cleaned-up-form `(mutual-recursion . ,cleaned-up-defuns)))
    `((value-triple (cw "Mutual: ~x0.~%" ',(strip-cadrs (cdr form))))
      ,cleaned-up-form
      (in-theory (e/d ,enables ,disables)))))

(defun redundant-clean-defthm-kwdargs (kwdargs)
  (b* ((?__function__ 'redundant-clean-defthm-kwdargs)
       ((when (atom kwdargs))
        nil)
       ((when (atom (cdr kwdargs)))
        (raise "odd number of elements in (:kwd val) list?"))
       ((list* kwd val rest) kwdargs)
       ((when (or (eq kwd :otf-flg)
                  (eq kwd :doc)
                  (eq kwd :hints)
                  (eq kwd :instructions)))
        (redundant-clean-defthm-kwdargs rest)))
    (list* kwd val (redundant-clean-defthm-kwdargs rest))))

(defun redundant-defthm (event-tuple state)
  (declare (ignorable state))
  (b* ((?__function__ 'redundant-defthm)
       (form  (acl2::access-event-tuple-form event-tuple))
       ((unless (and (consp form)
                     (eq (car form) 'defthm)))
        (raise "Called redundant-defthm on ~x0?" event-tuple))
       (name    (second form))
       (formula (third form))
       (kwdargs (redundant-clean-defthm-kwdargs (nthcdr 3 form)))
       ((mv enables disables) (name-to-e/ds name state)))
    `((value-triple (cw "Defthm: ~x0.~%" ',name))
      (defthm ,name ,formula . ,kwdargs)
      (in-theory (e/d ,enables ,disables)))))

(defun redundant-defmacro (event-tuple state)
  (declare (ignorable state))
  (b* ((?__function__ 'redundant-defmacro)
       (form  (acl2::access-event-tuple-form event-tuple))
       ((unless (and (consp form)
                     (eq (car form) 'defmacro)))
        (raise "Called redundant-defmacro on ~x0?" event-tuple))
       (name    (second form))
       (formals (third form))
       (decls   (redundant-clean-up-decls (butlast (nthcdr 3 form) 1)))
       (body    (car (last form))))
    `((value-triple (cw "Macro: ~x0.~%" ',name))
      (defmacro  ,name ,formals ,@decls ,body))))

(defun redundant-defconst (event-tuple state)
  (declare (ignorable state))
  (b* ((?__function__ 'redundant-defmacro)
       (form  (acl2::access-event-tuple-form event-tuple))
       ((unless (and (consp form)
                     (eq (car form) 'defconst)))
        (raise "Called redundant-defconst on ~x0?" event-tuple))
       (name    (second form))
       (value   (third form))
       (?doc    (fourth form)))
    `((value-triple (cw "Const: ~x0.~%" ',name))
      (defconst ,name ,value))))


(defun redundant-defstobj (event-tuple state)
  (declare (ignorable state))
  (b* ((?__function__ 'redundant-defmacro)
       (form  (acl2::access-event-tuple-form event-tuple))
       ((unless (and (consp form)
                     (eq (car form) 'defstobj)))
        (raise "Called redundant-defstobj on ~x0?" event-tuple))
       (name    (second form))
       (rest (cddr form)))
    `((value-triple (cw "Stobj: ~x0.~%" ',name))
      (defstobj ,name . ,rest))))

(defun redundant-encapsulate (event-tuple state)
  (declare (ignorable state))
  (b* ((?__function__ 'redundant-encapsulate)
       (form  (acl2::access-event-tuple-form event-tuple))
       ((unless (and (consp form)
                     (eq (car form) 'encapsulate)))
        (raise "Called redundant-encapsulate on ~x0?" event-tuple))
       (bound-fns    (second form))
       (rest (cddr form)))
    `((value-triple (cw "Encapsulate: ~x0.~%" ',(strip-cars bound-fns)))
      (encapsulate ,bound-fns . ,rest))))

(defun redundant-event1 (name force-programp state)
  (b* ((?__function__ 'redundant-event1)
       (world       (w state))
       (event-tuple (get-event-tuple name world))
       (form        (acl2::access-event-tuple-form event-tuple))
       ((unless (consp form))
        (raise "For ~x0: expected a valid event form, but found ~x1." name form))
       (type (car form))
       ((when (eq type 'defthm))
        (redundant-defthm event-tuple state))
       ((when (eq type 'defconst))
        (redundant-defconst event-tuple state))
       ((when (eq type 'defun))
        (redundant-defun event-tuple force-programp state))
       ((when (eq type 'defmacro))
        (redundant-defmacro event-tuple state))
       ((when (eq type 'mutual-recursion))
        (redundant-mutrec event-tuple force-programp state))
       ((when (eq type 'defstobj))
        (redundant-defstobj event-tuple state))
       ((when (eq type 'encapsulate))
        (redundant-encapsulate event-tuple state)))
     (raise "For ~x0: unsupported event type: ~x1" name type)))

(defun redundant-events1 (names force-programp state)
  (if (atom names)
      nil
    (append (redundant-event1 (car names) force-programp state)
            (redundant-events1 (cdr names) force-programp state))))



; Extension to handle macro aliases -------------------------------------------
;
; This is really subtle.  We generally want to introduce macro aliases first,
; before their associated functions, under the theory that folks will do things
; like:
;
;    (defmacro nice (foo bar &key baz boop)
;      `(nice-fn ,foo ,bar ,baz ,boop))
;    (defun nice-fn (foo bar baz boop)
;       (if ...
;          (nice (cdr foo) bar ...)        ;; i.e., using the macro in the def.
;         ...))
;
; This is straightforward enough for singly recursive functions, but for mutual
; recursions we need to possibly introduce all the macros first.

(defun find-macro-aliases-for-defun (form world)
  ;; Returns a list of macro-alias names (NIL if there are no aliases)
  (b* ((__function__ 'find-macro-aliases-for-defun)
       ((unless (and (consp form)
                     (or (eq (car form) 'defun)
                         (eq (car form) 'defund))))
        (raise "Expected a defun form, not ~x0." form))
       (name  (second form))
       (alias (car (rassoc name (table-alist 'acl2::macro-aliases-table world))))
       ((when alias)
        (list alias)))
    nil))

(defun find-macro-aliases-for-defuns (forms world)
  ;; Returns a list of macro-alias names (NIL if there are no aliases)
  (if (atom forms)
      nil
    (append (find-macro-aliases-for-defun (car forms) world)
            (find-macro-aliases-for-defuns (cdr forms) world))))

(defun find-defun-aliases-for-macro (form world) ;; form is a (defmacro foo ...)
  ;; Returns (mv macros fns)
  ;;   - macros is a list of macro names (including at least foo)
  ;;   - fns is a list of function names
  (b* ((__function__ 'find-defun-alias-for-macro)
       ((unless (and (consp form)
                     (eq (car form) 'defmacro)))
        (raise "Expected a defmacro form, not ~x0." form)
        (mv nil nil))
       (name  (second form))
       (fn    (cdr (assoc name (table-alist 'acl2::macro-aliases-table world))))
       ((unless fn)
        (mv (list name) nil))
       (defun-form (acl2::access-event-tuple-form (get-event-tuple fn world)))
       (type       (car defun-form))
       ((when (eq type 'mutual-recursion))
        (b* ((fns    (strip-cadrs (cdr defun-form)))
             (macros (find-macro-aliases-for-defuns (cdr defun-form) world)))
          (or (and (member name macros)
                   (member fn fns))
              (raise "Macro alias problem."))
          (mv macros fns)))
       ((when (eq type 'defun))
        (mv (list name) (list fn))))
    (raise "Expected macro alias for ~x0 to be a mutual-recursion or defun, ~
            but found ~x1." name defun-form)
    (mv nil nil)))


(defun redundant-event (name force-programp state)
  (b* ((?__function__ 'redundant-event)
       (world       (w state))
       (event-tuple (get-event-tuple name world))
       (form        (acl2::access-event-tuple-form event-tuple))
       ((unless (consp form))
        (raise "For ~x0: expected a valid event form, but found ~x1." name form))
       (type (car form))

       ((when (or (eq type 'defthm)
                  (eq type 'defconst)
                  (eq type 'defstobj)
                  (eq type 'encapsulate)))
        (redundant-event1 name force-programp state))

       ((when (eq type 'defun))
        (b* ((fn-events    (redundant-event1 name force-programp state))
             (defun        (acl2::access-event-tuple-form event-tuple))
             (macro-names  (find-macro-aliases-for-defun defun world))
             (macro-events (redundant-events1 macro-names force-programp state)))
          (append macro-events fn-events)))

       ((when (eq type 'mutual-recursion))
        (b* ((fn-events    (redundant-event1 name force-programp state))
             (defuns       (cdr (acl2::access-event-tuple-form event-tuple)))
             (macro-names  (find-macro-aliases-for-defuns defuns world))
             (- (cw "Macro names for mutual recursion ~x0: ~x1.~%" name macro-names))
             (macro-events (redundant-events1 macro-names force-programp state)))
          (append macro-events fn-events)))

       ((when (eq type 'defmacro))
        (b* ((defmacro        (acl2::access-event-tuple-form event-tuple))
             ((mv macros fns) (find-defun-aliases-for-macro defmacro world))
             (macro-events    (redundant-events1 macros force-programp state))
             (fn-events       (redundant-events1 fns force-programp state)))
          (append macro-events fn-events))))

    (raise "For ~x0: unsupported event type: ~x1 form: ~x2~%" name type
           (acl2::access-event-tuple-form event-tuple))))

(defun redundant-events (names force-programp state)
  (if (atom names)
      nil
    (append (redundant-event (car names) force-programp state)
            (redundant-events (cdr names) force-programp state))))





(defun defredundant-fn (names force-programp state)
  (let ((events (redundant-events names force-programp state)))
    `(encapsulate
      ()
      ;; This doesn't work with program mode, apparently
      ;; (set-enforce-redundancy t)
      ,(if force-programp
           '(program)
         '(logic))
      . ,events)))

(defmacro defredundant (&key force-programp
                             names)
  `(make-event
    (defredundant-fn ',names ',force-programp state)))
