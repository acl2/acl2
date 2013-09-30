; CUTIL - Centaur Basic Utilities
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "CUTIL")
(include-book "support")
(set-state-ok t)
(program)

(defxdoc defredundant
  :parents (cutil)
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
               landmark)))
    (cddr landmark)))

(defun runes-to-e/ds (runes enables disables state)
  (b* (((when (atom runes))
        (mv enables disables))
       (rune1     (car runes))
       (acl2::ens (acl2::ens state))
       (enabled1  (acl2::active-runep rune1))
       ((when enabled1)
        (runes-to-e/ds (cdr runes) (cons rune1 enables) disables state)))
    (runes-to-e/ds (cdr runes) enables (cons rune1 disables) state)))

(defun name-to-e/ds (name state)
  (b* ((runic-mapping-pairs
        (getprop name 'acl2::runic-mapping-pairs
                 nil 'acl2::current-acl2-world (acl2::w state)))
       (runes (strip-cdrs runic-mapping-pairs)))
    (runes-to-e/ds runes nil nil state)))

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
       ((when (member kwd '(:measure :mode :verify-guards
                                     :guard-debug :guard-hints 
                                     :hints :otf-flg)))
        (redundant-clean-up-xargs rest)))
    (list* kwd val
           (redundant-clean-up-xargs rest))))

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
        (cons arg1
              (redundant-clean-up-decl-args rest)))
       ((when (eq (car arg1) 'xargs))
        (cons (cons 'xargs
                    (redundant-clean-up-xargs (cdr arg1)))
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
        ;; Drop any documentation strings since they may refer to doc-sections
        ;; that aren't going to be present anymore.
        (redundant-clean-up-decls rest))
       ((unless (and (consp decl1)
                     (eq (car decl1) 'declare)))
        (raise "Bad declaration ~x0" x))
       (decl1-args (cdr decl1)))
    (cons (cons 'declare (redundant-clean-up-decl-args decl1-args))
          (redundant-clean-up-decls rest))))

(defun redundant-defun (event-tuple state)
  (b* ((?__function__ 'redundant-defun)
       (world (w state))
       (form  (acl2::access-event-tuple-form event-tuple))
       ((unless (and (consp form)
                     (eq (car form) 'defun)))
        (raise "Called redundant-defun on ~x0?" event-tuple))
       (fn      (second form))
       (formals (third form))
       (decls   (redundant-clean-up-decls (butlast (cdddr form) 1)))
       (body    (car (last form)))

       (world-formals (getprop fn 'acl2::formals :bad 'acl2::current-acl2-world world))
       ((unless (equal world-formals formals))
        (raise "Problem with formals for ~x0?" event-tuple))

       ;; elide measure in case it's not been redundantly introduced
       (just (getprop fn 'acl2::justification nil 'acl2::current-acl2-world world))
       (decls (if (not just)
                  decls
                (cons `(declare (xargs :measure (:? . ,(acl2::access acl2::justification just :subset))))
                      decls)))

       ;; figure out the correct :mode and :verify-guards, based on current state
       (symbol-class (getprop fn 'acl2::symbol-class nil 'acl2::current-acl2-world world))
       (decls (cond ((eq symbol-class :program)
                     (cons `(declare (xargs :mode :program))
                           decls))
                    ((eq symbol-class :ideal)
                     (cons `(declare (xargs :mode :logic :verify-guards nil))
                           decls))
                    ((eq symbol-class :common-lisp-compliant)
                     (cons `(declare (xargs :mode :logic :verify-guards t))
                           decls))
                    (t
                     (raise "Expected valid symbol-class for ~x0, found ~x1."
                            event-tuple symbol-class))))

       ;; figure out if the function and its executable-counterpart are
       ;; enabled.  we won't do anything with type-prescriptions since they're
       ;; completely broken anyway (e.g., the TP you get is based on your
       ;; current theory, not the theory at the DEFUN time anyway.)
       ((mv enables disables) (name-to-e/ds fn state)))
    `((defun ,fn ,formals ,@decls ,body)
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
    `((defthm ,name ,formula . ,kwdargs)
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
       (body    (car (last form)))
       ;; BOZO how about macro-aliases
       ;; BOZO how about binop-table
       ;; BOZO how about untranslate-patterns
       )
    `((defmacro  ,name ,formals ,@decls ,body))))

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
    `((defconst ,name ,value))))

(defun redundant-event (name state)
  (b* ((?__function__ 'redundant-event)
       (world       (w state))
       (event-tuple (get-event-tuple name world))
       (form        (acl2::access-event-tuple-form event-tuple))
       ((unless (consp form))
        (raise "For ~x0: expected a valid event form, but found ~x1." name form))
       (type (car form))
       ((when (eq type 'defun))    (redundant-defun event-tuple state))
       ((when (eq type 'defthm))   (redundant-defthm event-tuple state))
       ((when (eq type 'defmacro)) (redundant-defmacro event-tuple state))
       ((when (eq type 'defconst)) (redundant-defconst event-tuple state))
       )
    (raise "For ~x0: unsupported event type: ~x1" name type)))

(defun redundant-events (names state)
  (if (atom names)
      nil
    (append (redundant-event (car names) state)
            (redundant-events (cdr names) state))))

(defun defredundant-fn (names state)
  (let ((events (redundant-events names state)))
    `(encapsulate
      ()
      (set-enforce-redundancy t)
      (logic)
      . ,events)))

(defmacro defredundant (&rest names)
  `(make-event (defredundant-fn ',names state)))

