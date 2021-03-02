; Functions to define constants using make-event
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

;; TODO: Move to ../utilities

;; TODO: What are the best names for these things?

;; TODO: Can we combine these into a single utility which analyzes its FORM for
;; the stobjs-out and then does the right thing (maybe call check-user-term)?

;; See tests in defconst-computed-tests.lisp

;; See also books/std/util/defconsts.lisp.

;; Helper function.  Makes a defconst form with the indicated name and value.
;; NAME should be a legal constant name (a symbol that starts and ends with an
;; asterisk).  VALUE can be anything.
(defun make-defconst-form (name val)
  `(defconst ,name ',val))

;;;
;;; defconst-computed-simple
;;;

;; A variant of defconst that takes a FORM, to be evaluated, that can mention
;; (but not return) stobjs, including state.
(defmacro defconst-computed-simple (name form)
  `(make-event (make-defconst-form ',name ,form)))

;;;
;;; defconst-computed
;;;

;; A variant of defconst that takes a FORM that can mention stobjs and that
;; returns STATE.  FORM should return (mv value state).  FORM gets evaluated.
(defmacro defconst-computed (name form)
  `(make-event (mv-let (result state)
                 ,form
                 (mv nil ;no error
                     (make-defconst-form ',name result)
                     state))))

;;;
;;; defconst-computed3
;;;

;; A variant of defconst that takes a FORM that can mention stobjs and that
;; returns an error triple.  FORM should return (mv erp value state).  FORM
;; gets evaluated.
(defmacro defconst-computed3 (name form)
  `(make-event (mv-let (erp result state)
                 ,form
                 (mv erp
                     (make-defconst-form ',name result)
                     state))))

;;;
;;; defconst-computed-erp-and-val
;;;

;; A variant of defconst that takes a FORM that can mention stobjs and that
;; returns an error and a value.  FORM should return (mv erp value).  FORM gets
;; evaluated.
(defmacro defconst-computed-erp-and-val (name form)
  `(make-event (mv-let (erp val)
                 ,form
                 (mv erp
                     (make-defconst-form ',name val)
                     state))))
