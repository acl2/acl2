; Utilities about replaying books
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/file-io-light/read-objects-from-book" :dir :system)
(include-book "kestrel/utilities/file-existsp" :dir :system)

;; Returns state.
(defun load-port-file-if-exists (book-path ; no extension
                                 state)
  (declare (xargs :guard (stringp book-path)
                  :stobjs state
                  :mode :program))
  (let ((port-file-path (concatenate 'string book-path ".port")))
    (mv-let (existsp state)
      (file-existsp port-file-path state)
      (if (not existsp)
          (prog2$ (cw "NOTE: Not loading ~s0 (does not exist).~%" port-file-path)
                  state)
        (mv-let (erp val state)
          ;; TODO: Make this less noisy:
          (with-output! :off (acl2::event acl2::observation)
            (eval-port-file (concatenate 'string book-path ".lisp") 'load-port-file-if-exists state))
          (declare (ignore val))
          (if erp
              (prog2$ (er hard? 'load-port-file-if-exists "Error loading .port file for ~x0." book-path)
                      state)
            state))))))

;; Prints VAL, rounded to the hundredths place.
;; Returns nil
(defund print-rounded-val (val)
  (declare (xargs :guard (rationalp val)))
  (let* ((integer-part (floor val 1))
         (fraction-part (- val integer-part))
         (tenths (floor (* fraction-part 10) 1))
         (fraction-part-no-tenths (- fraction-part (/ tenths 10)))
         (hundredths (ceiling (* fraction-part-no-tenths 100) 1)) ; todo: do a proper rounding
         )
    (cw "~c0.~c1~c2" (cons integer-part 10) (cons tenths 1) (cons hundredths 1))))

;; Generate a short, printable thing that indicates an event (e.g., for a
;; defthm, this returns (defthm <name> :elided).
;; TODO: Handle more kinds of thing (see :doc events).
;; TODO: Maybe use ... instead of :elided.
(defun shorten-event (event)
  (if (not (consp event))
      event
    (case (car event)
      (local `(local ,(shorten-event (cadr event))))
      (in-package event)   ; no need to shorten
      (include-book event) ; no need to shorten
      ;; These have names, so we print the name:
      ((defun defund defun-nx defund-nx define defun-sk defund-sk define-sk defun-inline defun-notinline defund-inline defund-notinline defun$ defn

              defthm defthmd defthmg defthmr defrule defruled defrulel defruledl
              defaxiom
              defabbrev
              defmacro
              defstobj
              defcong
              defconst
              defret
              defchoose
              defequiv
              defxdoc
              ;; soft things like defun2?
              defexec
              defpun
              deflabel
              ;; defpkg ; no
              )
       `(,(car event) ,(cadr event) :elided))
      ;; defevaluator?
      ;; mutual-recursion?
      ;; skip-proofs?
      ((thm rule) `(,(car event) :elided))
      (theory-invariant '(theory-invariant :elided))
      (in-theory '(in-theory :elided))
      (deftheory `(deftheory ,(cadr event) :elided))
      (defsection `(defsection ,(cadr event) :elided))
      (encapsulate '(encapsulate :elided :elided)) ; todo: recur inside encapsulate?
      (progn '(progn :elided)) ; todo: recur inside progn?
      (t `(,(car event) :elided)))))
