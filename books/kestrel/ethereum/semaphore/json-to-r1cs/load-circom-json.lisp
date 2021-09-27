; Semaphore Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributing Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Analogously to kestrel-acl2/jvm/load-class.lisp ,
;; this file defines
;;   (load-circom-json <json-file> <prime-field-form>)
;; which makes an event containing a defconstant with the R1CS constraints
;; and an R1CS object maker function.

;; Note: this code is elliptic-curve-independent.

;; For example usage see
;;   ../r1cs/README.md

(include-book "kestrel/utilities/erp" :dir :system) ; for erp-nil

(include-book "kestrel/event-macros/cw-event" :dir :system)

(include-book "kestrel/utilities/pack" :dir :system)

(include-book "kestrel/utilities/make-event-quiet" :dir :system)

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system) ; for r1cs::r1cs

(include-book "misc/file-io" :dir :system)
(include-book "std/strings/strtok" :dir :system) ;for str::strtok

(include-book "kestrel/json-parser/parse-json-file" :dir :system)

(include-book "cj-to-acl2")

;; Since we are not currently proving anything about this conversion code,
;; speed it up by putting it in program mode.
(program)

; If we switch to logic mode, we may need this or something like it.
;(local
; (defthm stringp-of-car-of-last
;   (implies (and (string-listp x)
;                 (consp x))
;            (stringp (car (last x))))))

;; ".../multimux1-2.json" --> MULTIMUX-1-2-CONSTRAINTS
(defun file-name-to-defun-constraints-name (filename)
  ;; (declare (xargs :guard (stringp filename)))
  (let* ((wo-dir (car (last (str::strtok filename (list #\/)))))
         (wo-extension (first (str::strtok wo-dir (list #\.)))))
    (intern (string-append (string-upcase wo-extension)
                           "-CONSTRAINTS") "ACL2")))

;; ".../multimux1-2.json" --> MULTIMUX-1-2-VARS
(defun file-name-to-defun-vars-name (filename)
  ;; (declare (xargs :guard (stringp filename)))
  (let* ((wo-dir (car (last (str::strtok filename (list #\/)))))
         (wo-extension (first (str::strtok wo-dir (list #\.)))))
    (intern (string-append (string-upcase wo-extension)
                           "-VARS") "ACL2")))

;; ".../multimux1-2.json" --> MULTIMUX-1-2-MAKE-R1CS
(defun file-name-to-r1cs-maker-fn-name (filename)
  (let* ((wo-dir (car (last (str::strtok filename (list #\/)))))
         (wo-extension (first (str::strtok wo-dir (list #\.)))))
    (intern (string-append (string-upcase wo-extension) "-MAKE-R1CS") "ACL2")))

;; Replaces write-r1cs-file.  Instead of writing a file, just returns
;; the event that we want.
(defun make-r1cs-event (constraints vars prime-form defun-constraints-name defun-vars-name defun-nx-name)
  (declare (xargs :guard (and (symbolp defun-vars-name)
                              (symbolp defun-constraints-name)
                              (symbolp defun-nx-name))))
  (let ((primality-theorem 'primality-theorem-for-make-r1cs-event)
        (vars-theorem-name (pack$ 'var-listp-of- defun-vars-name))
        (constraints-theorem-1-name (pack$ 'r1cs-constraint-listp-of- defun-constraints-name))
        (constraints-theorem-2-name (pack$ 'good-r1cs-constraint-listp-of- defun-constraints-name)))
    `(encapsulate ()
       ;; Currently required for the guard proof, and having this separate makes failure more clear:
       (local (defthm ,primality-theorem
                (rtl::primep ,prime-form)))
       (cw-event "Created local primality theorem, ~x0.~%" ',primality-theorem)
       (defund ,defun-vars-name () (declare (xargs :guard t)) ',vars)
       (cw-event "Created vars defun, ~x0.~%" ',defun-vars-name)
       (defthm ,vars-theorem-name
         (r1cs::var-listp (,defun-vars-name)))
       (cw-event "Created vars theorem, ~x0.~%" ',vars-theorem-name)
       (defund ,defun-constraints-name () (declare (xargs :guard t)) ',constraints)
       (cw-event "Created constraints defun, ~x0.~%" ',defun-constraints-name)
       (defthm ,constraints-theorem-1-name
         (r1cs::r1cs-constraint-listp (,defun-constraints-name)))
       (cw-event "Created constraints theorem 1, ~x0.~%" ',constraints-theorem-1-name)
       ;; This can be a bit slow:
       (defthm ,constraints-theorem-2-name
         (r1cs::good-r1cs-constraint-listp (,defun-constraints-name) (,defun-vars-name)))
       (cw-event "Created constraints theorem 2, ~x0.~%" ',constraints-theorem-2-name)
       (local (in-theory (disable (:e ,defun-vars-name))))
       (local (in-theory (disable (:e ,defun-constraints-name))))
       (defun-nx ,defun-nx-name ()
         (declare (xargs :guard t))
         (r1cs::r1cs ,prime-form (,defun-vars-name) (,defun-constraints-name)))
       (cw-event "Created R1CS defun, ~x0.~%" ',defun-nx-name))))

; Returns (mv erp event defun-nx-name state)
(defun circom-json-event (cj-filename prime-form state)
  (declare (xargs :stobjs state
                  :guard (stringp cj-filename)
                  :verify-guards nil))
  (b* (((mv erp cj state) (parse-file-as-json cj-filename state))
       ((when erp) (mv erp nil nil state))
       (- (cw "Parsed JSON from ~x0.~%" cj-filename))
       ;; ((when erp) (mv erp nil nil state)) ;EM maybe do later
       ((mv constraints vars) (cj-to-r1cs cj))
       (defun-constraints-name (file-name-to-defun-constraints-name cj-filename))
       (defun-vars-name (file-name-to-defun-vars-name cj-filename))
       (defun-nx-name (file-name-to-r1cs-maker-fn-name cj-filename))
       (event (make-r1cs-event constraints vars prime-form
                               defun-constraints-name defun-vars-name defun-nx-name))
       (- (cw "Created R1CS event.~%")))
    (mv (erp-nil) event defun-nx-name state)))

;Returns (mv erp event state).
(defun load-circom-json-fn (cj-filename prime-form state)
  (declare (xargs :stobjs state
                  :guard (stringp cj-filename)
                  :verify-guards nil))
  (b* (((mv erp event defun-nx-name state)
        (circom-json-event cj-filename prime-form state))
       ((when erp) (mv erp nil state)))
    (mv (erp-nil)
        `(progn ,event
                (table acl2::depends-on-table ,cj-filename t)
                (value-triple ',defun-nx-name))
        state)))

;; PRIME-FORM should be something like (primes::bn-254-group-prime)
(defmacro load-circom-json (json-file prime-form)
  `(make-event-quiet (load-circom-json-fn ,json-file ,prime-form state)))

(defun show-circom-json-fn (cj-filename prime-form state)
  (declare (xargs :stobjs state
                  :guard (stringp cj-filename)
                  :verify-guards nil))
  (b* (((mv erp event & state)
        (circom-json-event cj-filename prime-form state))
       ((when erp) (mv erp nil state)))
    (progn$ (cw "Showing ACL2 event for ~s0:~%~X12" cj-filename event nil)
            (mv (erp-nil) '(value-triple :invisible) state))))

(defmacro show-circom-json (json-file prime-form)
  `(make-event-quiet (show-circom-json-fn ,json-file ,prime-form state)))
