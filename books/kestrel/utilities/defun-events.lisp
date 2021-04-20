; Utilities for processing defun forms
;
; Copyright (C) 2015-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

(include-book "declares0")

;move
(defthm butlast-of-nil
  (equal (butlast nil n)
         nil)
  :hints (("Goal" :in-theory (enable butlast))))

;; (defthm symbol-listp-of-butlast
;;   (implies (and (SYMBOL-LISTP X)
;;                 (natp n)
;;                 (<= n (len x)))
;;            (SYMBOL-LISTP (BUTLAST X N)))
;;   :hints (("Goal" :in-theory (enable butlast SYMBOL-LISTP))))

(defconst *defun-types*
  '(defun defund defun-nx defund-nx))

;add more to this!
(defund defun-formp (defun)
  (declare (xargs :guard t))
  (and (true-listp defun)
       (>= (len defun) 4)
       (member-eq (first defun) *defun-types*) ;TODO: Handle defun-inline, etc.?  define (maybe not)  Handle anything we might call fixup-defun on...
       (symbolp (second defun))     ;the function name
       (symbol-listp (third defun)) ;the formals
       ;; what to say about the body?  may contain macros?
       (all-declarep (butlast (cdr (cdr (cdr defun))) 1)) ;skip the defun, name, formals, and body.
       ))

(defun get-declares-from-defun (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))
                  ))
  (butlast (cdr (cdr (cdr defun))) 1)) ; (defun <name> <formals> <declare> ... <declare> <body>)

;; DEFUN is of the form (defun <name> <formals> <declare> ... <declare> <body>)
(defun replace-declares-in-defun (defun declares)
  (declare (xargs :guard (and (defun-formp defun)
                              (true-listp declares)
                              (all-declarep declares))
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))
                  ))
  `(,(first defun) ;defun, defund, etc.
    ,(second defun) ;name
    ,(third defun) ;formals
    ,@declares ;the new declares
    ,(car (last defun)) ;body
    ))

(defun get-body-from-defun (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (car (last defun))) ; (defun <name> <formals> <declare> ... <declare> <body>)

;; ;Check whether a defun form is recursive (TOOD: what about mutual recursion?)
;; (defun defun-recursivep (defun)
;;   (declare (xargs :guard (defun-formp defun)
;;                   :guard-hints (("Goal" :in-theory (enable defun-formp)))))
;;   (let* ((fn (second defun))
;;          (body (get-body-from-defun defun))
;;          (called-fns (get-called-fns-in-untranslated-term body)))
;;     (if (member-eq fn called-fns) t nil)))


(defund get-xargs-from-defun (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))
                  ))
  (get-xargs-from-declares (get-declares-from-defun defun)))

;(defforall-simple defun-formp)
;(verify-guards all-defun-formp)
(defun all-defun-formp (forms)
  (declare (xargs :guard t))
  (if (atom forms)
      t
    (and (defun-formp (first forms))
         (all-defun-formp (rest forms)))))

;add more to this!
(defun mutual-recursion-formp (mut-rec)
  (declare (xargs :guard t))
  (and (consp mut-rec)
       (eq 'mutual-recursion (ffn-symb mut-rec))
       (true-listp mut-rec)
       (all-defun-formp (fargs mut-rec))))

(defun defun-or-mutual-recursion-formp (event)
  (declare (xargs :guard t))
  (or (defun-formp event)
      (mutual-recursion-formp event)))

(defun find-defun-in-mut-rec (fn defuns)
  (declare (xargs :guard (and (symbolp fn)
                              (true-listp defuns)
                              (all-defun-formp defuns))
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (if (endp defuns)
      nil
    (if (eq fn (second (first defuns)))
        (first defuns)
      (find-defun-in-mut-rec fn (rest defuns)))))

(defun get-declares-from-event (fn event)
  (declare (xargs :guard (and (symbolp fn)
                              (defun-or-mutual-recursion-formp event))
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (let ((event-type (ffn-symb event)))
    (if (member-eq event-type *defun-types*)
        (get-declares-from-defun event)
      (if (eq 'mutual-recursion event-type)
          (let ((defun (find-defun-in-mut-rec fn (fargs event))))
            (if (not (defun-formp defun))
                nil ;TODO error!
          (get-declares-from-event fn defun)))
        (hard-error 'get-declares-from-event "Unknown type of event for ~x0." (acons #\0 fn nil))))))

(defthm all-declarep-of-get-declares-from-event
  (implies (defun-or-mutual-recursion-formp fn-event)
           (all-declarep (get-declares-from-event fn fn-event)))
  :hints (("Goal" :in-theory (enable defun-formp))))

(defun get-xargs-from-event (fn event)
  (declare (xargs :guard (and (symbolp fn)
                              (defun-or-mutual-recursion-formp event))
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))
                  ))
  (let ((event-type (ffn-symb event)))
    (if (member-eq event-type *defun-types*)
        (get-xargs-from-defun event)
      (if (eq 'mutual-recursion event-type)
          (let ((defun (find-defun-in-mut-rec fn (fargs event))))
            (if (not (defun-formp defun))
                nil ;TODO error!
          (get-xargs-from-event fn defun)))
        (hard-error 'get-xargs-from-event "Unknown type of event for ~x0." (acons #\0 fn nil))))))

;; Returns the untranslated body provided for FN in EVENT, which should be a DEFUN or MUTUAL-RECURSION.
;; TODO: Perhaps add support for DEFUNS, which is like MUTUAL-RECURSION.
(defund get-body-from-event (fn event)
  (declare (xargs :guard (and (symbolp fn)
                              (defun-or-mutual-recursion-formp event))
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))
                  ))
  (let ((event-type (ffn-symb event)))
    (if (member-eq event-type *defun-types*)
        (get-body-from-defun event)
      (if (eq 'mutual-recursion event-type)
          (let ((defun (find-defun-in-mut-rec fn (fargs event))))
            (if (not (defun-formp defun))
                (er hard? 'get-body-from-event "Failed to find a body for ~x0 in the event ~x1." fn event)
              (get-body-from-event fn defun)))
        (er hard? 'get-body-from-event "Unknown type of event for ~x0." fn)))))

(defun defun-has-explicit-guardp (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (some-declare-has-a-guard-or-type (get-declares-from-defun defun)))

;TODO: Consider stobj declarations (these act like guards?)
(defun any-defun-has-explicit-guardp (defuns)
  (declare (xargs :guard (all-defun-formp defuns)))
  (if (atom defuns)
      nil
    (or (defun-has-explicit-guardp (first defuns))
        (any-defun-has-explicit-guardp (rest defuns)))))

(defthm keyword-value-listp-of-get-xargs-from-defun
 (implies (defun-formp defun)
          (keyword-value-listp (get-xargs-from-defun defun)))
 :hints (("Goal" :in-theory (enable defun-formp get-xargs-from-defun))))

(local (in-theory (disable len)))

(defun defun-has-verify-guards-nilp (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (let* ((xargs (get-xargs-from-defun defun))
         (verify-guards (assoc-keyword :verify-guards xargs)))
    (if (not verify-guards)
        nil
      (eq nil (cadr verify-guards)))))

(defun any-defun-has-verify-guards-nilp (defuns)
  (declare (xargs :guard (all-defun-formp defuns)))
  (if (atom defuns)
      nil
    (or (defun-has-verify-guards-nilp (first defuns))
        (any-defun-has-verify-guards-nilp (rest defuns)))))

(defun guards-were-verified-in-defunp (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (and (defun-has-explicit-guardp defun)
       (not (defun-has-verify-guards-nilp defun))))

(defun guards-were-verified-in-eventp (fn-event) ;;TODO This assumes the verify-guards-eagerness was 1 when FN-EVENT was submitted.
  (declare (xargs :guard (defun-or-mutual-recursion-formp fn-event)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (if (member-eq (ffn-symb fn-event) *defun-types*)
      (guards-were-verified-in-defunp fn-event)
    ;; it's a mutual-recursion
    (let ((defuns (rest fn-event)))
      (and (any-defun-has-explicit-guardp defuns)
           (not (any-defun-has-verify-guards-nilp defuns))))))

(defun add-verify-guards-nil-to-defun (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))
                  ))
  (let* ((declares (get-declares-from-defun defun))
         (declares (add-verify-guards-nil declares))
         (defun (replace-declares-in-defun defun declares)))
    defun))

(defun add-verify-guards-t-to-defun (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))
                  ))
  (let* ((declares (get-declares-from-defun defun))
         (declares (add-verify-guards-t declares))
         (defun (replace-declares-in-defun defun declares)))
    defun))
