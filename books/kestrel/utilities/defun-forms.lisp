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
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/butlast" :dir :system))

;; (defthm symbol-listp-of-butlast
;;   (implies (and (SYMBOL-LISTP X)
;;                 (natp n)
;;                 (<= n (len x)))
;;            (SYMBOL-LISTP (BUTLAST X N)))
;;   :hints (("Goal" :in-theory (enable butlast SYMBOL-LISTP))))

(defconst *defun-types*
  '(defun defund defun-nx defund-nx))

;add more to this!
;; (<defun-type> <name> <formals> <declare> ... <declare> <body>)
(defund defun-formp (defun)
  (declare (xargs :guard t))
  (and (true-listp defun)
       (>= (len defun) 4)
       (member-eq (first defun) *defun-types*) ;TODO: Handle defun-inline, etc.?  define (maybe not)  Handle anything we might call fixup-defun on...
       (symbolp (second defun))     ;the function name
       (symbol-listp (third defun)) ;the formals
       ;; not much to say about the body, since it is an untranslated term
       ;; todo: should we allow a doc-string before the declares?
       (all-declarep (butlast (cdr (cdr (cdr defun))) 1)) ;skip the defun-type, name, formals, and body.
       ))

(defund get-declares-from-defun (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (butlast (cdr (cdr (cdr defun))) 1)) ; (defun <name> <formals> <declare> ... <declare> <body>)

(defthm all-declarep-of-get-declares-from-defun
  (implies (defun-formp defun)
           (all-declarep (get-declares-from-defun defun)))
  :hints (("Goal" :in-theory (enable get-declares-from-defun
                                     defun-formp))))

(defund get-xargs-from-defun (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))
                  ))
  (get-xargs-from-declares (get-declares-from-defun defun)))

(defthm keyword-value-listp-of-get-xargs-from-defun
  (implies (defun-formp defun)
           (keyword-value-listp (get-xargs-from-defun defun)))
  :hints (("Goal" :in-theory (enable defun-formp get-xargs-from-defun))))

(defund get-body-from-defun (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (car (last defun)))


;; DEFUN is of the form (defun <name> <formals> <declare> ... <declare> <body>)
(defund replace-declares-in-defun (defun declares)
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

(local (in-theory (disable all-declarep)))

(defthm defun-formp-of-replace-declares-in-defun
  (implies (and (defun-formp defun)
                (true-listp declares)
                (all-declarep declares))
           (defun-formp (replace-declares-in-defun defun declares)))
  :hints (("Goal" :in-theory (enable replace-declares-in-defun defun-formp))))
 ; (defun <name> <formals> <declare> ... <declare> <body>)

;; ;Check whether a defun form is recursive (TOOD: what about mutual recursion?)
;; (defun defun-recursivep (defun)
;;   (declare (xargs :guard (defun-formp defun)
;;                   :guard-hints (("Goal" :in-theory (enable defun-formp)))))
;;   (let* ((fn (second defun))
;;          (body (get-body-from-defun defun))
;;          (called-fns (get-called-fns-in-untranslated-term body)))
;;     (if (member-eq fn called-fns) t nil)))


;(defforall-simple defun-formp)
;(verify-guards all-defun-formp)
(defund all-defun-formp (forms)
  (declare (xargs :guard t))
  (if (atom forms)
      t
    (and (defun-formp (first forms))
         (all-defun-formp (rest forms)))))

(defthm defun-formp-of-car
  (implies (all-defun-formp forms)
           (equal (defun-formp (car forms))
                  (consp forms)))
  :hints (("Goal" :in-theory (enable all-defun-formp))))

(defthm all-defun-formp-of-cdr
  (implies (all-defun-formp forms)
           (all-defun-formp (cdr forms)))
  :hints (("Goal" :in-theory (enable all-defun-formp))))

;add more to this!
(defund mutual-recursion-formp (mut-rec)
  (declare (xargs :guard t))
  (and (consp mut-rec)
       (eq 'mutual-recursion (car mut-rec))
       (true-listp mut-rec)
       (all-defun-formp (fargs mut-rec))))

(defthm mutual-recursion-formp-forward-to-equal-of-car
  (implies (mutual-recursion-formp mut-rec)
           (equal (car mut-rec)
                  'mutual-recursion))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable mutual-recursion-formp))))

(defun defun-or-mutual-recursion-formp (event)
  (declare (xargs :guard t))
  (or (defun-formp event)
      (mutual-recursion-formp event)))

;todo: rename find-defun-in-list?
(defun find-defun-in-mut-rec (fn defuns)
  (declare (xargs :guard (and (symbolp fn)
                              (true-listp defuns)
                              (all-defun-formp defuns))
                  :guard-hints (("Goal" :in-theory (enable all-defun-formp
                                                           defun-formp)))))
  (if (endp defuns)
      nil
    (if (eq fn (second (first defuns)))
        (first defuns)
      (find-defun-in-mut-rec fn (rest defuns)))))

(defthm defun-formp-of-find-defun-in-mut-rec
  (implies (all-defun-formp defuns)
           (iff (defun-formp (find-defun-in-mut-rec fn defuns))
                (find-defun-in-mut-rec fn defuns)))
  :hints (("Goal" :in-theory (enable find-defun-in-mut-rec))))

(defun get-declares-from-event (fn event)
  (declare (xargs :guard (and (symbolp fn)
                              (defun-or-mutual-recursion-formp event))
                  :guard-hints (("Goal" :in-theory (enable defun-formp
                                                           mutual-recursion-formp)))))
  (let ((event-type (car event)))
    (if (member-eq event-type *defun-types*)
        (get-declares-from-defun event)
      (if (mbt (eq 'mutual-recursion event-type))
          (let ((defun (find-defun-in-mut-rec fn (fargs event))))
            (if (not (defun-formp defun))
                (er hard? 'get-declares-from-event "Failed to find a defun for ~x0 in ~x1." fn event)
              (get-declares-from-event fn defun)))
        (hard-error 'get-declares-from-event "Unknown type of event for ~x0." (acons #\0 fn nil))))))

(defthm all-declarep-of-get-declares-from-event
  (implies (defun-or-mutual-recursion-formp fn-event)
           (all-declarep (get-declares-from-event fn fn-event)))
  :hints (("Goal" :in-theory (enable defun-formp))))

(defun get-xargs-from-event (fn event)
  (declare (xargs :guard (and (symbolp fn)
                              (defun-or-mutual-recursion-formp event))
                  :guard-hints (("Goal" :in-theory (enable defun-formp
                                                           mutual-recursion-formp)))))
  (get-xargs-from-declares (get-declares-from-event fn event)))

;; Returns the *untranslated* body provided for FN in EVENT, which should be a DEFUN or MUTUAL-RECURSION.
;; TODO: Perhaps add support for DEFUNS, which is like MUTUAL-RECURSION.
(defund get-body-from-event (fn event)
  (declare (xargs :guard (and (symbolp fn)
                              (defun-or-mutual-recursion-formp event))
                  :guard-hints (("Goal" :in-theory (enable defun-formp
                                                           mutual-recursion-formp)))))
  (let ((event-type (ffn-symb event)))
    (if (member-eq event-type *defun-types*)
        (get-body-from-defun event)
      (if (eq 'mutual-recursion event-type)
          (let ((defun (find-defun-in-mut-rec fn (fargs event))))
            (if (not (defun-formp defun))
                (er hard? 'get-body-from-event "Failed to find a body for ~x0 in the event ~x1." fn event)
              (get-body-from-event fn defun)))
        (er hard? 'get-body-from-event "Unknown type of event for ~x0." fn)))))

;; todo: is a type declare really an explicit guard?  what about a :stobjs xarg?
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
                  :guard-hints (("Goal" :in-theory (enable defun-formp
                                                           mutual-recursion-formp)))))
  (if (member-eq (ffn-symb fn-event) *defun-types*)
      (guards-were-verified-in-defunp fn-event)
    ;; it's a mutual-recursion
    (let ((defuns (rest fn-event)))
      (and (any-defun-has-explicit-guardp defuns)
           (not (any-defun-has-verify-guards-nilp defuns))))))

(defund add-verify-guards-nil-to-defun (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))
                  ))
  (let* ((declares (get-declares-from-defun defun))
         (declares (add-verify-guards-nil declares))
         (defun (replace-declares-in-defun defun declares)))
    defun))

(defund add-verify-guards-t-to-defun (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))
                  ))
  (let* ((declares (get-declares-from-defun defun))
         (declares (add-verify-guards-t declares))
         (defun (replace-declares-in-defun defun declares)))
    defun))

;todo: use this more
(defund replace-xarg-in-defun (xarg val defun)
  (declare (xargs :guard (and (keywordp xarg)
                              (defun-formp defun))
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (let* ((declares (get-declares-from-defun defun))
         (declares (replace-xarg-in-declares xarg val declares))
         (defun (replace-declares-in-defun defun declares)))
    defun))

(defund remove-xarg-in-defun (xarg defun)
  (declare (xargs :guard (and (keywordp xarg)
                              (defun-formp defun))
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (let* ((declares (get-declares-from-defun defun))
         (declares (remove-xarg-in-declares xarg declares))
         (defun (replace-declares-in-defun defun declares)))
    defun))

(defthm defun-formp-of-replace-xarg-in-defun
  (implies (and (keywordp xarg)
                (defun-formp defun))
           (defun-formp (replace-xarg-in-defun xarg val defun)))
  :hints (("Goal" :in-theory (enable replace-xarg-in-defun))))

(defund replace-xarg-in-defuns (xarg val defuns)
  (declare (xargs :guard (and (keywordp xarg)
                              (true-listp defuns)
                              (all-defun-formp defuns))))
  (if (endp defuns)
      nil
    (cons (replace-xarg-in-defun xarg val (first defuns))
          (replace-xarg-in-defuns xarg val (rest defuns)))))

(defund replace-xarg-in-mutual-recursion (xarg val mutual-recursion)
  (declare (xargs :guard (and (keywordp xarg)
                              (mutual-recursion-formp mutual-recursion))
                  :guard-hints (("Goal" :in-theory (enable mutual-recursion-formp)))))
  `(mutual-recursion ,@(replace-xarg-in-defuns xarg val (fargs mutual-recursion))))

;; Removes hints (and similar things) from a defun's xargs.
(defun remove-hints-from-defun (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (let* ((declares (get-declares-from-defun defun))
         (declares (remove-xarg-in-declares :hints declares))
         (declares (remove-xarg-in-declares :otf-flg declares))
         (declares (remove-xarg-in-declares :measure-debug declares))
         (declares (remove-xarg-in-declares :guard-hints declares))
         (declares (remove-xarg-in-declares :guard-simplify declares))
         (declares (remove-xarg-in-declares :guard-debug declares)))
    (replace-declares-in-defun defun declares)))
