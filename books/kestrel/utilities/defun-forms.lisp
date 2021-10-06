; Utilities for processing defun forms
;
; Copyright (C) 2015-2021 Kestrel Institute
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

(defund get-name-from-defun (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (second defun))

(defund get-body-from-defun (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (car (last defun)))

(defund get-formals-from-defun (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (third defun))

(defund get-arity-from-defun (defun)
  (declare (xargs :guard (defun-formp defun)))
  (len (get-formals-from-defun defun)))


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

;; Note that :STOBJS xargs and TYPE declares both count as guards.
(defund defun-has-a-guardp (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (some-declare-contributes-a-guardp (get-declares-from-defun defun)))

(local (in-theory (disable len)))

;; Checker whether DEFUN has an explicit :verify-guards nil.
(defund defun-has-verify-guards-nilp (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (let* ((xargs (get-xargs-from-defun defun))
         (verify-guards (assoc-keyword :verify-guards xargs)))
    (if (not verify-guards)
        nil
      (eq nil (cadr verify-guards)))))

;; Checker whether DEFUN has an explicit :verify-guards t.
(defund defun-has-verify-guards-tp (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (let* ((xargs (get-xargs-from-defun defun))
         (verify-guards (assoc-keyword :verify-guards xargs)))
    (if (not verify-guards)
        nil
      (eq t (cadr verify-guards)))))

;; This assumes the verify-guard-eagerness is 1 (the usual value).
(defun defun-demands-guard-verificationp (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (or (defun-has-verify-guards-tp defun)
      (and (defun-has-a-guardp defun)
           (not (defun-has-verify-guards-nilp defun)))))

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

(defund remove-xarg-in-defun (xarg defun)
  (declare (xargs :guard (and (keywordp xarg)
                              (defun-formp defun))
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (let* ((declares (get-declares-from-defun defun))
         (declares (remove-xarg-in-declares xarg declares))
         (defun (replace-declares-in-defun defun declares)))
    defun))

(defthm defun-formp-of-remove-xarg-in-defun
  (implies (and (keywordp xarg)
                (defun-formp defun))
           (defun-formp (remove-xarg-in-defun xarg defun)))
  :hints (("Goal" :in-theory (enable remove-xarg-in-defun))))

;todo: use this more
(defund replace-xarg-in-defun (xarg val defun)
  (declare (xargs :guard (and (keywordp xarg)
                              (defun-formp defun))
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (let* ((declares (get-declares-from-defun defun))
         (declares (replace-xarg-in-declares xarg val declares))
         (defun (replace-declares-in-defun defun declares)))
    defun))

(defthm defun-formp-of-replace-xarg-in-defun
  (implies (and (keywordp xarg)
                (defun-formp defun))
           (defun-formp (replace-xarg-in-defun xarg val defun)))
  :hints (("Goal" :in-theory (enable replace-xarg-in-defun))))

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

;; This assumes the verify-guard-eagerness is 1 (the usual value).
;; This avoids leaving in an unnecessary :verify-guards t.
(defund ensure-defun-demands-guard-verification (defun)
  (declare (xargs :guard (defun-formp defun)
;                  :guard-hints (("Goal" :in-theory (enable defun-formp)))
                  ))
  (let* ((defun (remove-xarg-in-defun :verify-guards defun))) ; remove any :verify-guards, no matter what it is
    ;; Add back :verify-guards only in the case of no explicit :guard, (declare (type ...)), or :stobj
    (if (defun-has-a-guardp defun)
        defun ; no need for :verify-guards
      (add-verify-guards-t-to-defun defun))))
