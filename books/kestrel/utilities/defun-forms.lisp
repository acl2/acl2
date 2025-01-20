; Utilities for processing defun forms
;
; Copyright (C) 2015-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

(include-book "declares0") ; for all-declarep
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/butlast" :dir :system))
(local (include-book "kestrel/utilities/assoc-keyword" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(local
 (defthm butlast-of-append-helper
   (implies (equal (len y) n)
             (equal (butlast (append x y) n)
                    (true-list-fix x)))
   :hints (("Goal" :in-theory (enable butlast append)))))

;; (defthm symbol-listp-of-butlast
;;   (implies (and (SYMBOL-LISTP X)
;;                 (natp n)
;;                 (<= n (len x)))
;;            (SYMBOL-LISTP (BUTLAST X N)))
;;   :hints (("Goal" :in-theory (enable butlast SYMBOL-LISTP))))

(defconst *defun-types*
  '(defun defund defun-nx defund-nx))

;add more to this!
;; (<defun-type> <name> <formals> <declare/doc-string>* <body>)
(defund defun-formp (defun)
  (declare (xargs :guard t))
  (and (true-listp defun)
       (>= (len defun) 4)
       (member-eq (first defun) *defun-types*) ;TODO: Handle defun-inline, etc.?  define (maybe not)  Handle anything we might call fixup-defun on...
       (let* ((args (fargs defun))
              (name (first args))
              (formals (second args))
              (declares-and-doc-strings (butlast (cdr (cdr args)) 1)) ; skip name and args, remove body (comes last)
              (declares (remove-strings declares-and-doc-strings)) ; todo: could check that there is at most one doc string
              ;; (body (car (last args))) ; not much to say about the body, since it is an untranslated term
              )
         (and (symbolp name)
              (symbol-listp formals)
              (all-declarep declares)))))

(defund get-declares-from-defun (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (let* ((args (fargs defun))
         (declares-and-doc-strings (butlast (cdr (cdr args)) 1)))
    (remove-strings declares-and-doc-strings)))

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

(defund get-formals-from-defun (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (third defun))

(defund get-body-from-defun (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (car (last defun)))

(defund get-arity-from-defun (defun)
  (declare (xargs :guard (defun-formp defun)))
  (len (get-formals-from-defun defun)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund replace-declares-in-defun (defun declares)
  (declare (xargs :guard (and (defun-formp defun)
                              (true-listp declares)
                              (all-declarep declares))
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))
                  ))
  `(,(first defun) ;defun, defund, etc.
    ,(get-name-from-defun defun)
    ,(get-formals-from-defun defun)
    ;; TODO: Keep the doc-string, if present.
    ,@declares ;the new declares
    ,(get-body-from-defun defun)))

(local (in-theory (disable all-declarep)))

(defthm defun-formp-of-replace-declares-in-defun
  (implies (and (defun-formp defun)
                (true-listp declares)
                (all-declarep declares))
           (defun-formp (replace-declares-in-defun defun declares)))
  :hints (("Goal" :in-theory (enable replace-declares-in-defun
                                     defun-formp
                                     get-name-from-defun
                                     get-formals-from-defun
                                     get-body-from-defun))))
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

;; Checker whether DEFUN has an explicit :mode :program.
(defund defun-has-mode-programp (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (let* ((xargs (get-xargs-from-defun defun))
         (mode (assoc-keyword :mode xargs)))
    (if (not mode)
        nil
      (eq :program (cadr mode)))))

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
