; An evaluator that uses magic-ev-fncall.
;
; Copyright (C) 2019-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also magic-ev, but that one does not allow :program mode functions.
;; Other related things include unsafe-apply and ec-call.

(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

(local (in-theory (disable state-p
                           symbol-alistp ;todo: have the library above disable this
                           )))

(mutual-recursion
  ;; Returns (mv erp res), where either ERP is non-nil, indicating an error, or
  ;; RES the result of evaluating TERM under ALIST.  Throws a hard error if
  ;; something goes wrong.
  ;; The arguments HARD-ERROR-RETURNS-NILP and AOKP are simply passed through
  ;; to MAGIC-EV-FNCALL.
  (defun magic-ev-term (term alist hard-error-returns-nilp aokp state)
    (declare (xargs :guard (and (pseudo-termp term)
                                (symbol-alistp alist)
                                (booleanp hard-error-returns-nilp)
                                (booleanp aokp))
                    :stobjs state
                    :verify-guards nil ; done below
                    ))
    (if (variablep term)
        (let ((res (assoc-eq term alist)))
          (if res
              (mv nil (cdr res))
            ;; todo: return a msg here:
            (mv "Unbound var" nil)))
      (let ((fn (ffn-symb term)))
        (if (eq 'quote fn)
            (mv nil (unquote term))
          (if (eq 'if fn) ;magic-ev-fncall disallows IF
              (mv-let (erp test-res)
                (magic-ev-term (cadr term) alist hard-error-returns-nilp aokp state)
                (if erp
                    (mv erp nil)
                  (if test-res ; todo: special handling for OR?
                      (magic-ev-term (caddr term) alist hard-error-returns-nilp aokp state)
                    (magic-ev-term (cadddr term) alist hard-error-returns-nilp aokp state))))
            ;; TODO: Should we build in any common functions?
            ;; normal function call or lambda:
            (mv-let (erp arg-results)
              (magic-ev-terms (fargs term) alist hard-error-returns-nilp aokp state)
              (if erp
                  (mv erp nil)
                (if (consp fn)
                    ;; lambda application:
                    (magic-ev-term (lambda-body fn)
                                   (pairlis$ (lambda-formals fn) arg-results)
                                   hard-error-returns-nilp aokp state)
                  ;; normal function call:
                  (mv-let (v1 v2)
                    (magic-ev-fncall fn arg-results state nil nil)
                    (if v1 ; check for error
                        (mv v1 nil)
                      ;; no error:
                      (mv nil v2)))))))))))

  ;; Returns (mv erp res) where either ERP is non-nil, indicating an error, or
  ;; RES is the list resulting from evaluating TERMS under ALIST.
  (defun magic-ev-terms (terms alist hard-error-returns-nilp aokp state)
    (declare (xargs :guard (and (pseudo-term-listp terms)
                                (symbol-alistp alist)
                                (booleanp hard-error-returns-nilp)
                                (booleanp aokp))
                    :stobjs state))
    (if (endp terms)
        (mv nil nil)
      (mv-let (erp first-res)
        (magic-ev-term (first terms) alist hard-error-returns-nilp aokp state)
        (if erp
            (mv erp nil)
          (mv-let (erp rest-res)
            (magic-ev-terms (rest terms) alist hard-error-returns-nilp aokp state)
            (if erp
                (mv erp nil)
              (mv nil (cons first-res rest-res)))))))))

(defthm true-listp-of-mv-nth-1-of-magic-ev-terms
  (true-listp (mv-nth 1 (magic-ev-terms terms alist hard-error-returns-nilp aokp state)))
  :hints (("Goal" :induct (len terms))))

(verify-guards magic-ev-term
  :hints (("Goal" :expand ((pseudo-termp term)))))
