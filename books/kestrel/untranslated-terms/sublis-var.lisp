; Applying substitutions to untranslated terms
;
; Copyright (C) 2015-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: INCOMPLETE

(include-book "std/util/bstar" :dir :system) ;  included because this book "knows" about b*
(include-book "let-helpers")
(include-book "bstar-helpers")
(include-book "cond-helpers")
(include-book "case-match-helpers")
(include-book "std/alists/remove-assocs" :dir :system) ; todo: use clear-keys, or deprecate that?
(include-book "untranslated-variablep")
(include-book "untranslated-constantp")
(include-book "kestrel/utilities/forms" :dir :system)

;; (mutual-recursion
;;  (defun sublis-var-untranslated-term$ (alist term wrld)
;;    (declare (xargs :guard (and ;; (untranslated-termp term)
;;                                (symbol-alistp alist)
;;                                ;; (untranslated-term-listp (strip-cdrs alist))
;;                                (plist-worldp wrld))
;;                    :verify-guards nil
;;                    :measure (acl2-count term)
;;                    :hints (("Goal" :do-not-induct t))
;;                    :ruler-extenders :all))
;;    (if (untranslated-variablep term)
;;        (if (assoc-equal term alist)
;;            (cdr (assoc-equal term alist))
;;          term)
;;      (if (atom term)
;;          term
;;        (if (fquotep term)
;;            term
;;          (let* ((fn (ffn-symb term)))
;;            (if (eq fn 'let)
;;                ;; (let <bindings> ...declares... <body>)
;;                (b* ((bindings (let-bindings term))
;;                     (declares (let-declares term))
;;                     (body (let-body term))
;;                     (vars (let-binding-vars bindings))
;;                     (terms (let-binding-terms bindings))
;;                     ;; Apply the replacement to the terms to which the vars
;;                     ;; are bound (okay because all bindings happen
;;                     ;; simultaneously):
;;                     (new-terms (sublis-var-untranslated-term-list$ alist terms wrld))
;;                     ;; Remove any bindings whose vars are shadowed by the let:
;;                     (alist-for-body (remove-assocs vars alist))
;;                     ;; (body-vars (free-vars-in-untranslated-term$ body wrld)) ; todo: requires the world
;;                     ;; FIXME, if there is overlap between 1) vars in the replacements for free vars in the body, and 2) the bound vars, then signal an error (for now)
;;                     (new-body (sublis-var-untranslated-term$ alist-for-body body wrld)))
;;                  `(let ,(make-let-bindings vars new-terms) ,@declares ,new-body))
;;              (if (eq fn 'let*) ;fffixme
;;                (let* ((bindings (let-bindings term))
;;                       (declares (let-declares term))
;;                       (body (let-body term)))
;;                  `(let* ,(sublis-var-in-let*-bindings$ alist bindings wrld)
;;                     ,@declares
;;                     ,(sublis-var-untranslated-term$ alist body wrld)))
;;                (if (eq fn 'b*) ;fffixme
;;                    (let* ((bindings (farg1 term))
;;                           (result-forms (rest (fargs term)))
;;                           (terms (extract-terms-from-b*-bindings bindings))
;;                           (new-terms (sublis-var-untranslated-term-list$ alist terms wrld))
;;                           (new-bindings (recreate-b*-bindings bindings new-terms)))
;;                      `(b* ,new-bindings
;;                         ,@(sublis-var-untranslated-term-list$ alist result-forms wrld)))
;;                  (if (eq 'cond fn) ; (cond ...clauses...)
;;                      (let* ((clauses (fargs term))
;;                             (terms (extract-terms-from-cond-clauses clauses))
;;                             (new-terms (sublis-var-untranslated-term-list$ alist terms wrld)))
;;                        `(cond ,@(recreate-cond-clauses clauses new-terms)))
;;                    (if (eq fn 'case) ;; (case <expr> ...pairs...)
;;                        (let* ((expr (farg1 term))
;;                               (pairs (cdr (fargs term)))
;;                               (vals-to-match (strip-cars pairs))
;;                               (vals-to-return (strip-cadrs pairs)))
;;                          `(case ,(sublis-var-untranslated-term$ alist expr wrld)
;;                             ,@(make-doublets vals-to-match
;;                                              (sublis-var-untranslated-term-list$ alist vals-to-return wrld))))
;;                      (if (eq fn 'case-match) ; (case-match sym ...cases...)
;;                          (b* ((sym (farg1 term)) ; must be a symbol
;;                               (new-sym (sublis-var-untranslated-term$ alist sym wrld))
;;                               ((when (not (and (symbolp new-sym)
;;                                                (or (untranslated-variablep new-sym)
;;                                                    (untranslated-constantp new-sym))
;;                                                ))) ; todo: could let-bind a new var, for use in the case-match?
;;                                (er hard? 'sublis-var-untranslated-term$ "Attempt to create a case-match whose first argument is ~x0, which is not a legal symbol." new-sym))
;;                               (cases (rest (fargs term)))
;;                               ;;(terms-from-cases (extract-terms-from-case-match-cases cases))
;;                               ;;(new-terms-from-cases (sublis-var-untranslated-term-list$ alist terms-from-cases wrld))
;;                               ;;(new-cases (recreate-case-match-cases cases new-terms-from-cases))
;;                               (new-cases (sublis-var-case-match-cases$ alist cases wrld)))
;;                            `(case-match ,new-sym ,@new-cases))
;;                        (let* ((args (fargs term))
;;                               (args (sublis-var-untranslated-term-list$ alist args wrld)))
;;                          ;;todo: handle lambdas
;;                          (let* ((term (cons fn args)))
;;                            term)))))))))))))

;;  (defun sublis-var-in-let*-bindings$ (alist pairs wrld)
;;    (declare (xargs :guard (and (doublet-listp pairs)
;;                                (symbol-listp (strip-cars pairs))
;;                                ;(var-untranslated-term-pairsp pairs)
;;                                (symbol-alistp alist)
;;                                ;(untranslated-term-listp (strip-cdrs alist))
;;                                )))
;;    (if (endp pairs)
;;        nil
;;      (let* ((pair (first pairs))
;;             (var (first pair))
;;             (term (second pair)))
;;        (cons (list var
;;                    (sublis-var-untranslated-term$ alist term wrld))
;;              (sublis-var-in-let*-bindings$ alist (rest pairs) wrld)))))

;;  ;fixme: consider capture
;;  (defun sublis-var-case-match-cases$ (alist cases wrld)
;;    (declare (xargs :guard (and (legal-case-match-casesp cases)
;;                                ;; (untranslated-term-listp (extract-terms-from-case-match-cases cases))
;;                                (symbol-alistp alist)
;;                                ;;(untranslated-term-listp (strip-cdrs alist))
;;                                )))
;;    (if (endp cases)
;;        nil
;;      (let* ((case (first cases))
;;             (pattern (first case))
;;             (declares (butlast (rest case) 1)) ; may be empty
;;             (body (car (last case)))
;;             (alist-for-body (remove-assocs (vars-bound-in-case-match-pattern pattern) alist)))
;;        (cons `(,pattern
;;                ,@declares
;;                ,(sublis-var-untranslated-term$ alist-for-body body wrld))
;;              (sublis-var-case-match-cases$ alist (rest cases) wrld)))))

;;  (defun sublis-var-untranslated-term-list$ (alist terms wrld)
;;    (declare (xargs :guard (and (untranslated-term-listp terms)
;;                                (symbol-alistp alist)
;;                                (untranslated-term-listp (strip-cdrs alist)))))
;;    (if (endp terms)
;;        nil
;;      (cons (sublis-var-untranslated-term$ alist
;;                                           (first terms)
;;                                            wrld)
;;            (sublis-var-untranslated-term-list$ alist
;;                                                (rest terms)
;;                                                 wrld)))))
