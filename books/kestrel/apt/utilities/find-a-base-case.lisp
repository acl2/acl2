;; Author: Grant Jurgensen (grant@kestrel.edu)

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/terms-light/expr-calls-fn" :dir :system)
(include-book "kestrel/utilities/translate" :dir :system)
(include-book "kestrel/utilities/magic-macroexpand" :dir :system)
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

(defthm pseudo-termp-of-if-condition
  (implies (and (pseudo-termp term)
                (eq 'if (ffn-symb term)))
           (pseudo-termp (farg1 term))))

(defthm pseudo-termp-of-if-then-branch
  (implies (and (pseudo-termp term)
                (eq 'if (ffn-symb term)))
           (pseudo-termp (farg2 term))))

(defthm pseudo-termp-of-if-else-branch
  (implies (and (pseudo-termp term)
                (eq 'if (ffn-symb term)))
           (pseudo-termp (farg3 term))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Variant on translated terms

;; `term` is the term to find a base-case within.
;; `fns` is a list of functions to avoid. A base-case must not include these functions.
;; If `prefer-then` is `t`, we search with a bias toward "then" branches. If it
;; is `nil`, we are biased toward "else" branches.

;; Returns `(mv erp all-base largest)`, where `erp` is `nil` when a base-case
;; is found, `all-base` is `t` when the entire term is a base-case, and
;; if `erp` and `all-base` are both `nil`, then `largest` is the largest base-case.
(defun find-a-base-case-translated-aux (term fns prefer-then)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbol-listp fns)
                              (booleanp prefer-then))))
  (b* (((unless (consp term)) (mv nil t nil))
       ((unless (eq 'if (ffn-symb term)))
        (if (expr-calls-some-fn fns term)
            (mv t nil nil)
          (mv nil t nil)))
       ((mv erp-then all-base-then largest-then)
        (find-a-base-case-translated-aux (farg2 term) fns prefer-then))
       ((mv erp-else all-base-else largest-else)
        (find-a-base-case-translated-aux (farg3 term) fns prefer-then)))
    (cond (erp-then
           (if erp-else
               (mv erp-else nil nil)
             (mv nil nil (if all-base-else
                             (farg3 term)
                           largest-else))))
          (erp-else
           (mv nil nil (if all-base-then
                           (farg2 term)
                         largest-then)))
          (all-base-then
           (if all-base-else
               (if (not (expr-calls-some-fn fns (farg1 term)))
                   (mv nil t nil)
                 (mv nil nil (if prefer-then
                                 (farg2 term)
                               (farg3 term))))
             (mv nil nil (farg2 term))))
          (all-base-else
           (mv nil nil (farg3 term)))
          (prefer-then (mv nil nil largest-then))
          (t (mv nil nil largest-else)))))

(defun find-a-base-case-translated (term fns prefer-then)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbol-listp fns)
                              (booleanp prefer-then))))
  (mv-let (erp all-base largest)
          (find-a-base-case-translated-aux term fns prefer-then)
          (cond (erp (hard-error 'find-a-base-case "Cannot find a base case!" nil))
                (all-base term)
                (t largest))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Variant on untranslated terms

(include-book "kestrel/utilities/fake-worlds" :dir :system)

(defun untranslated-expr-calls-some-fn (fns term wrld)
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld))
                  :mode :program))
  (expr-calls-some-fn fns (translate-term term 'top wrld)))

(defun find-a-base-case-aux (term fns prefer-then wrld state)
  (declare (xargs :guard (and (symbol-listp fns)
                              (booleanp prefer-then)
                              (plist-worldp wrld))
                  :mode :program
                  :stobjs state))
  (b* (((unless (consp term)) (mv nil t nil))
       ((mv erp term) (magic-macroexpand term 'magic wrld state))
       ((when erp) (mv erp nil nil))
       ((unless (consp term)) (mv nil t nil))
       ((unless (eq 'if (ffn-symb term)))
        (if (untranslated-expr-calls-some-fn fns term wrld)
            (mv t nil nil)
          (mv nil t nil)))
       ((mv erp-then all-base-then largest-then)
        (find-a-base-case-aux (farg2 term) fns prefer-then wrld state))
       ((mv erp-else all-base-else largest-else)
        (find-a-base-case-aux (farg3 term) fns prefer-then wrld state)))
    (cond (erp-then
           (if erp-else
               (mv erp-else nil nil)
             (mv nil nil (if all-base-else
                             (farg3 term)
                           largest-else))))
          (erp-else
           (mv nil nil (if all-base-then
                           (farg2 term)
                         largest-then)))
          (all-base-then
           (if all-base-else
               (if (not (untranslated-expr-calls-some-fn fns (farg1 term) wrld))
                   (mv nil t nil)
                 (mv nil nil (if prefer-then
                                 (farg2 term)
                               (farg3 term))))
             (mv nil nil (farg2 term))))
          (all-base-else
           (mv nil nil (farg3 term)))
          (prefer-then (mv nil nil largest-then))
          (t (mv nil nil largest-else)))))

(defun find-a-base-case (term fns fake-fns prefer-then state)
  (declare (xargs :guard (and (symbol-listp fns)
                              (symbol-alistp fake-fns)
                              (nat-listp (strip-cdrs fake-fns))
                              (booleanp prefer-then))
                  :mode :program
                  :stobjs state))
  (mv-let (erp all-base largest)
          (find-a-base-case-aux term
                                (append fns (strip-cars fake-fns))
                                prefer-then
                                (add-fake-fns-to-world fake-fns (w state))
                                state)
          (cond (erp (hard-error 'find-a-base-case "Cannot find a base case!" nil))
                (all-base term)
                (t largest))))
