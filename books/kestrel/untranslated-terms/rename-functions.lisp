; Renaming functions in untranslated terms
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "replace-calls")

;; The point of this utility is to preserve as much of the structure of the
;; term (macro calls, named constants, lets, etc.) as possible.

;; See tests in rename-functions-tests.lisp.

(local (in-theory (disable natp)))

(local
 (defthm natp-of-cdr-of-assoc-equal
   (IMPLIES (AND (NAT-LISTP (STRIP-CDRS alist))
                 (SYMBOL-ALISTP alist)
                 (member-equal fn (STRIP-CARS alist)))
            (NATP (CDR (ASSOC-EQUAL fn alist))))))

;; Returns a list of forms of the form (<function> :arg1 ... :argn).
(defund make-calls-on-args-keywords (fns fn-arity-alist)
  (declare (xargs :guard (and (symbol-listp fns)
                              (symbol-alistp fn-arity-alist)
                              (nat-listp (strip-cdrs fn-arity-alist))
                              (subsetp-eq fns (strip-cars fn-arity-alist)))))
  (if (endp fns)
      nil
    (let* ((fn (first fns))
           (arity (cdr (assoc-eq fn fn-arity-alist))))
      (cons (cons fn (make-arg-keywords arity))
            (make-calls-on-args-keywords (rest fns) fn-arity-alist)))))

;; Rename functions according to function-renaming.  This calls replace-calls-in-untranslated-term
;; using an alist that maps each function to a form of the form (<new-fn> :arg1 ... :argn).
(defund rename-functions-in-untranslated-term (term ; an untranslated term
                                               function-renaming ; the renaming to apply
                                               state ; needed for magic-macroexpand (why?)
                                               )
  (declare (xargs :guard (and (symbol-alistp function-renaming)
                              (symbol-listp (strip-cdrs function-renaming)))
                  :mode :program ; since translation is done
                  :stobjs state))
  (let* ((wrld (w state))
         (wrld (set-ignore-ok-in-world wrld))
         (new-fns-arity-alist (pairlis$ (strip-cdrs function-renaming)
                                        (fn-arities (strip-cars function-renaming) wrld)))
         ;; New fns from the renaming may appear in TERM, but they are not yet
         ;; in the world, so we make this fake world:
         (fake-wrld (add-fake-fns-to-world new-fns-arity-alist wrld))
         (alist (pairlis$ (strip-cars function-renaming)
                          (make-calls-on-args-keywords (strip-cdrs function-renaming)
                                                       new-fns-arity-alist))))
    (replace-calls-in-untranslated-term term
                                        alist
                                        fake-wrld ; contains real for fake entries for all functions in TERM
                                        state)))
