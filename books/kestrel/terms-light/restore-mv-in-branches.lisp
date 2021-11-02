; A utility to "untranslate" calls of MV
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/syntactic-lists" :dir :system)
(local (include-book "kestrel/arithmetic-light/types" :dir :system))

;; Returns the number of return values (in the sense of MV) of FN.
(defund num-return-values-of-fn (fn wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (not (member-eq fn *stobjs-out-invalid*))
                              (plist-worldp wrld))))
  (len (stobjs-out fn wrld)))

;move
(defthm natp-of-cdr-of-assoc-equal-when-nat-listp-of-strip-cdrs
  (implies (nat-listp (strip-cdrs alist))
           (iff (natp (cdr (assoc-equal key alist)))
                (assoc-equal key alist))))

(local (in-theory (disable natp)))

;; (defun make-assumed-fn-num-vals-alist (function-renaming wrld)
;;   (declare (xargs :guard (and (function-renamingp function-renaming)
;;                               (plist-worldp wrld))))
;;   (if (endp function-renaming)
;;       nil
;;     (let* ((entry (car function-renaming))
;;            (old-fn (car entry))
;;            (new-fn (cdr entry)))
;;       (if (member-eq old-fn *stobjs-out-invalid*)
;;           (er hard? 'make-assumed-fn-num-vals-alist "Can't get stobjs-out of ~x0." old-fn)
;;         (acons new-fn
;;                (num-return-values-of-fn old-fn wrld)
;;                (make-assumed-fn-num-vals-alist (rest function-renaming) wrld))))))

(defun restore-mv-in-branches (term num-values
                                    fns-to-assume-ok ; these often include things not yet defined in WRLD
                                    wrld)
  (declare (xargs :guard (and (pseudo-termp term)
                              (integerp num-values)
                              (<= 2 num-values)
                              (symbol-listp fns-to-assume-ok)
                              (plist-worldp wrld))
                  :guard-hints (("Goal" :in-theory (enable ACL2-NUMBERP-WHEN-NATP)))
                  ))
  (if (variablep term)
      (er hard? 'restore-mv-in-branches "Failed to restore ~x0 to a term with ~x1 values." term num-values)
    (let ((fn (ffn-symb term)))
      (if (or (eq 'quote fn)
              (eq 'cons fn))
          (if (not (and (syntactic-true-listp term)
                        (= (syntactic-length term) num-values)))
              (er hard? 'restore-mv-in-branches "Failed to restore ~x0 to a term with ~x1 values." term num-values)
            `(mv ,@(syntactic-list-elements term)))
        (if (eq 'if fn)
            `(if ,(farg1 term)
                 ,(restore-mv-in-branches (farg2 term) num-values fns-to-assume-ok wrld)
               ,(restore-mv-in-branches (farg3 term) num-values fns-to-assume-ok wrld))
          (if (eq 'return-last fn)
              `(return-last ,(farg1 term)
                            ,(farg2 term)
                            ,(restore-mv-in-branches (farg3 term) num-values fns-to-assume-ok wrld))
            (if (consp fn) ;; check for lambda application
                `((lambda ,(lambda-formals fn) ,(restore-mv-in-branches (lambda-body fn) num-values fns-to-assume-ok wrld))
                  ,@(fargs term))
              (if (member-eq fn fns-to-assume-ok)
                  term
                (if (= (num-return-values-of-fn fn wrld) num-values)
                    term
                  (er hard? 'restore-mv-in-branches "Failed to restore ~x0 to a term with ~x1 values." term num-values))))))))))

(defthm pseudo-termp-of-restore-mv-in-branches
  (implies (and (pseudo-termp term)
                (integerp num-values)
                (<= 2 num-values))
           (pseudo-termp (restore-mv-in-branches term num-values
                                                 fns-to-assume-ok
                                                 wrld))))
