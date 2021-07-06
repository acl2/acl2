; Operations on interpreted-function-alists
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "interpreted-function-alistp")
(include-book "kestrel/utilities/remove-guard-holders" :dir :system)
(include-book "kestrel/utilities/terms" :dir :system) ; for get-fns-in-term
(local (include-book "kestrel/utilities/remove-guard-holders" :dir :system))

; this does not take pains to add subfunctions called by fn
;todo: call fn-formals?
(defun add-to-interpreted-function-alist (fn alist wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (symbol-alistp alist)
                              (plist-worldp wrld))))
  (let* ((props (getprops fn 'current-acl2-world wrld)))
    (if (not props)
        (hard-error 'add-to-interpreted-function-alist "Can't find a function named ~x0." (list (cons #\0 fn)))
      ;;fixme, check that it's indeed a function?
      (let* ((body (lookup-eq 'unnormalized-body props))
             (formals (lookup-eq 'formals props)))
        (if (not body)
            ;; print a warning
            (prog2$ ;(hard-error 'add-to-interpreted-function-alist "This function has no body: ~x0" (acons #\0 fn nil))
             (cw "NOTE: This function has no body: ~x0.~%" fn)
             alist)
          (if (not (pseudo-termp body))
              (prog2$ (er hard? 'add-to-interpreted-function-alist "Bad body for ~x0: ~x1" fn body)
                      alist)
            (let ((match (lookup-eq fn alist))
                  ;; We call remove-guard-holders-and-clean-up-lambdas to get rid of calls of
                  ;; return-last (and other things).  Note that this will get
                  ;; the :logic part of an MBE.  We might prefer the :exec
                  ;; part, but its correctness assumes the guards hold.  If the
                  ;; :logic part is too slow, consider building the function
                  ;; into an evaluator.
                  (body (remove-guard-holders-and-clean-up-lambdas body)))
              (if match
                  (if (equal match (list formals body))
                      ;;consistent with previous definition:
                      alist
                    (hard-error 'add-to-interpreted-function-alist "Inconsistent definitions for: ~x0" (acons #\0 fn nil)))
                (if (not (symbol-listp formals))
                    (prog2$ (er hard? 'add-to-interpreted-function-alist "Bad formals for ~x0: ~x1" fn formals)
                            alist)
                  (acons fn
                         (list formals body)
                         alist))))))))))

(defthm interpreted-function-alistp-of-add-to-interpreted-function-alist
  (implies (and (interpreted-function-alistp alist)
                (symbolp fn))
           (interpreted-function-alistp (add-to-interpreted-function-alist fn alist wrld))))

;returns an extension of acc
;this checks that fns aren't already present with different definitions
; this does not take pains to add subfunctions called by any of the fns
(defun add-fns-to-interpreted-function-alist (fns acc wrld)
  (declare (xargs :guard (and (symbol-listp fns)
                              (symbol-alistp acc)
                              (plist-worldp wrld))))
  (if (endp fns)
      acc
    (let* ((fn (car fns)))
      (add-fns-to-interpreted-function-alist (cdr fns)
                                        (add-to-interpreted-function-alist fn acc wrld)
                                        wrld))))

(defthm interpreted-function-alistp-of-add-fns-to-interpreted-function-alist
  (implies (and (interpreted-function-alistp alist)
                (symbol-listp fns))
           (interpreted-function-alistp (add-fns-to-interpreted-function-alist fns alist wrld))))

;; Create an interpreted-function-alist for FNS, a list of function names, by
;; getting their formals and bodies from WRLD.  TODO: Make a variant that also
;; adds all necessary supporting functions.
(defun make-interpreted-function-alist (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld))))
  (add-fns-to-interpreted-function-alist fns nil wrld))

(defthm interpreted-function-alistp-of-make-interpreted-function-alist
  (implies (symbol-listp fns)
           (interpreted-function-alistp (make-interpreted-function-alist fns wrld))))

;;;
;;; interpreted-function-alist-completep
;;;

;; Checks that there are no missing functions in the interpreted-function-alist
;; (functions called by other functions in the alist, which will cause
;; evaluation of functions in the alist to fail).
(defun interpreted-function-alist-completep-aux (alist all-fns)
  (declare (xargs :guard (and (interpreted-function-alistp alist)
                              (symbol-listp all-fns))
                  :guard-hints (("Goal" :in-theory (enable INTERPRETED-FUNCTION-ALISTP)))))
  (if (endp alist)
      t
    (let* ((pair (first alist))
           (fn (car pair))
           (info (cdr pair))
           ;; (formals (car info))
           (body (cadr info))
           (mentioned-fns (get-fns-in-term body)))
      (if (not (subsetp-equal mentioned-fns all-fns))
          (prog2$ (cw "WARNING: Intepreted-function-alist is missing defs for: ~x0 (called by ~x1)." (set-difference-eq mentioned-fns all-fns) fn)
                  nil)
        (interpreted-function-alist-completep-aux (rest alist) all-fns)))))

(defun interpreted-function-alist-completep (alist built-in-fns)
  (declare (xargs :guard (and (interpreted-function-alistp alist)
                              (symbol-listp built-in-fns))))
  (interpreted-function-alist-completep-aux alist
                                            (append (strip-cars alist)
                                                    built-in-fns)))
