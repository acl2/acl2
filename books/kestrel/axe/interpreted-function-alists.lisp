; Operations on interpreted-function-alists
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
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
(include-book "kestrel/utilities/supporting-functions" :dir :system)

; this does not take pains to add subfunctions called by fn
;todo: call fn-formals?
(defund add-to-interpreted-function-alist (fn alist wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (symbol-alistp alist)
                              (plist-worldp wrld))))
  (let* ((props (getprops fn 'current-acl2-world wrld)))
    (if (not props)
        (er hard? 'add-to-interpreted-function-alist "Can't find a function named ~x0." fn)
      ;;fixme, check that it's indeed a function?
      (let* ((body (lookup-eq 'unnormalized-body props))
             (formals (lookup-eq 'formals props)))
        (if (not body)
            ;; print a warning
            (prog2$ ;(er hard? 'add-to-interpreted-function-alist "This function has no body: ~x0" fn)
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
                    (er hard? 'add-to-interpreted-function-alist "Inconsistent definitions for: ~x0" fn))
                (if (not (symbol-listp formals))
                    (prog2$ (er hard? 'add-to-interpreted-function-alist "Bad formals for ~x0: ~x1" fn formals)
                            alist)
                  (acons fn
                         (list formals body)
                         alist))))))))))

(defthm interpreted-function-alistp-of-add-to-interpreted-function-alist
  (implies (and (interpreted-function-alistp alist)
                (symbolp fn))
           (interpreted-function-alistp (add-to-interpreted-function-alist fn alist wrld)))
  :hints (("Goal" :in-theory (enable add-to-interpreted-function-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;returns an extension of acc
;this checks that fns aren't already present with different definitions
; this does not take pains to add subfunctions called by any of the fns
(defund add-fns-to-interpreted-function-alist (fns acc wrld)
  (declare (xargs :guard (and (symbol-listp fns)
                              (interpreted-function-alistp acc)
                              (plist-worldp wrld))))
  (if (endp fns)
      acc
    (let* ((fn (car fns)))
      (add-fns-to-interpreted-function-alist (cdr fns)
                                             (add-to-interpreted-function-alist fn acc wrld)
                                             wrld))))

(defthm interpreted-function-alistp-of-add-fns-to-interpreted-function-alist
  (implies (and (interpreted-function-alistp acc)
                (symbol-listp fns))
           (interpreted-function-alistp (add-fns-to-interpreted-function-alist fns acc wrld)))
  :hints (("Goal" :in-theory (enable add-fns-to-interpreted-function-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Create an interpreted-function-alist for FNS, a list of function names, by
;; getting their formals and bodies from WRLD.  See also
;; make-complete-interpreted-function-alist, a variant that also adds all
;; necessary supporting functions.
(defund make-interpreted-function-alist (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld))))
  (add-fns-to-interpreted-function-alist fns nil wrld))

(defthm interpreted-function-alistp-of-make-interpreted-function-alist
  (implies (symbol-listp fns)
           (interpreted-function-alistp (make-interpreted-function-alist fns wrld)))
  :hints (("Goal" :in-theory (enable make-interpreted-function-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund interpreted-function-alist-completep-aux (alist
                                                  ok-fns ; includss all functions built-in to the evaluator and all functions in the original alist
                                                  )
  (declare (xargs :guard (and (interpreted-function-alistp alist)
                              (symbol-listp ok-fns))
                  :guard-hints (("Goal" :in-theory (enable interpreted-function-alistp
                                                           all-interpreted-function-infop)))))
  (if (endp alist)
      t
    (let* ((pair (first alist))
           (fn (car pair))
           (info (cdr pair))
           ;; (formals (car info))
           (body (cadr info))
           (mentioned-fns (get-fns-in-term body)))
      (if (not (subsetp-equal mentioned-fns ok-fns))
          (prog2$ (cw "WARNING: Intepreted-function-alist is missing defs for: ~x0 (called by ~x1)." (set-difference-eq mentioned-fns ok-fns) fn)
                  nil)
        (interpreted-function-alist-completep-aux (rest alist) ok-fns)))))

;; Checks that there are no missing functions in the interpreted-function-alist
;; (functions called by other functions in the alist and that are not among the
;; built-in-fns).  Such missing functions would cause evaluation of functions
;; in the alist to fail).
(defund interpreted-function-alist-completep (alist built-in-fns)
  (declare (xargs :guard (and (interpreted-function-alistp alist)
                              (symbol-listp built-in-fns))))
  (interpreted-function-alist-completep-aux alist
                                            (append (strip-cars alist)
                                                    built-in-fns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Make an interpreted-function-alist capable of interpreting all of the FNS
;; (thus, including their subfunctions).
(defund make-complete-interpreted-function-alist (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld))))
  (mv-let (defined-fns undefined-fns stopper-fns)
    (fns-supporting-fns fns nil wrld)
    (declare (ignore undefined-fns stopper-fns))
    (make-interpreted-function-alist defined-fns wrld)))
