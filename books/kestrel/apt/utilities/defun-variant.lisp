; Choosing which variant of defun to use
;
; Copyright (C) 2016-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/system/fundef-disabledp" :dir :system)
(include-book "std/system/non-executablep" :dir :system)
(include-book "std/system/function-namep" :dir :system)
(include-book "std/system/definedp" :dir :system)

;; Determine the appropriate variant of defun to use for the new function (defun, defund, defun-nx, or defund-nx).
;; See also isodata-new-pred/fun-macro.
;; (It's a pity that this needs to take state.  The root cause seems to be that
;; the "enabled structure" is in the state.)
;; As we extend the range of our transformations, we may want to generate
;; defun-sks, defines, and additional variants.
(defund defun-variant (old-fn ;; The old function symbol being transformed
                       new-fn-non-executable ;;Whether to make the new function non-executable (or :auto)
                       new-fn-disabled ;; Whether to disable the new function (or :auto)
                       state)
  (declare (xargs :guard (and (function-namep old-fn (w state))
                              (definedp old-fn (w state))
                              (member-eq new-fn-non-executable '(t nil :auto))
                              (member-eq new-fn-disabled '(t nil :auto)))
                  :stobjs state
                  :verify-guards nil ; todo: because of fundef-disabledp
                  ))
  (let* ((disabled (if (eq new-fn-disabled :auto)
                       ;; :auto means disable iff the old function is disabled:
                       (fundef-disabledp old-fn state)
                     new-fn-disabled))
         (non-executable (if (eq new-fn-non-executable :auto)
                             ;; :auto means non-exec iff the old function is
                             ;; non-exec:
                             (non-executablep old-fn (w state))
                           ;; Use the explicit boolean value provided:
                           new-fn-non-executable)))
    (if disabled
        (if non-executable
            'defund-nx
          'defund)
      (if non-executable
          'defun-nx
        'defun))))

(defthm defun-variant-return-type
  (member-equal (defun-variant old-fn new-fn-non-executable new-fn-disabled state)
                '(defun defund defun-nx defund-nx))
  :hints (("Goal" :in-theory (enable defun-variant))))
