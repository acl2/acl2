; Choosing which variant of defun to use
;
; Copyright (C) 2016-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/enumerations" :dir :system)
(include-book "kestrel/utilities/system/world-queries" :dir :system)

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
                              (t/nil/auto-p new-fn-non-executable)
                              (t/nil/auto-p new-fn-disabled))
                  :stobjs state
                  :verify-guards nil))
  (let* ((old-fn-disabled (fundef-disabledp old-fn state))
         (old-fn-non-executable (non-executablep old-fn (w state)))
         (disabled (if (eq new-fn-disabled :auto)
                       ;; :auto means disable iff the old function is disabled
                       old-fn-disabled
                     new-fn-disabled))
         (non-executable (if (eq new-fn-non-executable :auto)
                             ;; :auto means non-exec iff the old function is
                             ;; non-exec
                             old-fn-non-executable
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
