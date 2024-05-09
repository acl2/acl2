; Utilities to widen the margins
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/pos-fix" :dir :system)
(local (include-book "margins"))
(local (include-book "kestrel/utilities/state" :dir :system))

(local (in-theory (disable put-global)))

;; Makes the margins very wide, saving the old margins.
(defund widen-margins (state)
  (declare (xargs :stobjs state))
  (let* (;; Save the old margins for later restoration by unwiden-margins:
         (state (f-put-global 'old-fmt-hard-right-margin (f-get-global 'fmt-hard-right-margin state) state))
         (state (f-put-global 'old-fmt-soft-right-margin (f-get-global 'fmt-soft-right-margin state) state))
         ;; Change the margins:
         (state (set-fmt-hard-right-margin 410 state))
         (state (set-fmt-soft-right-margin 400 state)))
    state))

;; Restores the margins to what they were before widen-margins was called.
(defund unwiden-margins (state)
  (declare (xargs :stobjs state
                  :guard-hints (("Goal" :in-theory (enable boundp-global)))))
  ;; Restore the margins:
  (let* ((state (if (boundp-global 'old-fmt-hard-right-margin state)
                    (set-fmt-hard-right-margin (pos-fix (f-get-global 'old-fmt-hard-right-margin state)) state)
                  state))
         (state (if (boundp-global 'old-fmt-soft-right-margin state)
                    (set-fmt-soft-right-margin (pos-fix (f-get-global 'old-fmt-soft-right-margin state)) state)
                  state)))
    state))
