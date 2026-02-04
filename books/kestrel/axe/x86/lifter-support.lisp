; Utilities used by the x86 lifters
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "kestrel/x86/portcullis" :dir :system)

;; These assumptions get removed during pruning (unlikely to help and lead to
;; messages about non-known-boolean literals being dropped)
;; TODO: Add more?
;; TODO: Include IF?
;; TODO: This is x86-specific
(defconst *non-stp-assumption-functions*
  '(canonical-address-p$inline ; not used much anymore ; todo: update to what is used
    program-at
    separate
    x86p
    cr0bits-p$inline
    cr4bits-p$inline
    alignment-checking-enabled-p
    app-view))
