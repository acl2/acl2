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
(include-book "kestrel/executable-parsers/parsed-executable-tools" :dir :system)

;; These assumptions get removed during pruning (unlikely to help and lead to
;; messages about non-known-boolean literals being dropped)
;; TODO: Add more?
;; TODO: Include IF?
;; TODO: This is x86-specific
(defconst *non-stp-assumption-functions*
  '(canonical-address-p$inline ; not used much anymore ; todo: update to what is used
    program-at
    separate ; not used much anymore ; todo: update to what is used
    x86p
    cr0bits-p$inline
    cr4bits-p$inline
    alignment-checking-enabled-p
    app-view))

;; Returns a boolean
(defund resolve-position-independent (position-independent parsed-executable)
  (declare (xargs :guard (and (member-eq position-independent '(t nil :auto))
                              (parsed-executablep parsed-executable))))
  (let ((executable-type (parsed-executable-type parsed-executable)))
    (if (eq :auto position-independent)
        (if (eq executable-type :mach-o-64)
            t ; since clang seems to produce position-independent code by default ; todo: look at the PIE bit in the header.
          (if (eq executable-type :elf-64) ; todo: allow ELF32 as well?
              (elf-position-independentp parsed-executable)
            ;; TODO: Think about the other cases:
            t))
      ;; position-independent is t or nil, not :auto:
      position-independent)))
