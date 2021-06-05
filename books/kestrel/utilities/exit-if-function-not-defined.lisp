; A utility to ensure a function is defined
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defund exit-if-function-not-defined-fn (name state)
  (declare (xargs :guard (symbolp name)
                  :stobjs state))
  (if (getpropc name 'unnormalized-body nil (w state))
      nil ; function is defined, so don't exit
    (prog2$ (cw "ERROR: Exiting ACL2 because ~x0 is not defined!" name)
            (exit 1))))

;; Exit ACL2 immediately (!) if NAME is not a defined function.  Can prevent us
;; from calling save-exec when the stuff intended to be in the saved image did
;; not load properly (e.g., in the script that calls save-exec, you would call
;; this first).
(defmacro exit-if-function-not-defined (name)
  `(exit-if-function-not-defined-fn ',name state))
