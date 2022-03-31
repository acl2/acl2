; Print verbosity levels
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Consider using numeric print levels for faster comparison

(defund axe-print-levelp (x)
  (declare (xargs :guard t))
  (member-eq x '(nil :brief t :verbose :verbose!)))

(defthm axe-print-levelp-forward-to-symbolp
  (implies (axe-print-levelp x)
           (symbolp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-print-levelp))))
