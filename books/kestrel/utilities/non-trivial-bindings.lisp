; Finding lambda bindings where vars are not bound to themselves
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also collect-non-trivial-bindings, but that one is in :program mode.
;; A "non-trivial binding" is a binding of some var to some value other than itself.
(defund non-trivial-bindings (vars vals)
  (declare (xargs :guard (and (symbol-listp vars)
                              (true-listp vals))))
  (if (endp vars)
      nil
    (let ((var (first vars))
          (val (first vals)))
      (if (equal var val)
          ;; trivial binding, so skip:
          (non-trivial-bindings (rest vars) (rest vals))
        (cons (cons var val)
              (non-trivial-bindings (rest vars) (rest vals)))))))

(defthm symbol-alistp-of-non-trivial-bindings
  (implies (symbol-listp vars)
           (symbol-alistp (non-trivial-bindings vars vals)))
  :hints (("Goal" :in-theory (enable non-trivial-bindings))))

(defthm symbol-listp-of-strio-cars-of-non-trivial-bindings
  (implies (symbol-listp vars)
           (symbol-listp (strip-cars (non-trivial-bindings vars vals))))
  :hints (("Goal" :in-theory (enable non-trivial-bindings))))

(defthm pseudo-term-listp-of-strip-cdrs-of-trivial-bindings
  (implies (pseudo-term-listp vals)
           (pseudo-term-listp (strip-cdrs (non-trivial-bindings vars vals))))
  :hints (("Goal" :in-theory (enable non-trivial-bindings))))
