; A utility to gather the let-bound vars in a term
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

;; Returns the members of formals that don't correspond to themselves in the args.
(defund non-trivial-formals (formals args)
  (declare (xargs :guard (and (symbol-listp formals)
                              (pseudo-term-listp args))))
  (if (endp formals)
      nil
    (let* ((formal (first formals))
           (arg (first args)))
      (if (equal formal arg)
          ;; skip since trivial:
          (non-trivial-formals (rest formals) (rest args))
        (cons formal (non-trivial-formals (rest formals) (rest args)))))))

(defthm symbol-listp-of-non-trivial-formals
  (implies (symbol-listp formals)
           (symbol-listp (non-trivial-formals formals args)))
  :hints (("Goal" :in-theory (enable non-trivial-formals))))
