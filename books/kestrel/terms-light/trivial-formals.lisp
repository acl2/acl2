; A utility to filter lambda formals that are bound to themselves.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

;; Returns the members of FORMALS that correspond to themselves in the ARGS.
(defund trivial-formals (formals args)
  (declare (xargs :guard (and (symbol-listp formals)
                              (pseudo-term-listp args))))
  (if (endp formals)
      nil
    (let* ((formal (first formals))
           (arg (first args)))
      (if (equal formal arg)
          ;; keep since trivial:
          (cons formal (trivial-formals (rest formals) (rest args)))
        (trivial-formals (rest formals) (rest args))))))

(defthm symbol-listp-of-trivial-formals
  (implies (symbol-listp formals)
           (symbol-listp (trivial-formals formals args)))
  :hints (("Goal" :in-theory (enable trivial-formals))))
