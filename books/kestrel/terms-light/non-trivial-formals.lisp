; A utility to filter lambda formals that are not bound to themselves.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

;; Returns the members of FORMALS that don't correspond to themselves in the ARGS.
(defund non-trivial-formals (formals args)
  (declare (xargs :guard (and (symbol-listp formals)
                              (true-listp args) ; often, but not necessarily, pseudo-terms
                              )))
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

(defthm non-trivial-formals-of-cons-and-cons
  (equal (non-trivial-formals (cons formal formals) (cons arg args))
         (if (equal formal arg)
             (non-trivial-formals formals args)
           (cons formal (non-trivial-formals formals args))))
  :hints (("Goal" :in-theory (enable non-trivial-formals))))

(defthm non-trivial-formals-same
  (equal (non-trivial-formals formals formals)
         nil)
  :hints (("Goal" :induct t :in-theory (enable non-trivial-formals))))
