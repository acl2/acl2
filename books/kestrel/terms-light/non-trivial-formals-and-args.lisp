; Finding lambda formals that are not bound to themselves, and their args.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Finds the members of FORMALS that don't correspond to themselves in the ARGS.
;; Returns (mv non-trivial-formals non-trivial-args).
(defund non-trivial-formals-and-args (formals args)
  (declare (xargs :guard (and (symbol-listp formals)
                              (true-listp args) ; often, but not necessarily, pseudo-terms
                              )))
  (if (endp formals)
      (mv nil nil)
    (let ((formal (first formals))
          (arg (first args)))
      (mv-let (rest-formals rest-args)
        (non-trivial-formals-and-args (rest formals) (rest args))
        (if (equal formal arg)
            ;; skip since trivial:
            (mv rest-formals rest-args)
          (mv (cons formal rest-formals)
              (cons arg rest-args)))))))

(defthm symbol-listp-of-mv-nth-0-of-non-trivial-formals-and-args
  (implies (symbol-listp formals)
           (symbol-listp (mv-nth 0 (non-trivial-formals-and-args formals args))))
  :hints (("Goal" :in-theory (enable non-trivial-formals-and-args))))

(defthm true-listp-of-mv-nth-0-of-non-trivial-formals-and-args
  (implies (symbol-listp formals)
           (true-listp (mv-nth 0 (non-trivial-formals-and-args formals args))))
  :hints (("Goal" :in-theory (enable non-trivial-formals-and-args))))

(defthm true-listp-of-mv-nth-1-of-non-trivial-formals-and-args
  (implies (true-listp args)
           (true-listp (mv-nth 1 (non-trivial-formals-and-args formals args))))
  :hints (("Goal" :in-theory (enable non-trivial-formals-and-args))))

(defthm pseudo-term-listp-of-mv-nth-1-of-non-trivial-formals-and-args
  (implies (pseudo-term-listp args)
           (pseudo-term-listp (mv-nth 1 (non-trivial-formals-and-args formals args))))
  :hints (("Goal" :in-theory (enable non-trivial-formals-and-args))))

(defthm len-of-mv-nth-1-of-non-trivial-formals-and-args
  (equal (len (mv-nth 1 (non-trivial-formals-and-args formals args)))
         (len (mv-nth 0 (non-trivial-formals-and-args formals args))))
  :hints (("Goal" :in-theory (enable non-trivial-formals-and-args))))

(defthm <=-of-acl2-count-of-mv-nth-1-of-non-trivial-formals-and-args-linear
  (implies (equal (len formals) (len args))
           (<= (acl2-count (mv-nth 1 (non-trivial-formals-and-args formals args)))
               (acl2-count args)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable non-trivial-formals-and-args))))
