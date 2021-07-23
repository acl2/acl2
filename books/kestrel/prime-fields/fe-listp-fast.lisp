; Quickly determining that something is a field element
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "fe-listp")
(include-book "kestrel/lists-light/append-with-key" :dir :system)

;; Generates an assumption saying that all the VARS are field-elements.  This
;; uses make-append-with-key-nest to allow faster lookups of FEP facts in the
;; resulting assumption.
(defun gen-fe-listp-assumption (vars prime)
  (declare (xargs :guard (and (symbol-listp vars)
                              (consp vars))))
  `(fe-listp ,(acl2::make-append-with-key-nest vars) ,prime))

;; test: (gen-fe-listp-assumption '(x1 x2 x3 x4 x5 x6 x7 x8 x9 x10))

;move:
;test:
(thm
 (implies (fe-listp
           (acl2::append-with-key
            'x5
            (acl2::append-with-key 'x2
                             (acl2::append-with-key 'x10
                                              (cons x1 nil)
                                              (cons x10 nil))
                             (acl2::append-with-key 'x3
                                              (cons x2 nil)
                                              (acl2::append-with-key 'x4
                                                               (cons x3 nil)
                                                               (cons x4 nil))))
            (acl2::append-with-key 'x7
                             (acl2::append-with-key 'x6
                                              (cons x5 nil)
                                              (cons x6 nil))
                             (acl2::append-with-key 'x8
                                              (cons x7 nil)
                                              (acl2::append-with-key 'x9
                                                               (cons x8 nil)
                                                               (cons x9 nil)))))
           prime)
          (and (fep x1 prime)
               (fep x2 prime)
               (fep x3 prime)
               (fep x4 prime)
               (fep x5 prime)
               (fep x6 prime)
               (fep x7 prime)
               (fep x8 prime)
               (fep x9 prime)
               (fep x10 prime)))
 :hints (("Goal" :in-theory (e/d (member-equal) ()))))
