; Support for proofs about R1CSes
;
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "portcullis")
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(local (include-book "kestrel/prime-fields/equal-of-add-move-negs-bind-free" :dir :system))
(include-book "kestrel/prime-fields/rules2" :dir :system) ;reduce?
(include-book "kestrel/lists-light/append-with-key" :dir :system)
(include-book "kestrel/lists-light/memberp" :dir :system)
(include-book "kestrel/typed-lists-light/bit-listp" :dir :system)
(include-book "kestrel/bv/bvcat" :dir :system)
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)
(include-book "kestrel/bv/bitnot" :dir :system)
(local (include-book "kestrel/bv/bitwise" :dir :system))
(local (include-book "kestrel/bv/bvxor" :dir :system))
(local (include-book "kestrel/bv/rules9" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/bv/rules" :dir :system)) ; for  ACL2::GETBIT-OF-PLUS

;; TODO: Organize this material

(defthm acl2::bitp-when-bit-listp-and-memberp
  (implies (and (acl2::bit-listp free)
                (acl2::memberp x free))
           (acl2::bitp x)))

;; (defun gen-bit-listp-assumption (vars)
;;   (declare (xargs :guard (and (symbol-listp vars)
;;                               (consp vars))))
;;   `(acl2::bit-listp ,(acl2::make-append-with-key-nest vars)))

(defun acl2::make-bitp-claims-aux (terms acc)
  (declare (xargs :guard (true-listp terms)))
  (if (endp terms)
      acc
    (acl2::make-bitp-claims-aux (rest terms)
                                (cons `(bitp ,(first terms)) acc))))

;; Make a list of terms that together assert that all of the TERMS satisfy bitp.
(defun acl2::make-bitp-claims (terms)
  (declare (xargs :guard (true-listp terms)))
  (acl2::make-bitp-claims-aux (acl2::reverse-list terms) nil))
