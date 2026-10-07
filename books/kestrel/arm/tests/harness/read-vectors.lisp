; Reading test vectors from a file
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

;; Reads test vectors (see vectors.lisp) from a file holding one vector per
;; S-expression, as a converter written in another language might produce.
;; Vectors contain only keywords, numbers, and strings, so the package in which
;; the file is read does not matter.  The first element of the file that is
;; not a test vector is reported by its position and id, which a guard
;; violation on the whole list would not tell.

(include-book "vectors")
(include-book "kestrel/file-io-light/read-objects-from-file" :dir :system)
(include-book "std/util/bstar" :dir :system)

;; The position in X of its first element that is not a test vector, counting
;; from I, or nil if there is none.
(defun first-bad-vector (x i)
  (declare (xargs :guard (natp i)))
  (if (atom x)
      nil
    (if (test-vectorp (car x))
        (first-bad-vector (cdr x) (+ 1 i))
      i)))

(defthm first-bad-vector-type
  (implies (natp i)
           (or (null (first-bad-vector x i))
               (natp (first-bad-vector x i))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable test-vectorp))))

(defthm test-vector-listp-when-not-first-bad-vector
  (implies (and (not (first-bad-vector x i)) ; binds i
                (natp i)
                (true-listp x))
           (test-vector-listp x))
  :hints (("Goal" :in-theory (disable test-vectorp))))

;; Reads the test vectors in the file FILENAME.
;; Returns (mv erp vectors state).
(defun read-vectors (filename state)
  (declare (xargs :guard (stringp filename)
                  :stobjs state))
  (b* (((mv erp objects state)
        (acl2::read-objects-from-file filename state))
       ((when erp)
        (mv erp nil state))
       (bad (first-bad-vector objects 0))
       ((when bad)
        (let ((object (nth bad objects)))
          (mv (list :bad-vector filename
                    :position bad
                    :id (and (keyword-value-listp object)
                             (vec-get :id object nil)))
              nil
              state))))
    (mv nil objects state)))

(defthm test-vector-listp-of-mv-nth-1-of-read-vectors
  (test-vector-listp (mv-nth 1 (read-vectors filename state))))
