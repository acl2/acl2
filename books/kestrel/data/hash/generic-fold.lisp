; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HASH")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "kestrel/bv-lists/byte-listp-def" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/bv-lists/byte-listp" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ generic-fold
  :parents (hashes)
  :short "A generic fold of a hash step function over a byte list."
  :long
  (xdoc::topstring
    (xdoc::p
      "A byte-serial hash algorithm is characterized by a state type, a step
       function which updates the state with one byte, and a finalizer. This
       book constrains the state type and step function and develops the
       algebra of folding the step function over a byte list. In particular,
       @(tsee update-bytes-of-append) is the key lemma allowing a hash of a
       serialized object (see @(see serialization)) to be decomposed along the
       structure of the serialization.")
    (xdoc::p
      "Concrete hash functions (e.g. @(see jenkins-one-at-a-time)) obtain
       instances of these theorems by functional instantiation. The initial
       state and the finalizer are not constrained here; they appear only
       outside the fold and require no generic theory."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The constrained hash state and step function:
;;   - statep recognizes hash states.
;;   - state-fix coerces arbitrary objects to hash states, and is the identity
;;     on hash states.
;;   - update-byte updates the state with one byte. It always produces a hash
;;     state, and does not distinguish a non-state from its coercion.

(encapsulate
  (((statep *) => *)
   ((state-fix *) => *)
   ((update-byte * *) => *))

  (local (defun statep (st)
           (natp st)))

  (local (defun state-fix (st)
           (nfix st)))

  (local (defun update-byte (st byte)
           (declare (ignore byte))
           (nfix st)))

  (defrule statep-of-state-fix
    (statep (state-fix st)))

  (defrule state-fix-when-statep
    (implies (statep st)
             (equal (state-fix st)
                    st))
    :enable nfix)

  (defrule statep-of-update-byte
    (statep (update-byte st byte)))

  (defrule update-byte-of-state-fix
    (equal (update-byte (state-fix st) byte)
           (update-byte st byte))
    :enable nfix))

;;;;;;;;;;;;;;;;;;;;

(defrule state-fix-of-state-fix
  (equal (state-fix (state-fix st))
         (state-fix st))
  :use (:instance state-fix-when-statep (st (state-fix st)))
  :disable state-fix-when-statep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-bytes (st (bytes acl2::byte-listp))
  :short "Fold the constrained step function over a byte list."
  :returns (st$ statep :hints (("Goal" :induct t)))
  (if (endp bytes)
      (state-fix st)
    (update-bytes (update-byte st (car bytes))
                  (cdr bytes))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t update-bytes)))

(defrule update-bytes-of-state-fix
  (equal (update-bytes (state-fix st) bytes)
         (update-bytes st bytes))
  :induct t
  :enable update-bytes)

(defrule update-bytes-of-append
  (equal (update-bytes st (append x y))
         (update-bytes (update-bytes st x) y))
  :induct (update-bytes st x)
  :enable update-bytes)
