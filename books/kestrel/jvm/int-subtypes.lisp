; Representation of subtypes of int in the JVM model
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

;;; TODO: Should these be functions or macros?
;;; TODO: Change these to the JVM package?

(include-book "kestrel/bv/slice" :dir :system)
(include-book "kestrel/bv/getbit" :dir :system)
(include-book "kestrel/bv/repeatbit" :dir :system)
(include-book "kestrel/jvm/java-types" :dir :system)

;; A boolean must be stored in an int field as 0 or 1 (see 2.3.4).
(defund acl2::java-boolean-as-int-p (i)
  (declare (xargs :guard t))
  (acl2::java-booleanp i))

;; A byte represented as part of a 32-bit int
(defund acl2::java-byte-as-int-p (i)
  (declare (xargs :guard t))
  (and (unsigned-byte-p 32 i)
       ;; check that it is correctly sign-extended:
       (equal (acl2::slice 31 8 i)
              (acl2::repeatbit 24 (acl2::getbit 7 i)))))

;; Tests of java-byte-as-int-p:
(assert-event (acl2::java-byte-as-int-p 0))
(assert-event (acl2::java-byte-as-int-p 127))
(assert-event (not (acl2::java-byte-as-int-p 128)))
(assert-event (acl2::java-byte-as-int-p (acl2::bvchop 32 -1)))
(assert-event (acl2::java-byte-as-int-p (acl2::bvchop 32 -128)))
(assert-event (not (acl2::java-byte-as-int-p (acl2::bvchop 32 -129))))

;; A short represented as part of a 32-bit int
(defund acl2::java-short-as-int-p (i)
  (declare (xargs :guard t))
  (and (unsigned-byte-p 32 i)
       ;; check that it is correctly sign-extended:
       (equal (acl2::slice 31 16 i)
              (acl2::repeatbit 16 (acl2::getbit 15 i)))))

;; Tests of java-short-as-int-p:
(assert-event (acl2::java-short-as-int-p 0))
(assert-event (acl2::java-short-as-int-p 32767))
(assert-event (not (acl2::java-short-as-int-p 32768)))
(assert-event (acl2::java-short-as-int-p (acl2::bvchop 32 -1)))
(assert-event (acl2::java-short-as-int-p (acl2::bvchop 32 -32768)))
(assert-event (not (acl2::java-short-as-int-p (acl2::bvchop 32 -32769))))

;; A char represented as part of a 32-bit int
;; TODO: Add tests
 ;; implies that it is correctly zero-extended
(defund acl2::java-char-as-int-p (i)
  (declare (xargs :guard t))
  (unsigned-byte-p 16 i))

;add a backchain limit (but Axe doesn't support them yet)?
(defthm not-equal-nil-when-java-byte-as-int-p
  (implies (acl2::java-byte-as-int-p x)
           (not (equal nil x))))

;add a backchain limit (but Axe doesn't support them yet)?
(defthm not-equal-nil-when-java-boolean-as-int-p
  (implies (acl2::java-boolean-as-int-p x)
           (not (equal nil x))))

;add a backchain limit (but Axe doesn't support them yet)?
(defthm not-equal-nil-when-java-char-as-int-p
  (implies (acl2::java-char-as-int-p x)
           (not (equal nil x))))

;add a backchain limit (but Axe doesn't support them yet)?
(defthm not-equal-nil-when-java-short-as-int-p
  (implies (acl2::java-short-as-int-p x)
           (not (equal nil x))))
