; Representations of Java values as bit-vectors.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;TODO: Switch to java package and remove java- from the name?

;TODO: Or should these recognize the signed integer ranges, with separate functions jvm-bytep, etc. for the bit vectors?

;TODO: Perhaps someday use BVP here instead of UNSIGNED-BYTE-P

(include-book "kestrel/bv/unsigned-byte-p" :dir :system)

;; Note that some of these values are signed, but here they are encoded into
;; bit-vectors, which are always unsigned.

;; Note that in the JVM itself, values shorter than ints are often stored in
;; int fields.

;; A boolean is a single 0 or 1 (we could consider making this be either true
;; or false, instead of a number).  See JVM spec section 2.3.4 (The boolean Type).
(defund java-booleanp (i)
  (declare (xargs :guard t))
  (unsigned-byte-p 1 i))

;; A byte is 8 bits
(defund java-bytep (i)
  (declare (xargs :guard t))
  (unsigned-byte-p 8 i))

;; A short is a 16-bits
(defund java-shortp (i)
  (declare (xargs :guard t))
  (unsigned-byte-p 16 i))

;; A char is 16-bits
(defund java-charp (i)
  (declare (xargs :guard t))
  (unsigned-byte-p 16 i))

;; An int is a 32-bits
(defund java-intp (i)
  (declare (xargs :guard t))
  (unsigned-byte-p 32 i))

;; A long is 64-bits
(defund java-longp (l)
  (declare (xargs :guard t))
  (unsigned-byte-p 64 l))
