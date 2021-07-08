; Basic definitions about arrays.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "heap0")

;In the JVM, a one-dimensional array occupies a single object in the heap.

;fixme use special-data?
;fixme what if there is a class called "ARRAY"? use :array?
;rename since this is not a pair?!
(defmacro array-contents-pair ()
  ''("ARRAY" "contents" . "dummy-descriptor"))

(defthm heap-object-keyp-of-array-contents-pair
  (heap-object-keyp (array-contents-pair)))

;use this more?  make it a macro?
(defun array-contents (ref heap)
  (declare (xargs :guard (and (addressp ref)
                              (jvm::heapp heap))))
  (get-field ref (array-contents-pair) heap))

;;;
;;; array-object-fields
;;;

;; Only these fields should affect array-refp.  The length is not a field but
;; is computed from the contents.
(defun acl2::array-object-fields ()
  (declare (xargs :guard t))
  (list (acl2::class-pair)
        (acl2::array-contents-pair)))

(defthm all-heap-object-keyp-of-array-object-fields
  (acl2::all-heap-object-keyp (acl2::array-object-fields)))

;;;
;;; array-length
;;;

;Note: The JVM spec says "Once an array object is created, its length never changes."
;we are no longer storing the array's length field separately...
;should this be a function rather than a macro (would need to be disabled, since rules are written in terms of it)
;call array-contents?
;calling this when we already have the contents would cause the get-field to be redone..
(defmacro array-length (ref heap)
  `(len (get-field ,ref (array-contents-pair) ,heap)))
