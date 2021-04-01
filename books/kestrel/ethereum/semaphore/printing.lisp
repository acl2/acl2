; Set up readable names and printing for prime field values
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZKSEMAPHORE")

(include-book "kestrel/prime-fields/printing" :dir :system)
(include-book "baby-jubjub-prime")

;; Refrains from handling 256 and below:
(make-event `(progn ,@(pfield::add-evisc-tuples-for-powers-of-2 35 9 *baby-jubjub-prime* "ZKSEMAPHORE")))

(make-event `(progn ,@(pfield::add-evisc-tuples-for-negated-powers-of-2 33 *baby-jubjub-prime* "ZKSEMAPHORE")))

(make-event `(progn ,@(pfield::add-evisc-tuples-for-inverse-powers-of-2 33 *baby-jubjub-prime* "ZKSEMAPHORE")))

(make-event `(progn ,@(pfield::add-evisc-tuples-for-negated-inverse-powers-of-2 32 *baby-jubjub-prime* "ZKSEMAPHORE")))



;; Special case for -1:
;; Note that the name acl2::*-1* is already in use (for a quoted thing)
(defconst acl2::*minus1* (- *baby-jubjub-prime* 1))
(table acl2::evisc-table acl2::*minus1* "#.acl2::*minus1*")
