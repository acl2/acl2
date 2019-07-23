; BV Library: Definition of bvcat
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; For theorems about bvcat, see bvcat.lisp.

(include-book "bvchop-def")
(include-book "logapp-def")
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/expt"))
(local (include-book "../arithmetic-light/numerator"))

(defund bvcat (highsize highval lowsize lowval)
  (declare (type integer highval lowval)
           (type (integer 0 *) highsize lowsize))
  (logapp lowsize lowval (bvchop highsize highval)))

(defthm natp-of-bvcat-type
  (natp (bvcat highsize highval lowsize lowval))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable bvcat natp))))

;; natp-of-bvcat-type is at least as good
(in-theory (disable (:type-prescription bvcat)))
