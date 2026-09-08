; Purely functional double-ended queues (deques), following Okasaki.
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Aakash Koneru

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/data/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "DEQUE"
  (union-eq '(defxdoc+
              lnfix
              reverse-list)
            ;; EMPTYP is a generic operation name that the deque wants to own.
            (set-difference-eq *std-pkg-symbols*
                               #!STD
                               '(emptyp))))
