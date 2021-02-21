; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This very basic variant of the test hons.lisp also succeeds, both for
; certify-book and subsequent include-book, both before and after the changes
; to early loading of compiled files in mid-February, 2021.  However, 

; Below, "hl" comes from the filename.

(in-package "ACL2")

(local (defun hl-fn (x) x))

(defconst *hl1* (hons 3 4))

(make-event `(defconst *hl2* ',(hons 3 4)))

; After including the book, the second error below occurred before February
; 2021.  If however we include these events in the book, that problem goes away
; -- maybe because of sharing of *hl1* and *hl2* in the certificate, but I
; haven't thought that through.

#||
(defttag :ttag-test)

(progn!
 (set-raw-mode t)
 (if (hl-hspace-honsp-wrapper *hl1*)
     (cw "Success for *hl1*.~%")
   (error "Not a hons: *hl1*"))
 (if (hl-hspace-honsp-wrapper *hl2*)
     (cw "Success for *hl2*.~%")
   (error "Not a hons: *hl2*")))
||#

; Here is what I think was happening before the changes in mid-February 2021.

; I think the "oldp" case of install-for-add-trip-hcomp-build saved us when
; there is no local event, because of the lack of rolling back the world during
; the include-book phase of certify-book, which caused the constants not to be
; qualified.  With the local event, that rolling back took place and hence
; *bar* was qualified, so the early load of the compiled file at
; install-for-add-trip-include-book used the defconst event for the value from
; the compiled file, which wasn't a hons, rather than the hash-table value.
