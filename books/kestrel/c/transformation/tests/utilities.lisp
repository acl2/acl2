; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/defines" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define assert-file-contents-fn
  (file content state)
  (b* (((unless (stringp file))
        (mv (msg "~x0 must be a string." file) nil state))
       (actual-content (read-file-into-string file))
       (state (increment-file-clock state)))
    (value `(assert-event
              (equal
                ,actual-content
                ,content)))))

(defmacro assert-file-contents
  (&key file content)
  `(make-event (assert-file-contents-fn ',file ',content state)))
