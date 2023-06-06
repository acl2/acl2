; HTCLIENT -- HTTP/HTTPS Client Library
;
; Copyright (C) 2022-2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)
; Supporting Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HTCLIENT")

;; This book is just a lighter-weight variant of post-logic.lisp.

;(include-book "std/util/define" :dir :system)
;(include-book "std/basic/defs" :dir :system)
;(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This will be replaced by an include-book later.
(local
 (defthm state-p1-of-read-acl2-oracle
   (implies (state-p1 state)
            (state-p1 (mv-nth 2 (read-acl2-oracle state))))
   :hints (("Goal" :in-theory (enable read-acl2-oracle)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Provably equivalent to the function post in post.lisp.
(defun post-light (url data state kwds)
  (declare (xargs :guard (and (stringp url) (alistp data) (doublet-listp kwds))
                  :stobjs state)
           (ignore url data kwds))
  (prog2$ (er hard? 'post-light "Raw Lisp definition not installed?")
          (mv-let (err1 val1 state)
            (read-acl2-oracle state)
            (declare (ignore err1))
            (mv-let (err2 val2 state)
              (read-acl2-oracle state)
              (declare (ignore err2))
              (if val1
                  (mv val1 "" state)
                (mv nil (if (stringp val2) val2 "") state))))))
