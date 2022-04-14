; A utility to separate args
;
; Copyright (C) 2016-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Split ARGS into an initial portion of non-keywords, and the rest, which
;; should be a keyword-alist.
;; Returns (mv non-keyword-args keyword-alist).
;; ex: (split-keyword-args '(x 3 y z :foo 4 :bar 5))
(defun split-keyword-args (args)
  (declare (xargs :guard (true-listp args)))
  (if (endp args)
      (mv nil nil)
    (if (keywordp (first args))
        (mv nil args)
      (mv-let (rest-args rest-keyword-alist)
        (split-keyword-args (rest args))
        (mv (cons (first args) rest-args)
            rest-keyword-alist)))))
