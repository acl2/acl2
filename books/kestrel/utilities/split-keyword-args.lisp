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
;; should be a keyword-value-list.
;; Returns (mv non-keyword-args keyword-value-list).
;; ex: (split-keyword-args '(x 3 y z :foo 4 :bar 5))
;; See also partition-rest-and-keyword-args.
(defun split-keyword-args (args)
  (declare (xargs :guard (true-listp args)))
  (if (endp args)
      (mv nil nil)
    (if (keywordp (first args))
        (mv nil args)
      (mv-let (rest-args rest-keyword-value-list)
        (split-keyword-args (rest args))
        (mv (cons (first args) rest-args)
            rest-keyword-value-list)))))
