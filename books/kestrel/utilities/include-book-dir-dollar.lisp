; A wrapper for include-book-dir.
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "state"))

(in-theory (disable include-book-dir))

;; from the guard of include-book-dir.
;; TODO: Change include-book-dir to call this?
(defund include-book-dir-guard (dir state)
  (declare (xargs :stobjs state))
  (and
   (symbolp dir) ; could drop
   (or
    (not (raw-include-book-dir-p state))
    (and
     (symbol-alistp (f-get-global 'raw-include-book-dir!-alist
                                  state))
     (symbol-alistp (f-get-global 'raw-include-book-dir-alist
                                  state))))
   (let
       ((wrld (w state)))
     (and
      (alistp (table-alist 'acl2-defaults-table wrld))
      (alistp (cdr (assoc-eq :include-book-dir-alist
                             (table-alist 'acl2-defaults-table
                                          wrld))))
      (alistp (table-alist 'include-book-dir!-table
                           wrld))))))

;; Better guard, always returns a string
(defund include-book-dir$ (dir state)
  (declare (xargs :guard (keywordp dir)
                  :stobjs state
                  :guard-hints (("Goal" :in-theory (enable include-book-dir-guard)))))
  (if (not (include-book-dir-guard dir state))
      (prog2$ (er hard? 'include-book-dir$ "include-book-dir-guard is violated for ~x0." dir)
              "")
    (let ((res (include-book-dir dir state)))
      (if (not (stringp res))
          (prog2$ (er hard? 'include-book-dir$ "Include-book-dir returns the non-string ~x0." res)
                  "")
        res))))

(defthm stringp-of-include-book-dir$
  (stringp (include-book-dir$ dir state))
  :hints (("Goal" :in-theory (enable include-book-dir$))))
