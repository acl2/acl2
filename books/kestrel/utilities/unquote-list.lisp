; Unquoting a list of quoteps
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "quote") ; for all-myquotep, todo: switch to quote-listp

(defund unquote-list (lst)
  (declare (xargs :guard (and (true-listp lst)
                              (all-myquotep lst))))
  (cond ((not (consp lst)) nil)
        (t (cons (unquote (car lst))
                 (unquote-list (cdr lst))))))
