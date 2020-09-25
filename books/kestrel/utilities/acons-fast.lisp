; A macro version of acons
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This is faster in my tests than acons (since acons is a function).  (Also,
;; this does not have a guard requiring (alistp alist), whereas acons does.)
(defmacro acons-fast (key datum alist)
  `(cons (cons ,key ,datum) ,alist))
