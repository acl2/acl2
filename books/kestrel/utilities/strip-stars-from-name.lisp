; A utility to strip the stars from the name of a constant
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))

;dup in unroll-java-code
(defun strip-stars-from-name (name)
  (declare (xargs :guard (symbolp name)))
  (b* ((str (symbol-name name))
       (chars (coerce str 'list))
       ((when (not (and (<= 2 (len chars))
                        (equal #\* (first chars))
                        (equal #\* (car (last chars))))))
        (er hard? 'strip-stars-from-name "~x0 does not start and end with stars." name))
       (chars (cdr (butlast chars 1)))
       (str (coerce chars 'string))
       (result (intern-in-package-of-symbol str name)))
    result))
