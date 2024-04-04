; Apply strip-cars to every element of a list
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-alistp") ; todo: use alist-listp instead?

(defund map-strip-cars (alists)
  (declare (xargs :guard (all-alistp alists)))  ; todo: use alist-listp instead?
  (if (atom alists) ; (endp alists)
      nil
    (cons (strip-cars (first alists))
          (map-strip-cars (rest alists)))))
