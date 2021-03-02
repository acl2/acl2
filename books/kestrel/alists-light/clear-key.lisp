; Clearing a key in an alist
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defun clear-key (key alist)
  (declare (xargs :guard (alistp alist)))
  (if (endp alist)
      nil
    (if (equal key (caar alist))
        (clear-key key (cdr alist))
      (cons (car alist)
            (clear-key key (cdr alist))))))
