; Clearing a key in an alist
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defund clear-key (key alist)
  (declare (xargs :guard (alistp alist)))
  (if (endp alist)
      nil
    (if (equal key (caar alist))
        (clear-key key (cdr alist))
      (cons (car alist)
            (clear-key key (cdr alist))))))

(defthm alistp-of-clear-key
  (implies (alistp alist)
           (alistp (clear-key key alist)))
  :hints (("Goal" :in-theory (enable clear-key))))
