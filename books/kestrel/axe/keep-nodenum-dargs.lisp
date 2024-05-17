; Keep only atoms (e.g., nodenums) in a list
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

(include-book "darg-listp")

;; Keep the nodenums from a list of nodenums and quoteps
(defund keep-nodenum-dargs (dargs)
  (declare (xargs :guard (darg-listp dargs)))
  (if (endp dargs)
      nil
    (let ((item (first dargs)))
      (if (atom item)
          (cons item (keep-nodenum-dargs (cdr dargs)))
        (keep-nodenum-dargs (cdr dargs))))))

(defthm nat-listp-of-keep-nodenum-dargs
  (implies (darg-listp dargs)
           (nat-listp (keep-nodenum-dargs dargs)))
  :hints (("Goal" :in-theory (enable keep-nodenum-dargs))))
