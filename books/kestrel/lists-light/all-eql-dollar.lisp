; A variant of all-equal$ that uses eql as the test.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; A variant of all-equal$ that uses eql as the test.
(defund all-eql$ (x lst)
  (declare (xargs :guard (and (true-listp lst)
                              (eqlablep x))))
  (if (endp lst)
      t
    (and (eql x (first lst))
         (all-eql$ x (rest lst)))))

;; todo: rewrite to all-equal$
