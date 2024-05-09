; Gathering a list of all the functions in a world
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Helper function for all-functions-in-world.
(defund all-functions-in-world-aux (wrld acc)
  (declare (xargs :guard (and (plist-worldp wrld)
                              (true-listp acc))))
  (if (endp wrld)
      (remove-duplicates-equal acc) ;slow?  consider a version of remove-duplicates that uses fast alists or property worlds?
    (let* ((triple (first wrld))
           (prop (cadr triple)))
      (if (eq 'formals prop)
          (all-functions-in-world-aux (rest wrld) (cons (car triple) acc))
        (all-functions-in-world-aux (rest wrld) acc)))))

(defthm symbol-listp-of-all-functions-in-world-aux
  (implies (and (symbol-listp acc)
                (plist-worldp wrld))
           (symbol-listp (all-functions-in-world-aux wrld acc)))
  :hints (("Goal" :in-theory (enable all-functions-in-world-aux))))

;; Return a list of all functions currently present in WRLD.
;; Example usage: (all-functions-in-world (w state))
(defund all-functions-in-world (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (all-functions-in-world-aux wrld nil))

(defthm symbol-listp-of-all-functions-in-world
  (implies (plist-worldp wrld)
           (symbol-listp (all-functions-in-world wrld)))
  :hints (("Goal" :in-theory (enable all-functions-in-world))))
