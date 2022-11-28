; Replacing an arg that corresponds to a formal
;
; Copyright (C) 2014-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Put in NEW-ARG for the member of ARGS that corresponds to FORMAL in FORMALS.
(defund replace-corresponding-arg (new-arg args formal formals)
  (declare (xargs :guard (and (true-listp args)
                              (symbolp formal)
                              (symbol-listp formals))))

  (if (endp args)
      nil ;error?
    (if (eq formal (first formals))
        ;; todo: don't recur in this case?
        (cons new-arg (replace-corresponding-arg new-arg (rest args) formal (rest formals)))
      (cons (first args)
            (replace-corresponding-arg new-arg (rest args) formal (rest formals))))))

(defthm pseudo-term-listp-of-replace-corresponding-arg
  (implies (and (pseudo-term-listp args)
                (pseudo-termp new-arg))
           (pseudo-term-listp (replace-corresponding-arg new-arg args formal formals)))
  :hints (("Goal" :in-theory (enable replace-corresponding-arg))))

(defthm len-of-replace-corresponding-arg
  (equal (len (replace-corresponding-arg new-arg args formal formals))
         (len args))
  :hints (("Goal" :in-theory (enable replace-corresponding-arg))))
