; Utilities to make variable names
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; todo: compare to new-var-names

(include-book "kestrel/utilities/pack" :dir :system)

;use pack?
(defund make-var-names-aux (base-symbol startnum endnum)
  (declare (xargs :guard (symbolp base-symbol)
                  :measure (nfix (+ 1 (- endnum startnum)))
                  ))
  (if (or (not (natp startnum))
          (not (natp endnum))
          (< endnum startnum))
      nil
    (cons (pack-in-package-of-symbol base-symbol base-symbol (nat-to-string startnum))
          (make-var-names-aux base-symbol (+ 1 startnum) endnum))))

(defthm pseudo-term-listp-of-make-var-names-aux
  (pseudo-term-listp (make-var-names-aux base-symbol startnum endnum))
  :hints (("Goal" :in-theory (enable make-var-names-aux))))

(defthm symbol-listp-of-make-var-names-aux
  (symbol-listp (make-var-names-aux base-symbol startnum endnum))
  :hints (("Goal" :in-theory (enable make-var-names-aux))))

;was called make-var-names
(defund make-var-names-x (namecount)
  (declare (xargs ;:mode :program
                  :guard t))
  (reverse (make-var-names-aux 'x 1 namecount)))

(defund make-var-names (count base-name)
  (declare (xargs ;:mode :program
                  :guard (and (natp count)
                              (symbolp base-name))))
  (reverse (make-var-names-aux base-name 0 (+ -1 count))))
