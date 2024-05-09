; The global-class-alist structure
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

;; The global-class-alist maps class names to class-infops.  This is different
;; from a JVM class-table structure, which is a record.

;; Registers a class in the global-class-alist.
;; class-name should be a string, and class-info should be a form that evaluates to a class-infop.
(defmacro add-to-global-class-alist (class-name class-info)
  `(table acl2::global-class-table ,class-name ,class-info))

;; Returns the global-class-table as an alist.
(defund global-class-alist (state)
  (declare (xargs :stobjs (state)))
  (table-alist 'acl2::global-class-table (w state)))
