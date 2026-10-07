; The global-class-alist structure
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "classes")

;; The global-class-alist maps class names to class-infops.  This is different
;; from a JVM class-table structure, which is a record.

(defun add-to-global-class-alist-fn (class-name class-info)
  (declare (xargs :guard t ))
  (if (not (jvm::class-namep class-name))
      (er hard? 'add-to-global-class-alist-fn "Bad class name: ~x0." class-name)
    (if (not (jvm::class-infop class-info class-name))
        (er hard? 'add-to-global-class-alist-fn "Bad class info: ~x0." class-info)
      `(table acl2::global-class-table ,class-name ',class-info))))

;; Registers a class in the global-class-alist.
;; CLASS-NAME should evaluate to a string.
;; CLASS-INFO should evaluate to a class-info.
(defmacro add-to-global-class-alist (class-name class-info)
  `(make-event (add-to-global-class-alist-fn ,class-name ,class-info)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns the global-class-table as an alist.
(defund global-class-alist (state)
  (declare (xargs :stobjs state))
  (table-alist 'acl2::global-class-table (w state)))
