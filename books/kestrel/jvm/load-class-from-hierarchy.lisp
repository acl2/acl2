; A variant of load-class
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "load-class")
(include-book "class-and-path-utils")

;Returns (mv erp event state constant-pool)
(defun load-class-from-hierarchy-fn (fully-qualified-class-name
                                     root ;no trailing slash
                                     whole-form
                                     state
                                     constant-pool)
  (declare (xargs :guard (and (jvm::class-namep fully-qualified-class-name)
                              (stringp root)
                              (consp whole-form)
                              (symbolp (car whole-form)))
                  :stobjs (state constant-pool)))
  (b* (((when (command-is-redundantp whole-form state))
        (mv (erp-nil) '(value-triple :invisible) state constant-pool))
       (class-file (concatenate 'string
                                root
                                "/"
                                (path-of-class-file-within-dir fully-qualified-class-name)))
       ((mv erp class-name class-info field-defconsts state constant-pool)
        (read-and-parse-class-file class-file t state constant-pool))
       ((when erp)
        (er hard? 'load-class-from-hierarchy-fn "Error reading or parsing ~x0: ~x1" class-file erp)
        (mv erp nil state constant-pool))
       (events (events-for-class class-name class-info field-defconsts)))
    (mv (erp-nil)
        `(progn ,@events
                ;; Record the fact that the containing book depends on this class:
                (table acl2::depends-on-table ,class-file t)
                ;; For redundancy checking (at least for now, the whole-form must be identical):
                (table load-class-table ',whole-form t)
                ;; Print the name of the class constant:
                (value-triple ',(class-info-constant-name class-name)))
        state
        constant-pool)))

;; Submit events to load a Java class, including a defconst containing the
;; parsed contents of the class, an event to add it to the global-class-table,
;; etc. ROOT should contain class files organized in the usual way, with one
;; directory level for each part of each fully qualified name.
(defmacro load-class-from-hierarchy (&whole whole-form
                                            fully-qualified-class-name
                                            &key
                                            (root '"."))
  `(make-event-quiet (load-class-from-hierarchy-fn ,fully-qualified-class-name
                                                   ,root
                                                   ',whole-form
                                                   state
                                                   constant-pool)))
