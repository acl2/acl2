; A tool to read in a Java class and create ACL2 events representing it
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book defines a utility, read-class, to read in a Java class, create
;; ACL2 events representing its contents, and register it as a known class
;; whose contents should be assumed in subsequent Axe lifter calls.

;; Note that this utility is not really related to the JVM's notion of "class
;; loading".  TODO: So consider renaming this utility.

;; NOTE: Users of read-class may want to add DEPENDS-ON forms to their books to
;; inform cert.pl about the dependencies on the loaded class files (see :doc
;; raw-lisp-and-other-dependencies).  Calling (depends-on-lines) after calling
;; read-class will print appropriate lines to be copied into your book.

;; TODO: Rename this book to read-class.lisp

(include-book "read-and-parse-class-file")
(include-book "events-for-class")
(include-book "kestrel/utilities/mydefconst" :dir :system)
(include-book "kestrel/utilities/make-event-quiet" :dir :system)
(include-book "kestrel/utilities/depends-on-table" :dir :system)
(include-book "kestrel/utilities/redundancy" :dir :system)
(local (include-book "kestrel/bv-lists/unsigned-byte-listp" :dir :system))

;; Returns (mv erp event state constant-pool).  Helper function for read-class.
;; Uses the name stored in the class file, ignoring the filename
(defun read-class-fn (class-file dir whole-form state constant-pool)
  (declare (xargs :stobjs (state constant-pool)
                  :guard (and (stringp class-file)
                              (or (null dir)
                                  (keywordp dir))
                              (consp whole-form)
                              (symbolp (car whole-form)))))
  (b* (((when (command-is-redundantp whole-form state))
        (mv (erp-nil) '(value-triple :invisible) state constant-pool))
       ((mv erp class-name class-info field-defconsts state constant-pool)
        (read-and-parse-class-file-with-dir class-file dir t state constant-pool))
       ((when erp)
        (er hard? 'read-class-fn "Error reading or parsing ~x0: ~x1" class-file erp)
        (mv erp nil state constant-pool)))
    (mv (erp-nil)
        `(progn ,@(events-for-class class-name class-info field-defconsts)
                ;; Record the fact that the containing book depends on this class:
                (table acl2::depends-on-table ,class-file t)
                ;; For redundancy checking (at least for now, the whole-form must be identical):
                (table read-class-table ',whole-form t)
                ;; Print the name of the class constant:
                (value-triple ',(class-info-constant-name class-name)))
        state
        constant-pool)))

;; Reads in the indicated Java bytecode .class file and creates a defconst
;; containing the parsed contents of the class.  Also adds the class to the
;; global-class-alist.
(defmacro read-class (&whole whole-form
                             class-file
                             &key
                             (dir 'nil))
  `(make-event-quiet (read-class-fn ,class-file ',dir ',whole-form state constant-pool)))
