; A tool to read in a .jar file and register some or all of its classes
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/include-book-dir-dollar" :dir :system)
(include-book "kestrel/jvm/class-and-path-utils" :dir :system)
(include-book "kestrel/jvm/events-for-class" :dir :system)
(include-book "kestrel/jvm/class-file-parser" :dir :system)
(include-book "kestrel/utilities/redundancy" :dir :system)
(include-book "kestrel/strings-light/string-ends-withp" :dir :system)
(include-book "kestrel/strings-light/string-starts-withp" :dir :system)
(include-book "kestrel/zip/unzip" :dir :system)
(local (include-book "kestrel/typed-lists-light/string-listp" :dir :system))

(local (in-theory (disable string-listp ;prevent induction
                           )))

;; For each of the CLASS-NAMES, turns dots into slashes and adds .class at the end
(defund class-names-to-paths (class-names)
  (declare (xargs :guard (string-listp class-names)))
  (if (endp class-names)
      nil
    (cons (concatenate 'string (turn-dots-into-slashes (first class-names)) ".class")
          (class-names-to-paths (rest class-names)))))

(defthm string-listp-of-class-names-to-paths
  (implies (string-listp class-names)
           (string-listp (class-names-to-paths class-names)))
  :hints (("Goal" :in-theory (enable class-names-to-paths))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp events constant-pool count).
(defun events-for-classes-from-alist (alist ; maps paths to classes
                                      acc
                                      constant-pool ; stobj that makes class file parsing more efficient
                                      count)
  (declare (xargs :guard (and (alistp alist)
                              (string-listp (strip-cars alist))
                              (byte-list-listp (strip-cdrs alist))
                              (true-listp acc)
                              (natp count))
                  :stobjs constant-pool))
  (if (endp alist)
      (mv nil (reverse acc) constant-pool count)
    (b* ((entry (first alist))
         (path (car entry)) ; we ignore the actual path (get the class name from the class file)
         )
      (if (or (string-starts-withp path "META-INF/") ; I've seen module-info.class under META-INF/
              (not (string-ends-withp path ".class")))
          ;; Skip since not a .class file we want:
          (events-for-classes-from-alist (rest alist) acc constant-pool count)
        (b* ((bytes (cdr entry))
             ;; Parse the bytes read:
             ((mv erp class-name class-info field-defconsts constant-pool)
              (parse-class-file-bytes bytes constant-pool))
             ((when erp)
              (er hard? 'events-for-classes-from-alist "Error parsing classfile for ~x0." path)
              (mv erp nil constant-pool count))
             (events-for-class (events-for-class class-name
                                                 class-info
                                                 field-defconsts ; do we always want these?
                                                 )))
          (events-for-classes-from-alist (rest alist)
                                         (cons `(progn ,@events-for-class)
                                               acc)
                                         constant-pool
                                         (+ 1 count)))))))

(defthm true-listp-of-mv-nth-1-of-events-for-classes-from-alist
  (implies (true-listp acc)
           (true-listp (mv-nth 1 (events-for-classes-from-alist alist acc constant-pool count)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp event byte-array-stobj constant-pool state).
(defund read-jar-fn (jar-path dir class-names verbosep whole-form state byte-array-stobj constant-pool)
  (declare (xargs :guard (and (stringp jar-path)
                              (or (null dir)
                                  (keywordp dir))
                              (or (eq :all class-names)
                                  (string-listp class-names))
                              (booleanp verbosep)
                              (consp whole-form)
                              (symbolp (car whole-form)))
                  :stobjs (state byte-array-stobj constant-pool)))
  (b* (;; Check for redundancy:
       ((when (command-is-redundantp whole-form state))
        (mv (erp-nil) '(value-triple :invisible) state byte-array-stobj constant-pool))
       ;; Combine the JAR-PATH and the DIR to get the full path:
       ;; todo: factor out this pattern, which is also in read-and-parse-class-file-with-dir:
       (directory (if dir
                      (include-book-dir$ dir state)
                    "./"))
       ((when (not (stringp directory)))
        (er hard? 'read-jar-fn "Bad directory: ~x0." directory)
        (mv `(:bad-include-book-dir ,directory) nil state byte-array-stobj constant-pool))
       (jar-path (concatenate 'string directory jar-path))
       ;; Read the .jar:
       ((mv erp path-to-decompressed-bytes-alist byte-array-stobj state)
        (if (eq :all class-names)
            (unzip jar-path :all verbosep byte-array-stobj state)
          (let ((paths (class-names-to-paths class-names))) ; turns dots into slashes
            (unzip jar-path paths verbosep byte-array-stobj state))))
       ((when erp) (mv erp nil state byte-array-stobj constant-pool))
       ;; Parse each of the class files and create events to register it:
       ((mv erp events constant-pool count)
        (events-for-classes-from-alist path-to-decompressed-bytes-alist nil constant-pool 0))
       ((when erp) (mv erp nil state byte-array-stobj constant-pool))
       (- (cw "Read ~x0 classes from ~x1~%." count jar-path)))
    (mv nil ; no error
        `(progn ,@events
                ;; Record the fact that the containing book depends on this jar:
                (table acl2::depends-on-table ,jar-path t)
                ;; For redundancy checking (at least for now, the whole-form must be identical):
                (table read-jar-table ',whole-form t)
                (value-triple :invisible))
        state byte-array-stobj constant-pool)))

;; Read in a .jar file and register the given classes (or all classes if none
;; are explicitly listed).
(defmacro read-jar (&whole whole-form
                           jar-path
                           &key
                           (dir 'nil)
                           (classes ':all) ; names of classes (fully-qualified), or :all
                           (verbosep 'nil)
                           )
  `(make-event-quiet (read-jar-fn ,jar-path ,dir ',classes ,verbosep ',whole-form state byte-array-stobj constant-pool)))
