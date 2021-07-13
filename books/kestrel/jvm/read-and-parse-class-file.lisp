; A tool to read and parse a Java .class file
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/file-io-light/read-file-into-byte-list" :dir :system)
(include-book "class-file-parser")
(include-book "kestrel/utilities/file-existsp" :dir :system)
(include-book "kestrel/utilities/include-book-dir-dollar" :dir :system)
(local (include-book "kestrel/bv-lists/unsigned-byte-listp" :dir :system))
(local (include-book "kestrel/utilities/state" :dir :system))

(local (in-theory (enable all-unsigned-byte-p-when-unsigned-byte-listp)))

(local (in-theory (disable w boundp-global)))

;; Returns (mv erp class-name class-info field-defconsts state constant-pool).
(defund read-and-parse-class-file (class-file error-if-doesnt-existp state constant-pool)
  (declare (xargs :guard (stringp class-file)
                  :stobjs (state constant-pool)))
  (b* (((mv existsp state) ; consider skipping this step?
        (file-existsp class-file state))
       ((when (not existsp))
        (and error-if-doesnt-existp (er hard? 'read-and-parse-class-file "File does not exist: ~x0." class-file))
        (mv :file-does-not-exist nil nil nil state constant-pool))
       ((mv erp bytes state)
        (read-file-into-byte-list class-file state))
       ((when erp)
        (prog2$ (er hard? 'read-and-parse-class-file "Failed to read from file ~x0.  Result: ~x1." class-file bytes)
                (mv erp nil nil nil state constant-pool)))
       ;; Parse the bytes read:
       ((mv erp class-name class-info field-defconsts constant-pool)
        (parse-class-file-bytes bytes constant-pool))
       ((when erp) (mv erp nil nil nil state constant-pool)))
    (mv (erp-nil) class-name class-info field-defconsts state constant-pool)))

(defthm class-namep-of-mv-nth-1-of-read-and-parse-class-file
  (implies (not (mv-nth 0 (read-and-parse-class-file class-file error-if-doesnt-existp state constant-pool)))
           (jvm::class-namep (mv-nth 1 (read-and-parse-class-file class-file error-if-doesnt-existp state constant-pool))))
  :hints (("Goal" :in-theory (enable read-and-parse-class-file))))

(defthm class-infop0-of-mv-nth-2-of-read-and-parse-class-file
  (implies (not (mv-nth 0 (read-and-parse-class-file class-file error-if-doesnt-existp state constant-pool)))
           (jvm::class-infop0 (mv-nth 2 (read-and-parse-class-file class-file error-if-doesnt-existp state constant-pool))))
  :hints (("Goal" :in-theory (enable read-and-parse-class-file))))

(defthm class-infop-of-mv-nth-2-of-read-and-parse-class-file
  (implies (not (mv-nth 0 (read-and-parse-class-file class-file error-if-doesnt-existp state constant-pool)))
           (jvm::class-infop (mv-nth 2 (read-and-parse-class-file class-file error-if-doesnt-existp state constant-pool))
                             (mv-nth 1 (read-and-parse-class-file class-file error-if-doesnt-existp state constant-pool))))
  :hints (("Goal" :in-theory (enable read-and-parse-class-file))))

(defthm true-listp-of-mv-nth-3-of-read-and-parse-class-file
  (implies (not (mv-nth 0 (read-and-parse-class-file class-file error-if-doesnt-existp state constant-pool)))
           (true-listp (mv-nth 3 (read-and-parse-class-file class-file error-if-doesnt-existp state constant-pool))))
  :hints (("Goal" :in-theory (enable read-and-parse-class-file))))

;; Returns (mv erp class-name class-info field-defconsts state constant-pool).  Reads from either the directory in
;; which ACL2 was started (if DIR is nil), or from the directory associated
;; with DIR (if non-nil) by a previous call of add-include-book-dir.
(defund read-and-parse-class-file-with-dir (class-file
                                            dir ; nil, or something added by add-include-book-dir, such as :kestrel-acl2
                                            error-if-doesnt-existp
                                            state
                                            constant-pool)
  (declare (xargs :stobjs (state constant-pool)
                  :guard (and (stringp class-file)
                              (or (null dir)
                                  (keywordp dir))
                              (booleanp error-if-doesnt-existp))))
  (b* ((directory (if dir
                      (include-book-dir$ dir state)
                    "./"))
       ((when (not (stringp directory)))
        (mv `(:bad-include-book-dir ,directory) nil nil nil state constant-pool))
       (class-file (concatenate 'string directory class-file)))
    (read-and-parse-class-file class-file error-if-doesnt-existp state constant-pool)))

(defthm class-namep-of-mv-nth-1-of-read-and-parse-class-file-with-dir
  (implies (not (mv-nth 0 (read-and-parse-class-file-with-dir class-file dir error-if-doesnt-existp state constant-pool)))
           (jvm::class-namep (mv-nth 1 (read-and-parse-class-file-with-dir class-file dir error-if-doesnt-existp state constant-pool))))
  :hints (("Goal" :in-theory (enable read-and-parse-class-file-with-dir))))

(defthm class-infop0-of-mv-nth-2-of-read-and-parse-class-file-with-dir
  (implies (not (mv-nth 0 (read-and-parse-class-file-with-dir class-file dir error-if-doesnt-existp state constant-pool)))
           (jvm::class-infop0 (mv-nth 2 (read-and-parse-class-file-with-dir class-file dir error-if-doesnt-existp state constant-pool))))
  :hints (("Goal" :in-theory (enable read-and-parse-class-file-with-dir))))

(defthm class-infop-of-mv-nth-2-of-read-and-parse-class-file-with-dir
  (implies (not (mv-nth 0 (read-and-parse-class-file-with-dir class-file dir error-if-doesnt-existp state constant-pool)))
           (jvm::class-infop (mv-nth 2 (read-and-parse-class-file-with-dir class-file dir error-if-doesnt-existp state constant-pool))
                             (mv-nth 1 (read-and-parse-class-file-with-dir class-file dir error-if-doesnt-existp state constant-pool))))
  :hints (("Goal" :in-theory (enable read-and-parse-class-file-with-dir))))

(defthm true-listp-of-mv-nth-3-of-read-and-parse-class-file-with-dir
  (implies (not (mv-nth 0 (read-and-parse-class-file-with-dir class-file dir error-if-doesnt-existp state constant-pool)))
           (true-listp (mv-nth 3 (read-and-parse-class-file-with-dir class-file dir error-if-doesnt-existp state constant-pool))))
  :hints (("Goal" :in-theory (enable read-and-parse-class-file-with-dir))))

;; ;;;
;; ;;; show-raw-parsed-class
;; ;;;

;; (defund show-raw-parsed-class-fn (class-file
;;                                   dir ; nil, or something added by add-include-book-dir, such as :kestrel-acl2
;;                                   state
;;                                   constant-pool)
;;   (declare (xargs :stobjs (state constant-pool)
;;                   :guard (and (stringp class-file)
;;                               (or (null dir)
;;                                   (keywordp dir)))))
;;   (b* (((mv erp raw-parsed-class state constant-pool) (read-and-parse-class-file-with-dir class-file dir t state constant-pool))
;;        ((when erp) (mv erp nil state constant-pool))
;;        (class-name (lookup-eq :this_class raw-parsed-class)))
;;     (progn$ (cw "Raw info for class ~s0:~%" class-name)
;;             (cw "~X01" raw-parsed-class nil)
;;             (mv (erp-nil) nil state constant-pool))))

;; ;; Show the raw parsed class.
;; (defmacro show-raw-parsed-class (class-file
;;                                  &key
;;                                  (dir 'nil))
;;   `(show-raw-parsed-class-fn ,class-file ',dir state constant-pool))

;;;
;;; show-class-info
;;;

(defund show-class-info-fn (class-file
                            dir ; nil, or something added by add-include-book-dir, such as :kestrel-acl2
                            state
                            constant-pool)
  (declare (xargs :stobjs (state constant-pool)
                  :guard (and (stringp class-file)
                              (or (null dir)
                                  (keywordp dir)))))
  (b* (((mv erp class-name class-info
            & ; field-defconsts
            state constant-pool) (read-and-parse-class-file-with-dir class-file dir t state constant-pool))
       ((when erp) (mv erp nil state constant-pool)))
    (progn$ (cw "Info for class ~s0:~%" class-name)
            (cw "~X01" class-info nil)
            (mv (erp-nil) nil state constant-pool))))

;; Show class-info for the given class
(defmacro show-class-info (class-file
                           &key
                           (dir 'nil))
  `(show-class-info-fn ,class-file ',dir state constant-pool))
