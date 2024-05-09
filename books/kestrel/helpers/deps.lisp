; Utilities for dealing with dependencies among community books
;
; Copyright (C) 2022-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/file-io-light/read-object-from-file" :dir :system)
(include-book "kestrel/strings-light/string-ends-withp" :dir :system)
(include-book "kestrel/strings-light/strip-suffix-from-strings" :dir :system)
(include-book "kestrel/utilities/extend-pathname-dollar" :dir :system)
(include-book "kestrel/utilities/include-book-dir-dollar" :dir :system)
(local (include-book "kestrel/typed-lists-light/string-listp" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

;move?
(defund keep-strings-that-end-in (strs str acc)
  (declare (xargs :guard (and (string-listp strs)
                              (stringp str)
                              (string-listp acc))))
  (if (endp strs)
      (reverse acc)
    (let ((first-str (first strs)))
      (if (string-ends-withp first-str ".cert")
          (keep-strings-that-end-in (rest strs) str (cons first-str acc))
        (keep-strings-that-end-in (rest strs) str acc)))))

(defthm true-listp-of-keep-strings-that-end-in
  (implies (true-listp acc)
           (true-listp (keep-strings-that-end-in strs str acc)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable keep-strings-that-end-in))))

(defthm string-listp-of-keep-strings-that-end-in
  (implies (and (string-listp strs)
                (string-listp acc))
           (string-listp (keep-strings-that-end-in strs str acc)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable keep-strings-that-end-in))))

;; Reads the file build/Makefile-deps.lsp and returns its contents as an alist.  One entry in the alist is the :dependency-map.
;; Returns (mv erp deps-info state).
(defund community-book-deps (state)
  (declare (xargs :stobjs state
                  :mode :program ; todo
                  ))
  (mv-let (erp deps-info state)
    (read-object-from-file (extend-pathname$ (include-book-dir$ :system state) "build/Makefile-deps.lsp" state) state)
    (if erp
        (mv :failed-to-read-community-book-deps nil state)
      (if (not (alistp deps-info))
          (mv :bad-deps-info nil state)
        (mv nil           ; no error
            deps-info     ;(strip-cars dependency-map)
            state)))))

;; Returns (mv erp deps-map state).
;; TODO: The dep list of a given book may contain duplicates.
;; Books in this map may depend on other files, such as .acl2 files or even data files.
(defund raw-community-book-dependency-map (state)
  (declare (xargs :stobjs state
                  :mode :program ; todo
                  ))
  (mv-let (erp deps-info state)
    (community-book-deps state)
    (if erp
        (mv erp nil state)
      (let ((dependency-map (cdr (assoc-eq :dependency-map deps-info))))
        (if (not (alistp dependency-map))
            (mv :bad-deps-map nil state)
          (mv nil dependency-map state))))))

;; Extracts just the book dependencies, removes duplicates, and drops .cert extensions.
(defund clean-book-dependency-map (deps acc)
  (declare (xargs :guard (and (alistp deps)
                              ;; (string-list-listp (strip-cdrs deps))
                              (alistp acc))
                  :guard-hints (("Goal" :expand (strip-cdrs deps)))))
  (if (endp deps)
      (reverse acc)
    (let* ((pair (first deps))
           (book (car pair))
           (book (if (stringp book) book (prog2$ (er hard? 'clean-book-dependency-map "Bad book name: ~x0" book) "")))
           (all-deps (cdr pair))
           (clean-deps (if (string-listp all-deps)
                           ;; TODO: Why can duplicates even arise?
                           (strip-suffix-from-strings ".cert" (remove-duplicates-equal (keep-strings-that-end-in all-deps ".cert" nil)))
                         (er hard? 'clean-book-dependency-map "Bad deps: ~x0" all-deps))))
      (clean-book-dependency-map (rest deps)
                                 (acons (strip-suffix-from-string ".cert" book)
                                        clean-deps
                                        acc)))))

;; Returns (mv erp deps-map state).
(defund community-book-dependency-map (state)
  (declare (xargs :stobjs state
                  :mode :program ; todo
                  ))
  (mv-let (erp deps-map state)
    (raw-community-book-dependency-map state)
    (if erp
        (mv erp nil state)
      (mv nil (clean-book-dependency-map deps-map nil) state))))

(defun all-deps-of-books (books map ans)
  (declare (xargs :mode :program ;todo
                  ))
  (if (endp books)
      ans
    (let* ((book (first books))
           (deps (cdr (assoc-equal book map)))
           (new-deps (set-difference-equal deps ans)))
      (all-deps-of-books (append new-deps (rest books)) map (append new-deps ans)))))

;; Returns a list of all the books that BOOK depends on, according to books/build/Makefile-deps.lsp.
;; This includes books that come in via local include-books.
;; todo: consider sorting the result
(defun all-deps-of-community-book (book ; no suffix
                                   state)
  (declare (xargs :stobjs state
                  :mode :program ; todo
                  ))
  (mv-let (erp map state)
    (community-book-dependency-map state)
    (if erp
        (mv erp nil state)
      (mv nil (all-deps-of-books (list book) map nil) state))))

;; Example (all-deps-of-community-book "kestrel/lists-light/append" state)
