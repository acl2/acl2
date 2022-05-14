; Utilities for dealing with dependencies among community books
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/file-io-light/read-object-from-file" :dir :system)
(include-book "kestrel/strings-light/string-ends-inp" :dir :system)

;move?
(defund keep-strings-that-end-in (strs str acc)
  (declare (xargs :guard (and (string-listp strs)
                              (stringp str)
                              (string-listp acc))))
  (if (endp strs)
      (reverse acc)
    (let ((first-str (first strs)))
      (if (string-ends-inp first-str ".cert")
          (keep-strings-that-end-in (rest strs) str (cons first-str acc))
        (keep-strings-that-end-in (rest strs) str acc)))))

(defthm true-listp-of-keep-strings-that-end-in
  (implies (true-listp acc)
           (true-listp (keep-strings-that-end-in strs str acc)))
  :hints (("Goal" :in-theory (enable keep-strings-that-end-in))))

;; Returns (mv erp deps-info state).
(defund read-deps-info (state)
  (declare (xargs :stobjs state))
  (mv-let (erp deps-info state)
    (read-object-from-file "../../build/Makefile-deps.lsp" state) ; todo: make portable
    (if erp
        (mv :failed-to-read-deps-info nil state)
      (if (not (alistp deps-info))
          (mv :bad-deps-info nil state)
        ;; (let ((dependency-map (cdr (assoc-eq :dependency-map deps-info))))
        ;;   (if (not (alistp dependency-map))
        ;;       (mv :bad-deps-info nil state)
        (mv nil           ; no error
            deps-info     ;(strip-cars dependency-map)
            state)))))

;; Example usage:
;; (mv-let (erp deps-info state) (read-deps-info state) (declare (ignore erp)) (assign deps-info deps-info))
;; (assoc-eq :CERT_PL_CERTS (@ deps-info))
;; (assoc-eq :dependency-map (@ deps-info))
;; (strip-cars (@ deps-info))

;; Extract just the book dependencies.
;; TODO: Maybe strip .cert from the names of all the books
(defund book-deps (deps acc)
  (declare (xargs :guard (and (alistp deps)
                              ;; (string-list-listp (strip-cdrs deps))
                              (alistp acc))
                  :guard-hints (("Goal" :expand (strip-cdrs deps)))))
  (if (endp deps)
      (reverse acc)
    (let* ((pair (first deps))
           (book (car pair))
           (all-deps (cdr pair))
           (book-deps (if (string-listp all-deps)
                          ;; TODO: Why can duplicates even arise?
                          (remove-duplicates-equal (keep-strings-that-end-in all-deps ".cert" nil))
                        (er hard? 'book-deps "Bad deps: ~x0" all-deps))))
      (book-deps (rest deps)
                 (acons book book-deps acc)))))

;; (mv-let (erp deps-info state) (read-deps-info state) (declare (ignore erp)) (assign deps-info deps-info))
;; (book-deps (cdr (assoc-eq :dependency-map (@ deps-info))) nil)
