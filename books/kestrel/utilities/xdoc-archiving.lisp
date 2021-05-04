; Utilities for archiving xdoc resources
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "XDOC")

(include-book "xdoc/archive-matching-topics" :dir :system)

;; Returns a list of the XDOC resource directories registered in WRLD.
;;move?
(defun get-xdoc-resource-dirs (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (let ((alist (table-alist 'xdoc::xdoc wrld)))
    (if (not (alistp alist))
        (er hard? 'get-xdoc-resource-dirs "Bad alist.")
      (cdr (assoc-eq 'xdoc::resource-dirs alist)))))

;; Generate a call to archive-matching-topics that archives all topics in the
;; indicated subtree of books/.
;; TREE-PATH should not start or end in "/".
(defun archive-topics-for-books-tree-fn (tree-path ; relative to "books/"
                                         )
  (declare (xargs :guard (stringp tree-path)))
  (let ((path-prefix (concatenate 'string "[books]/" tree-path "/")))
    `(archive-matching-topics
      ;; The test to apply to an arbitrary topic, X, to decide whether to archive
      ;; it (a topic is an alist whose keys are :from, :name, :short, etc.):
      (str::strprefixp ,path-prefix (cdr (assoc-eq :from x))))))

;; Archive all xdoc topics from the indicated subtree of the main books/ directory.
;; TREE-PATH should not start or end in "/".
(defmacro archive-topics-for-books-tree (tree-path ; relative to "books/"
                                         )
  (declare (xargs :guard (stringp tree-path)))
  (archive-topics-for-books-tree-fn tree-path))
