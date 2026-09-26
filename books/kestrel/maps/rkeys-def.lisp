; Definitions of rkeys and related functions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Rename this file?

(include-book "misc/records" :dir :system)
(local (include-book "maps0")) ; reduce?
(include-book "../sets/sets") ; todo: reduce

(defun key-set (r)
  (declare (xargs :guard (rcdp r)))
  (if (consp r)
      (set::insert (caar r)
                   (key-set (cdr r)))
    (set::emptyset)))

(defthm setp-key-set
  (set::setp (key-set r)))

(defun rkeys (r)
  (declare (type t r))
  (key-set (acl2->rcd r)))

;return the keys of the map as a list
(defun key-list (map)
  (declare (type t map))
  (set::2list (rkeys map)))
