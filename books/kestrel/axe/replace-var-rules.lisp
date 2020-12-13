; Rules about replace-var as used by Axe
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/alists-light/maybe-replace-var" :dir :system)
(include-book "axe-trees")
(include-book "all-dargp-less-than")

(defthm dargp-of-maybe-replace-var
  (implies (and (all-dargp (strip-cdrs alist))
                (symbolp term)
                (not (equal term (maybe-replace-var term alist))))
           (dargp (maybe-replace-var term alist)))
  :hints (("Goal" :in-theory (enable maybe-replace-var))))

(defthm dargp-less-than-of-maybe-replace-var
  (implies (and (all-dargp-less-than (strip-cdrs alist) bound)
                (symbolp term)
                (not (equal term (maybe-replace-var term alist))))
           (dargp-less-than (maybe-replace-var term alist) bound))
  :hints (("Goal" :in-theory (enable maybe-replace-var))))

(defthm myquotep-of-maybe-replace-var
  (implies (and (all-dargp (strip-cdrs alist))
                (symbolp term)
                (equal 'quote (car (maybe-replace-var term alist))))
           (myquotep (maybe-replace-var term alist)))
  :hints (("Goal" :use dargp-of-maybe-replace-var
           :in-theory (disable dargp-of-maybe-replace-var))))

(defthm axe-treep-of-maybe-replace-var
  (implies (and (all-dargp (strip-cdrs alist))
                (symbolp term))
           (axe-treep (maybe-replace-var term alist)))
  :hints (("Goal" :use dargp-of-maybe-replace-var
           :in-theory (disable dargp-of-maybe-replace-var))))

(defthm bounded-axe-treep-of-maybe-replace-var
  (implies (and (all-dargp-less-than (strip-cdrs alist) bound)
                (symbolp term))
           (bounded-axe-treep (maybe-replace-var term alist) bound))
  :hints (("Goal" :use dargp-less-than-of-maybe-replace-var
           :in-theory (e/d (bounded-axe-treep-when-dargp-less-than)
                           (dargp-less-than-of-maybe-replace-var)))))
