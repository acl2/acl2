; std/alists/worth-hashing.lisp
; Copyright (C) 2013, Regents of the University of Texas
; Written by Bob Boyer and Warren A. Hunt, Jr. (some years before that)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; This file was originally part of misc/hons-help.lisp.  Jared moved these
; definitions into the std/alists library.

(in-package "ACL2")
(include-book "std/util/define" :dir :system)

(define worth-hashing1 (x n)
  (declare (type (unsigned-byte 8) n)
           (xargs :guard t))
  (mbe :logic (>= (len x) n)
       :exec
       (cond ((eql n 0) t)
             ((atom x) nil)
             (t (worth-hashing1 (cdr x) (the (unsigned-byte 8) (1- n)))))))

(local (in-theory (enable worth-hashing1)))

(define worth-hashing (x)
  :parents (std/alists)
  :short "Heuristic for deciding when to use @(see fast-alists)."

  :long "<p>When alists are very short, it may be better for performance and
memory usage to use naive alist algorithms instead of constructing hash
tables.</p>

<p>@(call worth-hashing) is a rough heuristic that is used in various
fast-alist operations (e.g., @(see fal-all-boundp)) to decide when alists are
long enough or will be used heavily enough to justify constructing hash
tables.</p>

<p>It currently just decides whether @('x') is longer than 18 elements long.
This particular choice is just a historical oddity that probably has no
empirical justification.</p>"
  :returns bool
  :inline t
  (mbe :logic (>= (len x) 18)
       :exec (and (consp x)
                  (worth-hashing1 (cdr x) 17))))

