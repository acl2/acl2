; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; fast-alist-pop.lisp
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "tools/include-raw" :dir :system)
(include-book "xdoc/top" :dir :system)

(defttag fast-alist-pop)

(defxdoc fast-alist-pop
  :parents (fast-alists)
  :short "@('fast-alist-pop') removes the first key-value pair from a fast
alist, provided that the key is not bound in the remainder of the alist."
  :long "<p>This is a user extension to the ACL2 (in particular, ACL2H) system.
It may eventually be added to acl2h proper, but until then it requires a trust
tag since it hasn't been thoroughly vetted for soundness.</p>

<p>Logically, fast-alist-pop is just @('CDR').  However, it has a special
side-effect when called on a fast alist (see @(see hons-acons)).  A fast alist
has a backing hash table mapping its keys to their corresponding (unshadowed)
pairs, which supports constant-time alist lookup.  @(see Hons-acons) adds
key/value pairs to the alist and its backing hash table, and @(see hons-get)
performs constant-time lookup by finding the backing hash table and looking up
the key in the table.  However, logically, hons-get is just @(see
hons-assoc-equal), a more traditional alist lookup function that traverses the
alist until it finds the matching key.  Correspondingly, fast-alist-pop is
logically just CDR, but it removes the key/value pair corresponding to the CAR
of the alist from its backing hash table.</p>

<p>To maintain both the consistency of the alist with the backing hash table
and constant-time performance, fast-alist-pop has a guard requiring that the
key of that first pair not be bound in the cdr of the alist.  Otherwise, simply
removing that pair from the hash table would not be correct, since the key
would remain in the alist bound to some value, which could only be discovered
by linearly traversing the alist.</p>

<p>Note this is just a special case of @(see fast-alist-pop*).</p>")

(defun fast-alist-pop (x)
  "Has an under-the-hood definition."
  (declare (xargs :guard (or (not (consp x))
                             (not (consp (car x)))
                             (not (hons-assoc-equal (caar x) (cdr x))))))
  (mbe :logic (cdr x)
       :exec
       (progn$
        (er hard? 'fast-alist-pop
            "Under the hood definition not installed?")
        (and (consp x)
             (cdr x)))))

(defxdoc fast-alist-pop*
  :parents (fast-alists)
  :short "@('fast-alist-pop*') removes the first key-value pair from a fast
alist, rebinding that key to its previous value in the backing hash table.
That value must be provided as the prev-binding argument."
  :long "<p>This is a user extension to the ACL2 (in particular, ACL2H) system.
It may eventually be added to acl2h proper, but until then it requires a trust
tag since it hasn't been thoroughly vetted for soundness.</p>

<p>Logically, @('(fast-alist-pop* pair x)') is just @('(cdr x)').  However, it
has a special side-effect when called on a fast alist (see @(see hons-acons)).
A fast alist has a backing hash table mapping its keys to their
corresponding (unshadowed) pairs, which supports constant-time alist lookup.
@(see Hons-acons) adds key/value pairs to the alist and its backing hash table,
and @(see hons-get) performs constant-time lookup by finding the backing hash
table and looking up the key in the table.  However, logically, hons-get is
just @(see hons-assoc-equal), a more traditional alist lookup function that
traverses the alist until it finds the matching key.  Correspondingly,
fast-alist-pop* is logically just CDR, but it undoes the binding in the backing
hash table represented by the CAR of the alist.  The guard requires that the
@('prev-binding') argument is the shadowed binding of @('(caar x)') in the
remainder of the alist, so to undo that binding in the backing hash table, we
associate that key to the cdr of the @('prev-binding').</p>")

(defun fast-alist-pop* (prev-binding x)
  "Has an under-the-hood definition."
  (declare (xargs :guard (or (not (consp x))
                             (not (consp (car x)))
                             (equal (hons-assoc-equal (caar x) (cdr x)) prev-binding)))
           (ignorable prev-binding))
  (mbe :logic (cdr x)
       :exec
       (progn$
        (er hard? 'fast-alist-pop*
            "Under the hood definition not installed?")
        (and (consp x)
             (cdr x)))))


; (depends-on "fast-alist-pop-raw.lsp")
(include-raw "fast-alist-pop-raw.lsp")

#||

(include-book
 "std/util/bstar" :dir :system)

(b* ((alist (hons-acons 'a 1 nil))
     (alist (hons-acons 'b 2 alist))
     (alist (fast-alist-pop alist)))
  (and (not (hons-get 'b alist))
       (equal (hons-get 'a alist) '(a . 1))))

||#
