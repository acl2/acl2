; Rev function and lemmas
; Copyright (C) 2005-2013 by Jared Davis <jared@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
;
; rev.lisp
; This file was originally part of the Unicode library.

(in-package "ACL2")
(include-book "list-fix")
(local (include-book "revappend"))
(local (include-book "append"))

(defun revappend-without-guard (x y)
  (declare (xargs :guard t))
  (mbe :logic (revappend x y)
       :exec  (if (consp x)
                  (revappend-without-guard (cdr x)
                                           (cons (car x) y))
                y)))

(defsection rev
  :parents (std/lists reverse)
  :short "Logically simple alternative to @(see reverse) for lists."

  :long "<p>This function is nicer to reason about than ACL2's built-in @(see
reverse) function because it is more limited:</p>

<ul>
<li>@('reverse') can operate on strings or lists, whereas @('rev') can only
    operate on lists.</li>

<li>@('reverse') has a tail-recursive definition, which makes it generally
    more difficult to induct over than the non tail-recursive @('rev').</li>
</ul>

<p>Despite its simple @(see append)-based logical definition, @('rev') should
perform quite well thanks to @(see mbe).</p>"

  (defund rev (x)
    (declare (xargs :verify-guards nil
                    :guard t))
    (mbe :logic (if (consp x)
                    (append (rev (cdr x))
                            (list (car x)))
                  nil)
         :exec (revappend-without-guard x nil)))

  (local (in-theory (enable rev)))

  (defthm rev-when-not-consp
    (implies (not (consp x))
             (equal (rev x)
                    nil))
    :hints(("Goal" :in-theory (enable rev))))

  (defthm rev-of-cons
    (equal (rev (cons a x))
           (append (rev x)
                   (list a)))
    :hints(("Goal" :in-theory (enable rev))))

  (defthm true-listp-of-rev
    (true-listp (rev x))
    :rule-classes :type-prescription)

  (defthm rev-of-list-fix
    (equal (rev (list-fix x))
           (rev x))
    :hints(("Goal" :induct (len x))))

  (defthm len-of-rev
    (equal (len (rev x))
           (len x)))

  (defthm rev-of-rev
    (equal (rev (rev x))
           (list-fix x)))

  (defthm consp-of-rev
    (equal (consp (rev x))
           (consp x))
    :hints(("Goal" :induct (len x))))

  (defthm rev-under-iff
    (iff (rev x) (consp x))
    :hints(("Goal" :induct (len x))))

  (defthm revappend-removal
    (equal (revappend x y)
           (append (rev x) y)))

  (verify-guards rev)

  (defthm reverse-removal
    (implies (true-listp x)
             (equal (reverse x)
                    (rev x))))

  (defthm rev-of-append
    (equal (rev (append x y))
           (append (rev y) (rev x))))

  (encapsulate
    ()
    (local (defun cdr-cdr-induction (x y)
             (if (or (atom x)
                     (atom y))
                 nil
               (cdr-cdr-induction (cdr x) (cdr y)))))

    (local (defthm lemma
             (equal (equal (list a) (append y (list b)))
                    (and (atom y)
                         (equal a b)))))

    (local (defthm lemma2
             (implies (and (true-listp x)
                           (true-listp y))
                      (equal (equal (append x (list a))
                                    (append y (list b)))
                             (and (equal x y)
                                  (equal a b))))
             :hints(("Goal" :induct (cdr-cdr-induction x y)))))

    (defthm equal-of-rev-and-rev
      (equal (equal (rev x) (rev y))
             (equal (list-fix x) (list-fix y)))
      :hints(("Goal" :induct (cdr-cdr-induction x y)))))

  (encapsulate
    ()
    (local (defthm make-character-list-of-append
             ;; Reprove this to avoid including make-character-list
             (equal (make-character-list (append x y))
                    (append (make-character-list x)
                            (make-character-list y)))))

    (defthm make-character-list-of-rev
      ;; This arguably doesn't belong here, but maybe it makes more sense here
      ;; than in str/make-character-list, since this way we don't have to include
      ;; rev just to get lemmas about make-character-list.
      (equal (make-character-list (rev x))
             (rev (make-character-list x)))
      :hints(("Goal" :in-theory (enable make-character-list)))))


  (def-listp-rule element-list-p-of-rev
    (implies (element-list-p x)
             (element-list-p (rev x))))

  (def-listfix-rule element-list-fix-of-rev
    (equal (element-list-fix (rev x))
           (rev (element-list-fix x))))

  (def-projection-rule elementlist-projection-of-rev
    (equal (elementlist-projection (rev x))
           (rev (elementlist-projection x)))))



