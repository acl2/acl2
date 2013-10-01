; Record Like Stobjs
; Copyright (C) 2011-2012 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "misc/records" :dir :system)
(include-book "misc/definline" :dir :system)
(local (include-book "local")) ;; just some nth/update-nth stuff.

; GROUNDWORK DEMO 2
;
; This file is very similar to demo1.lisp, but extends the idea to a stobj that
; has a field that is constrained to be an integer.  It seems pretty
; straightforward to put simple type constraints on the fields.

(defstobj st

  (st-foo       :type integer :initially 0)
  (st-bar       :initially 0)
  (st-misc      :initially nil)

  (st-good      :initially t)
  (st-badplace  :initially nil)

  :inline t)

(deftheory st-accessors
  '(update-st-foo
    update-st-bar
    update-st-misc
    update-st-good
    update-st-badplace
    st-foo
    st-bar
    st-misc
    st-good
    st-badplace))

; I can basically fix everything through the definitions of SET-SET and ST-GET
; by just doing everything in terms of a new, WEAK-STP predicate instead of
; using the more restrictive STP predicate.
;
; Before trying weak-stp, I tried to come up with a way to shadow foo with
; another field, so that non-integer writes to foo would be put somewhere else,
; with this taking precedence over whatever values was in foo.  But this seemed
; to be getting pretty complicated.
;
; I now think this weak-stp idea is much nicer.  It lets me almost copy from
; demo1.lisp up through st-set and st-get, and the integerp constraint only
; ends up mattering in the guards of st-set-foo, where they belong.

(defun-nx weak-stp (st)
  (declare (xargs :guard t))
  (and (true-listp st)
       (= (length st) 5)))

(defthm weak-stp-when-stp
  (implies (stp st)
           (weak-stp st)))

(in-theory (disable stp
                    weak-stp
                    create-st
                    st-accessors))

(defthm consp-when-weak-stp
  (implies (weak-stp st)
           (and (consp st)
                (true-listp st)))
  :rule-classes :compound-recognizer
  :hints(("Goal" :in-theory (enable weak-stp))))

(defthm len-when-weak-stp
  (implies (weak-stp st)
           (equal (len st) 5))
  :hints(("Goal" :in-theory (enable weak-stp))))

(defthm acl2-count-of-st-badplace
  (implies (weak-stp st)
           (< (acl2-count (st-badplace st))
              (acl2-count st)))
  :hints(("Goal" :in-theory (enable st-accessors))))

(defthm stp-of-create-st
  (stp (create-st))
  :hints(("Goal" :in-theory (enable create-st stp))))

(defthm weak-stp-of-update-st
  (implies (weak-stp st)
           (and (weak-stp (update-st-foo val st))
                (weak-stp (update-st-bar val st))
                (weak-stp (update-st-misc val st))
                (weak-stp (update-st-good val st))
                (weak-stp (update-st-badplace val st))))
  :hints(("Goal" :in-theory (enable weak-stp st-accessors))))

(defun st-get1 (name st)
  (declare (xargs :stobjs st))
  (cond ((eq name :foo)
         (st-foo st))
        ((eq name :bar)
         (st-bar st))
        (t
         (g name (st-misc st)))))

(defun st-set1 (name val st)
  (declare (xargs :stobjs st
                  :guard (if (eq name :foo)
                             (integerp val)
                           t)))
  (cond ((eq name :foo)
         (update-st-foo val st))
        ((eq name :bar)
         (update-st-bar val st))
        (t
         (update-st-misc (s name val (st-misc st)) st))))

(defthm weak-stp-of-st-set1
  (implies (weak-stp st)
           (weak-stp (st-set1 name val st))))

(defthm st-get1-of-st-set1-same
  (equal (st-get1 name (st-set1 name val st))
         val)
  :hints(("Goal" :in-theory (enable st-accessors))))

(defthm st-get1-of-st-set1-diff
  (implies (not (equal name1 name2))
           (equal (st-get1 name1 (st-set1 name2 val st))
                  (st-get1 name1 st)))
  :hints(("Goal" :in-theory (enable st-accessors))))

(defthm st-set1-of-st-get1-same
  (implies (weak-stp st)
           (equal (st-set1 name (st-get1 name st) st)
                  st))
  :hints(("Goal" :in-theory (enable st-accessors))))

(defthm st-set1-of-st-set1-same
  (equal (st-set1 name val1 (st-set1 name val2 st))
         (st-set1 name val1 st))
  :hints(("Goal" :in-theory (enable st-accessors))))

(defthm st-set1-of-st-set1-diff
  (implies (and (not (equal name1 name2))
                (weak-stp st))
           (equal (st-set1 name1 val1 (st-set1 name2 val2 st))
                  (st-set1 name2 val2 (st-set1 name1 val1 st))))
  :hints(("Goal" :in-theory (enable st-accessors weak-stp))))

(in-theory (disable st-get1 st-set1))



; No longer has a guard, but that's fine...

(defun-nx bad-stp (st)
  (or (not (weak-stp st))
      (and (not (st-good st))
           (bad-stp (st-badplace st))
           (let* ((st2 (create-st))
                  (st2 (update-st-good nil st2))
                  (st2 (update-st-badplace (st-badplace st) st2)))
             (equal st st2)))))



; No longer has a guard, but that's fine...

(defun-nx to (st)
  (if (bad-stp st)
      (let* ((new-st (create-st))
             (new-st (update-st-badplace st new-st))
             (new-st (update-st-good nil new-st)))
        new-st)
    st))

(defthm to-identity
  (implies (not (bad-stp st))
           (equal (to st)
                  st)))

(defthm weak-stp-of-to
  (weak-stp (to st))
  :hints(("Goal"
          :in-theory (e/d (weak-stp st-accessors)))))

(defthm bad-stp-of-to
  (equal (bad-stp (to st))
         (bad-stp st))
  :hints(("Goal"
          :expand ((bad-stp (update-st-good nil (update-st-badplace st (create-st)))))
          :in-theory (enable st-accessors))))


; No longer has a guard, but that's fine...

(defun-nx from (st)
  (if (bad-stp st)
      (st-badplace st)
    st))

(defthm from-identity
  (implies (not (bad-stp st))
           (equal (from st)
                  st)))

(defthm from-to-inverse
  (equal (from (to st))
         st)
  :hints(("Goal" :in-theory (enable st-accessors))))

(defthm to-from-inverse
  (implies (weak-stp st)
           (equal (to (from st))
                  st))
  :hints(("Goal" :in-theory (enable st-accessors))))

(in-theory (disable to from))


; These are as before but without the guards, which is fine

(defun-nx st-get (name st)
  (st-get1 name (to st)))

(defun-nx st-set (name val st)
  (from (st-set1 name val (to st))))

(defthm st-get-of-st-set-same
  (equal (st-get name (st-set name val st))
         val))

(defthm st-get-of-st-set-diff
  (implies (not (equal name1 name2))
           (equal (st-get name1 (st-set name2 val st))
                  (st-get name1 st))))

(defthm st-set-of-st-get-same
  (equal (st-set name1 (st-get name1 st) st)
         st))

(defthm st-set-of-st-set-same
  (equal (st-set name val1 (st-set name val2 st))
         (st-set name val1 st)))

(defthm st-set-of-st-set-diff
  (implies (not (equal name1 name2))
           (equal (st-set name1 val1 (st-set name2 val2 st))
                  (st-set name2 val2 (st-set name1 val1 st)))))

(in-theory (disable st-set st-get))


(defund good-stp (st)
  (declare (xargs :stobjs st))
  (mbe :logic (and (weak-stp st)
                   (if (st-good st) t nil))
       :exec (if (st-good st) t nil)))

(defthm not-bad-when-good
  (implies (good-stp st)
           (not (bad-stp st)))
  :hints(("Goal" :in-theory (enable good-stp bad-stp))))

(defthm good-stp-of-create-st
  (good-stp (create-st))
  :hints(("Goal" :in-theory (enable create-st good-stp)
          ;; wtf??
          :expand ((:free (x) (hide x))))))

(encapsulate
  ()
  (local (defthm l0
           (equal (st-good (st-set1 name val st))
                  (st-good st))
           :hints(("Goal"
                   :in-theory (enable st-set1 st-accessors)))))

  (local (defthm l1
           (implies (good-stp st)
                    (good-stp (st-set1 name val st)))
           :hints(("Goal" :in-theory (enable good-stp)))))

  (defthm good-stp-of-st-set
    (implies (force (good-stp st))
             (good-stp (st-set name val st)))
    :hints(("Goal" :in-theory (enable good-stp st-set)))))


(encapsulate
  ()
  (local (in-theory (enable st-get st-get1 good-stp)))

  (definline st-get-foo (st)
    (declare (xargs :stobjs st :guard (good-stp st)))
    (mbe :logic (st-get :foo st)
         :exec (st-foo st)))

  (definline st-get-bar (st)
    (declare (xargs :stobjs st :guard (good-stp st)))
    (mbe :logic (st-get :bar st)
         :exec (st-bar st)))

  (definline st-get-any (fld st)
    (declare (xargs :stobjs st :guard (good-stp st)))
    (mbe :logic (st-get fld st)
         :exec (st-get1 fld st)))

  (local (in-theory (enable st-set st-set1)))

  (local (defthm bad-stp-when-st-good
           (implies (and (stp st)
                         (st-good st))
                    (not (bad-stp st)))))

  (local (defthm bad-stp-of-update-foo-when-st-good
           (implies (and (stp st)
                         (st-good st)
                         ;; CHANGE -- need a guard about val
                         (integerp val))
                    (not (bad-stp (update-st-foo val st))))
           :hints(("Goal"
                   :in-theory (enable bad-stp stp st-accessors)))))

  (definline st-set-foo (val st)
    (declare (xargs :stobjs st
                    :guard (and (good-stp st)
                                ;; CHANGE -- need a guard about val
                                (integerp val))))
    (mbe :logic (st-set :foo val st)
         :exec (update-st-foo val st)))

  (local (defthm bad-stp-of-update-bar-when-st-good
           (implies (and (stp st)
                         (st-good st))
                    (not (bad-stp (update-st-bar val st))))
           :hints(("Goal"
                   :in-theory (enable bad-stp stp st-accessors)))))

  (definline st-set-bar (val st)
    (declare (xargs :stobjs st :guard (good-stp st)))
    (mbe :logic (st-set :bar val st)
         :exec (update-st-bar val st)))

  (local (defthm bad-stp-of-st-set1-when-st-good
           (implies (and (weak-stp st)
                         (st-good st))
                    (not (bad-stp (st-set1 name val st))))
           :hints(("Goal"
                   :in-theory (enable bad-stp weak-stp st-accessors)))))

  (local (in-theory (disable st-set1)))

  (definline st-set-any (name val st)
    (declare (xargs :stobjs st
                    :guard (and (good-stp st)
                                (if (eq name :foo)
                                    (integerp val)
                                  t))))
    (mbe :logic (st-set name val st)
         :exec (st-set1 name val st))))

(defmacro st-put (name val &optional (stname 'st))
  (cond ((equal name :foo)
         `(st-set-foo ,val ,stname))
        ((equal name :bar)
         `(st-set-bar ,val ,stname))
        (t
         `(st-set-any ,name ,val ,stname))))

(defmacro st-val (name &optional (stname 'st))
  (cond ((equal name :foo)
         `(st-get-foo ,stname))
        ((equal name :bar)
         `(st-get-bar ,stname))
        (t
         `(st-get-any ,name ,stname))))


;;; Examples...

#||

(st-put :foo 3)
(st-val :foo)

(st-put :foo 'bad)  ;; guard error
(st-val :foo)

(st-put :bar 5)
(st-val :bar)

(st-put :baz 7)
(st-val :baz)

(set-gag-mode nil)

(defthm crock
  (equal (st-put :foo foo (st-put :bar bar (st-put :baz baz)))
         (st-put :bar bar (st-put :baz baz (st-put :foo foo)))))

(defthm crock2
  (equal (st-get :argh (st-put :foo foo (st-put :bar bar (st-put :baz baz))))
         (st-get :argh (st-put :bar bar (st-put :baz baz (st-put :foo foo))))))

||#


; And from there it's just the ordinary things, e.g., setting up s* style
; macros, etc.
