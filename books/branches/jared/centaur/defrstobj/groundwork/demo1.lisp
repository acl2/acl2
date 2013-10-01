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

; GROUNDWORK DEMO 1
;
; This file explains the main idea for a simple state that only has a couple of
; unconstrained fields (not having to deal with arrays or type restrictions
; makes the problem a bit easier).


; -----------------------------------------------------------------------------
;
;                            MY PROCESSOR STATE
;
; -----------------------------------------------------------------------------

(defstobj st

; Here are some "real" fields that I imagine the user cares about.  (More of
; these fields could easily be added.)

  (st-foo       :initially 0)
  (st-bar       :initially 0)

; Here is a special field that I will treat as an ordinary misc/record for
; storing any keys other than :foo or :bar.  It wouldn't be especially
; efficient to use this field, but it might occasionally be convenient for
; one-off things.

  (st-misc      :initially nil)

; Here are two extra fields that I will use to achieve the pure,
; hypothesis-free theorems from misc/records.  In practice, these fields should
; always have their default values.  But the logical fiction behind them is
; explained more, below.

  (st-good      :initially t)
  (st-badplace  :initially nil)

  :inline t)

; Some completely uninteresting groundwork...

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

(in-theory (disable stp
                    create-st
                    st-accessors))

(defthm consp-when-stp
  (implies (stp st)
           (and (consp st)
                (true-listp st)))
  :rule-classes :compound-recognizer
  :hints(("Goal" :in-theory (enable stp))))

(defthm len-when-stp
  (implies (stp st)
           (equal (len st) 5))
  :hints(("Goal" :in-theory (enable stp))))

(defthm acl2-count-of-st-badplace
  (implies (stp st)
           (< (acl2-count (st-badplace st))
              (acl2-count st)))
  :hints(("Goal" :in-theory (enable st-accessors))))

(defthm stp-of-create-st
  (stp (create-st))
  :hints(("Goal" :in-theory (enable create-st stp))))

(defthm stp-of-update-st
  (implies (stp st)
           (and (stp (update-st-foo val st))
                (stp (update-st-bar val st))
                (stp (update-st-misc val st))
                (stp (update-st-good val st))
                (stp (update-st-badplace val st))))
  :hints(("Goal" :in-theory (enable stp st-accessors))))




; -----------------------------------------------------------------------------
;
;                           A HALF-WAY SOLUTION
;
; -----------------------------------------------------------------------------

; I now introduce "arbitrary" accessor/mutator functions, ST-GET1 and ST-SET1,
; which let me treat the ST as a single record-like structure.  The basic idea
; is:
;
;   - The key :FOO goes to the FOO field,
;   - The key :BAR goes to the BAR field, and
;   - Any other keys go to the MISC field (with ordinary g/s operations).
;
; The GOOD and BADPLACE fields aren't part of the interface.  They only exist
; to allow me to implement TO and FROM above, and to use it below.

(defun st-get1 (name st)
  (declare (xargs :stobjs st))
  (cond ((eq name :foo)
         (st-foo st))
        ((eq name :bar)
         (st-bar st))
        (t
         (g name (st-misc st)))))

(defun st-set1 (name val st)
  (declare (xargs :stobjs st))
  (cond ((eq name :foo)
         (update-st-foo val st))
        ((eq name :bar)
         (update-st-bar val st))
        (t
         (update-st-misc (s name val (st-misc st)) st))))


; I can prove theorems that are sort of similar to the misc/records theorems
; about ST-GET1 and ST-SET1, but of course in a couple of cases I need extra
; hyps because in principle you could call these on malformed states.

(defthm stp-of-st-set1
  (implies (stp st)
           (stp (st-set1 name val st))))

(defthm st-get1-of-st-set1-same
  (equal (st-get1 name (st-set1 name val st))
         val)
  :hints(("Goal" :in-theory (enable st-accessors))))

(defthm st-get1-of-st-set1-diff
  (implies (not (equal name1 name2))
           (equal (st-get1 name1 (st-set1 name2 val st))
                  (st-get1 name1 st)))
  :hints(("Goal" :in-theory (enable st-accessors))))

(defthm st-set1-of-st-get1-same  ;; extra hyp needed!
  (implies (stp st)
           (equal (st-set1 name (st-get1 name st) st)
                  st))
  :hints(("Goal" :in-theory (enable st-accessors))))

(defthm st-set1-of-st-set1-same
  (equal (st-set1 name val1 (st-set1 name val2 st))
         (st-set1 name val1 st))
  :hints(("Goal" :in-theory (enable st-accessors))))

(defthm st-set1-of-st-set1-diff ;; extra hyp needed!
  (implies (and (not (equal name1 name2))
                (stp st))
           (equal (st-set1 name1 val1 (st-set1 name2 val2 st))
                  (st-set1 name2 val2 (st-set1 name1 val1 st))))
  :hints(("Goal" :in-theory (enable st-accessors stp))))

(in-theory (disable st-get1 st-set1))



; -----------------------------------------------------------------------------
;
;                    BAD STATES, AND MY INVERTIBLE MAPPING
;
; -----------------------------------------------------------------------------

; Now I want to get rid of these hyps.  To do this I'm going to do the same
; trick that is described in these papers, just adapted to the ST stobj:
;
;    Matt Kaufmann and Rob Sumners.  Efficient rewriting of operations on
;    finite structures in ACL2.  ACL2 Workshop 2002.
;
;    Jared Davis.  Memories: array-like records for ACL2.  ACL2 Workshop, 2006.
;
; The main idea is to partition the ACL2 universe into two sets.
;
; The first set is already defined.  It is the set of all objects recognized by
; STP, which ACL2 defines as a consequence of the DEFSTOBJ.
;
; The second set is recognized by BAD-STP (below) and it consists of:
;   (1) all objects rejected by STP, and also:
;   (2) all STP objects where:
;         - The GOOD field is NIL,
;         - The BADPLACE field is recursively a BAD-STP, and
;         - All other fields have their default values.
;
; This gives me an infinite overlap between the good and bad objects, which I
; can exploit in the same way as these other libraries.
;
; You might think the STOBJ restrictions would prevent us from dealing with
; these sorts of things.  For instance, BAD-STP is going to call itself
; recursively on the BADPLACE field of the stobj.  But, basically, as long as
; make things non-executable, ACL2 is willing to drop the STOBJ restrictions
; and let us just work with their logical definitions.

(defun-nx bad-stp (st)
  (declare (xargs :guard t))
  (or (not (stp st))
      (and (not (st-good st))
           (bad-stp (st-badplace st))

; I want to force all the other fields to have their default values to be
; considered part of the overlap.  A nice way to do this is by just editing the
; object produced by (create-st).  That way, I don't have to say anything here
; about specific user fields, and the same definition should work if new fields
; are added.

           (let* ((st2 (create-st))
                  (st2 (update-st-good nil st2))
                  (st2 (update-st-badplace (st-badplace st) st2)))
             (equal st st2)))))


; (TO ST) is the identity for non-bad states, but if given a bad state ST, it
; just creates a new bad state whose BADPLACE is ST.  This is of course a huge
; violation of stobj discipline since it potentially sticks the input stobj
; into a new stobj's BADPLACE field, but again non-executability lets us get
; away with it.

(defun-nx to (st)
  (declare (xargs :stobjs st))
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

(defthm stp-of-to
  (stp (to st))
  :hints(("Goal"
          :in-theory (e/d (stp st-accessors)
                          (stp-of-create-st))
          :use ((:instance stp-of-create-st)))))

(defthm bad-stp-of-to
  (equal (bad-stp (to st))
         (bad-stp st))
  :hints(("Goal"
          :expand ((bad-stp (update-st-good nil (update-st-badplace st (create-st)))))
          :in-theory (enable st-accessors))))



; (FROM ST) is also the identity for non-bad states, but for bad states it just
; grabs the state that had been pushed into the BADPLACE.  This is an
; especially funny function in that it might return a valid stobj or it might
; not, so of course it has to be non-executable.

(defun-nx from (st)
  (declare (xargs :stobjs st))
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
  (implies (stp st)
           (equal (to (from st))
                  st))
  :hints(("Goal" :in-theory (enable st-accessors))))

(in-theory (disable to from))




; -----------------------------------------------------------------------------
;
;                       MISC/RECORDS LIKE ACCESSORS
;
; -----------------------------------------------------------------------------

; With the mapping in place I can now introduce ST-GET and ST-SET, which are
; the main logical definitions that replace G and S but write to the ST stobj.
; They have the same hyp-free G/S theorems!
;
; These are basically like the definitions in the memories library or the fast
; records book.  Of course they have to be non-executable since they use things
; like TO and FROM which don't make sense in terms of the STOBJ discipline.

(defun-nx st-get (name st)
  (declare (xargs :stobjs st))
  (st-get1 name (to st)))

(defun-nx st-set (name val st)
  (declare (xargs :stobjs st))
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


; -----------------------------------------------------------------------------
;
;                       DEFINITIONS FOR EXECUTION
;
; -----------------------------------------------------------------------------

; Now the only thing that is left is to be able to actually define functions
; that we can logically rewrite to ST-GET but which in the execution will
; update the STOBJ.
;
; For this I first need a definition of a good stobj.

(defund good-stp (st)
  (declare (xargs :stobjs st))
  (mbe :logic (and (stp st)
                   (if (st-good st) t nil))
       :exec (if (st-good st) t nil)))

(defthm not-bad-when-good
  (implies (good-stp st)
           (not (bad-stp st)))
  :hints(("Goal" :in-theory (enable good-stp bad-stp))))


; All of the real functions will need a guard showing that goodness is always
; preserved.  This should be only a minor irritant, since goodness is so easy
; and is always preserved:

(defthm good-stp-of-create-st
  (good-stp (create-st))
  :hints(("Goal" :in-theory (enable create-st good-stp))))

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




; And here are the real accessors/mutators.
;
; I leave these enabled.  Their :logic definitions are just calls of ST-GET or
; ST-SET, so they can be reasoned about just as if the STOBJ was a record.
; Meanwhile, their executable definitions just call the STOBJ accessors and
; destructive mutators.

(encapsulate
  ()

  (local (in-theory (enable st-get st-get1 good-stp)))


; New accessors are easy:

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


; The guard proofs for mutators are slightly trickier, but the lemmas
; needed are not too bad.

  (local (in-theory (enable st-set st-set1)))

  (local (defthm bad-stp-when-st-good
           (implies (and (stp st)
                         (st-good st))
                    (not (bad-stp st)))))

  (local (defthm bad-stp-of-update-foo-when-st-good
           (implies (and (stp st)
                         (st-good st))
                    (not (bad-stp (update-st-foo val st))))
           :hints(("Goal"
                   :in-theory (enable bad-stp stp st-accessors)))))

  (definline st-set-foo (val st)
    (declare (xargs :stobjs st :guard (good-stp st)))
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
           (implies (and (stp st)
                         (st-good st))
                    (not (bad-stp (st-set1 name val st))))
           :hints(("Goal"
                   :in-theory (enable bad-stp stp st-accessors)))))

  (local (in-theory (disable st-set1)))

  (definline st-set-any (name val st)
    (declare (xargs :stobjs st :guard (good-stp st)))
    (mbe :logic (st-set name val st)
         :exec (st-set1 name val st))))


; That's basically it.
;
; At this point, for programming we have:
;
;   (ST-GET-FOO ST)            ; Return ST[:FOO]
;   (ST-GET-BAR ST)            ; Return ST[:BAR]
;   (ST-GET-ANY NAME ST)       ; Return ST[NAME]
;
;   (ST-SET-FOO VAL ST)        ; Set ST[:FOO] := VAL
;   (ST-SET-BAR VAL ST)        ; Set ST[:BAR] := VAL
;   (ST-SET-ANY NAME VAL ST)   ; Set ST[NAME] := VAL
;
; But logically, for efficient rewriting,
;
;    - All of the GETs expand into (ST-GET NAME ST).
;    - All of the SETs expand into (ST-SET NAME VAL ST).
;
; We can now make a nice wrapper that hides the ST stobj and automatically
; calls the most efficient function for any particular field, e.g.,

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
