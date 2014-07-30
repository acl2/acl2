; Record Like Stobjs
; Copyright (C) 2011-2012 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "misc/definline" :dir :system)
(include-book "misc/records" :dir :system)
(local (include-book "local")) ;; just some nth/update-nth stuff.

; GROUNDWORK DEMO 3
;
; This is like demo2.lisp, but I make FOO an array of integers instead of a
; single integer.  To the outside, the FOO field looks like a record that can
; hold any keys and values.  The restrictions on its size and values are
; relegated to guards and play no logical role.

; This is somewhat tricky.  My basic idea is to represent the FOO field with
; both an array and a record.  The array holds the indicies, 0 through 31 in
; this case.  The record holds any other keys that aren't valid indices in the
; real array.

(include-book "array-rec")  ;; Lots of stuff related to array/record pairs


(defstobj st

  ;; FOO is internally represented as an array/record pair, where basically the
  ;; array holds keys 0...31 and the record holds any other keys.
  (st-foo       :type (array integer (32)) :initially 0)
  (st-foo-bad   :initially nil)

  (st-bar       :initially 0)
  (st-misc      :initially nil)

  (st-good      :initially t)
  (st-badplace  :initially nil)

  :inline t)


(defsection st-foo-boilerplate

  (defthm st-foop-of-make-list-ac
    ;; This theorem is needed to show stp holds of create-st.
    (implies (and (integerp val)
                  (st-foop acc))
             (st-foop (make-list-ac n val acc)))
    :hints(("Goal" :in-theory (enable st-foop make-list-ac))))

  (defthm true-listp-when-st-foop
    (implies (st-foop x)
             (true-listp x))
    :rule-classes :compound-recognizer)


  ;; Add accessor/mutator for the array since the defstobj doesn't introduce
  ;; them.

  (defun-nx st-foo (st)
    (declare (xargs :stobjs st))
    (nth *st-fooi* st))

  (defun-nx update-st-foo (val st)
    (declare (xargs :stobjs st))
    (update-nth *st-fooi* val st)))


(defthm stp-of-create-st
  (stp (create-st))
  :hints(("Goal" :in-theory (enable create-st stp))))



(deftheory st-accessors
  ;; minor changes here since st changes
  '(update-st-foo
    update-st-fooi
    update-st-foo-bad
    update-st-bar
    update-st-misc
    update-st-good
    update-st-badplace
    st-foo
    st-fooi
    st-foo-bad
    st-bar
    st-misc
    st-good
    st-badplace))

(in-theory (disable st-accessors create-st))



(defsection weak-stp

; The new WEAK-STP is somewhat misnamed.  In some ways it is still weaker than
; the STP predicate, for instance it doesn't require that the elements of
; ST-FOO be integers.  But in other ways it is stronger than STP, e.g., here I
; am enforcing that ST-FOO-BAD should never have anything in indices 0...31.

  (defund-nx weak-stp (st)
    (and (true-listp st)
         (= (len st) 6)
         (array-rec-pair-p (st-foo st)
                           (st-foo-bad st)
                           (st-foo-length st))))

  (local (in-theory (enable weak-stp)))

  (defthm consp-when-weak-stp
    (implies (weak-stp st)
             (and (consp st)
                  (true-listp st)))
    :rule-classes :compound-recognizer)

  (defthm len-when-weak-stp
    (implies (weak-stp st)
             (equal (len st) 6)))

  (defthm acl2-count-of-st-badplace
    (implies (weak-stp st)
             (< (acl2-count (st-badplace st))
                (acl2-count st)))
    :hints(("Goal" :in-theory (enable st-accessors))))

  (defthm weak-stp-of-update-st
    (implies (force (weak-stp st))
             (and (implies (and (force (natp n))
                                (force (< n (st-foo-length st))))
                           (weak-stp (update-st-fooi n val st)))
                  (weak-stp (update-st-bar val st))
                  (weak-stp (update-st-misc val st))
                  (weak-stp (update-st-good val st))
                  (weak-stp (update-st-badplace val st))))
    :hints(("Goal" :in-theory (enable weak-stp st-accessors)))))




(defsection foo-wrappers

; These aren't intended to be executed.  But they give us the logical story of
; how values are written into and read from the two field that comprise FOO.
; You would have similar wrappers for every array/record pair.

  (defund-nx st-get-foo-rec (st)
    (array-to-rec (- (st-foo-length st) 1)
                  (st-foo st)
                  (st-foo-bad st)))

  (defund-nx st-set-foo-rec (val st)
    (let* ((arr (st-foo st))
           (len (st-foo-length st))
           (arr (rec-to-array (- len 1) val arr))
           (rec (delete-rec-indices (- len 1) val))
           (st  (update-st-foo arr st))
           (st  (update-st-foo-bad rec st)))
      st))

  (local (in-theory (enable weak-stp
                            st-accessors
                            st-get-foo-rec
                            st-set-foo-rec
                            array-rec-pair-p)))

; Main theorems about these special FOO wrappers.

  (defthm weak-stp-of-st-set-foo-rec
    (implies (force (weak-stp st))
             (weak-stp (st-set-foo-rec val st))))

  (defthm st-get-foo-rec-of-st-set-foo-rec
    (equal (st-get-foo-rec (st-set-foo-rec val st))
           val))

  (defthm st-set-foo-rec-of-st-get-foo-rec
    (implies (weak-stp st)
             (equal (st-set-foo-rec (st-get-foo-rec st) st)
                    st)))

  (defthm st-set-foo-rec-of-st-set-foo-rec
    (implies (weak-stp st)
             (equal (st-set-foo-rec val1 (st-set-foo-rec val2 st))
                    (st-set-foo-rec val1 st))))


; Frame theorems about these special FOO wrappers.

  (defthm st-get-foo-rec-after-updating-other
    (implies (and (weak-stp st)
                  (natp n)
                  (not (equal n *st-fooi*))
                  (not (equal n *st-foo-bad*)))
             (equal (st-get-foo-rec (update-nth n val st))
                    (st-get-foo-rec st))))

  (defthm st-set-foo-rec-after-updating-other
    (implies (and (weak-stp st)
                  (natp n)
                  (not (equal n *st-fooi*))
                  (not (equal n *st-foo-bad*)))
             (equal (st-set-foo-rec val1 (update-nth n val2 st))
                    (update-nth n val2 (st-set-foo-rec val1 st)))))

  (defthm other-after-st-set-foo-rec
    (implies (and (weak-stp st)
                  (natp n)
                  (not (equal n *st-fooi*))
                  (not (equal n *st-foo-bad*)))
             (equal (nth n (st-set-foo-rec val st))
                    (nth n st))))


; Extra well-formedness theorems about the FOO wrappers.  These are needed to
; show that UPDATE-ST-FOOI is the same as using our wrappers.

  (defthm update-st-fooi-when-good-inputs
    (implies (and (weak-stp st)
                  (natp i)
                  (integerp val)
                  (< i (st-foo-length st)))
             (equal (update-st-fooi i val st)
                    (st-set-foo-rec (s i val (st-get-foo-rec st)) st))))

  (defthm st-set-foo-rec-still-good
    (implies (and (weak-stp st)
                  (natp i)
                  (< i (st-foo-length st)))
             (weak-stp
              (st-set-foo-rec (s i val (st-get-foo-rec st)) st))))

  (defthm st-good-of-st-set-foo-rec
    (equal (st-good (st-set-foo-rec val st))
           (st-good st)))

  )



(defsection st-wrappers

; Main wrappers are basically as before, but we now use our special FOO
; wrappers in the case of writing/reading from FOO.

  (defund-nx st-get1 (name st)
    (cond ((eq name :foo)
           (st-get-foo-rec st))
          ((eq name :bar)
           (st-bar st))
          (t
           (g name (st-misc st)))))

  (defund-nx st-set1 (name val st)
    (cond ((eq name :foo)
           (st-set-foo-rec val st))
          ((eq name :bar)
           (update-st-bar val st))
          (t
           (update-st-misc (s name val (st-misc st)) st))))

  (local (in-theory (enable st-get1 st-set1)))

  (defthm weak-stp-of-st-set1
    (implies (weak-stp st)
             (weak-stp (st-set1 name val st))))

  (local (in-theory (enable st-accessors)))

  (defthm st-get1-of-st-set1-same
    (equal (st-get1 name (st-set1 name val st))
           val))

  (defthm st-get1-of-st-set1-diff
    (implies (and (weak-stp st)
                  (not (equal name1 name2)))
             (equal (st-get1 name1 (st-set1 name2 val st))
                    (st-get1 name1 st))))

  (defthm st-set1-of-st-get1-same
    (implies (weak-stp st)
             (equal (st-set1 name (st-get1 name st) st)
                    st)))

  (defthm st-set1-of-st-set1-same
    (implies (weak-stp st)
             (equal (st-set1 name val1 (st-set1 name val2 st))
                    (st-set1 name val1 st))))

  (defthm st-set1-of-st-set1-diff
    (implies (and (not (equal name1 name2))
                  (weak-stp st))
             (equal (st-set1 name1 val1 (st-set1 name2 val2 st))
                    (st-set1 name2 val2 (st-set1 name1 val1 st))))))



(defun-nx bad-stp (st)
  (or (not (weak-stp st))
      (and (not (st-good st))
           (bad-stp (st-badplace st))
           (let* ((st2 (create-st))
                  (st2 (update-st-good nil st2))
                  (st2 (update-st-badplace (st-badplace st) st2)))
             (equal st st2)))))



(defsection good/bad-conversion

  (defund-nx to (st)
    (if (bad-stp st)
        (let* ((new-st (create-st))
               (new-st (update-st-badplace st new-st))
               (new-st (update-st-good nil new-st)))
          new-st)
      st))

  (defund-nx from (st)
    (if (bad-stp st)
        (st-badplace st)
      st))

  (local (in-theory (enable to from)))

  (defthm to-identity
    (implies (not (bad-stp st))
             (equal (to st)
                    st)))

  (defthm weak-stp-of-to
    (weak-stp (to st))
    :hints(("Goal" :in-theory (e/d (weak-stp st-accessors create-st)))))

  (defthm bad-stp-of-to
    (equal (bad-stp (to st))
           (bad-stp st))
    :hints(("Goal"
            :expand ((bad-stp (update-st-good nil (update-st-badplace st (create-st)))))
            :in-theory (enable st-accessors))))

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
    :hints(("Goal" :in-theory (enable st-accessors)))))



(defsection main-logical-story

  (defund-nx st-get (name st)
    (st-get1 name (to st)))

  (defund-nx st-set (name val st)
    (from (st-set1 name val (to st))))

  (local (in-theory (enable st-get st-set)))

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
                    (st-set name2 val2 (st-set name1 val1 st))))))



(defsection good-stp

; We expect that (ST-GOOD ST) should always hold and that (ST-FOO-BAD ST)
; should always be NIL.  If this is the case, then our GOOD-STP function should
; be very fast.

  (local (in-theory (enable stp
                            weak-stp
                            st-accessors
                            array-rec-pair-p)))

  (local (defthm good-stp-help1
           (implies (and (stp st)
                         (not (st-foo-bad st)))
                    (weak-stp st))))

  (defund good-stp (st)
    (declare (xargs :stobjs st))
    (mbe :logic (and (weak-stp st)
                     (if (st-good st) t nil))
         :exec (and (st-good st)
                    (or (not (st-foo-bad st))
                        ;; this shouldn't get executed:
                        (equal (st-foo-bad st)
                               (delete-rec-indices 31 (st-foo-bad st)))))))

  (local (in-theory (enable good-stp bad-stp)))

  (defthm not-bad-when-good
    (implies (good-stp st)
             (not (bad-stp st))))

  (defthm good-stp-of-create-st
    (good-stp (create-st))
    :hints(("Goal" :in-theory (enable create-st))))

  (local (defthm l0
           (equal (st-good (st-set1 name val st))
                  (st-good st))
           :hints(("Goal"
                   :in-theory (enable st-set1 st-set-foo-rec)))))

  (local (defthm l1
           (implies (good-stp st)
                    (good-stp (st-set1 name val st)))
           :hints(("Goal" :in-theory (enable good-stp)))))

  (defthm good-stp-of-st-set
    (implies (force (good-stp st))
             (good-stp (st-set name val st)))
    :hints(("Goal" :in-theory (enable st-set)))))



(defsection nice-getters

  (local (in-theory (enable st-get
                            st-get1
                            st-get-foo-rec
                            good-stp
                            st-accessors)))

  (definline st-get-fooi (i st)
    (declare (xargs :stobjs st
                    :guard (and (good-stp st)
                                (natp i)
                                (< i (st-foo-length st)))))
    (mbe :logic (g i (st-get :foo st))
         :exec (st-fooi i st)))

  (definline st-get-bar (st)
    (declare (xargs :stobjs st :guard (good-stp st)))
    (mbe :logic (st-get :bar st)
         :exec (st-bar st)))

  ;; We don't provide an st-get-any anymore, since st-get-foo-rec isn't
  ;; efficiently executable in general.

  )


(defsection nice-setters

  (local (in-theory (enable good-stp
                            st-set
                            st-set1
                            st-get
                            st-get1)))

  (definline st-set-fooi (i val st)
    (declare (xargs :stobjs st
                    :guard (and (good-stp st)
                                (natp i)
                                (integerp val)
                                (< i (st-foo-length st)))))
    (mbe :logic (st-set :foo
                        (s i val (st-get :foo st))
                        st)
         :exec (update-st-fooi i val st)))

  (defthm st-good-of-update-st-bar
    (equal (st-good (update-st-bar val st))
           (st-good st))
    :hints(("Goal" :in-theory (enable st-accessors))))

  (definline st-set-bar (val st)
    (declare (xargs :stobjs st
                    :guard (good-stp st)))
    (mbe :logic (st-set :bar val st)
         :exec (update-st-bar val st))))

