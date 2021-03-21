; Standard Association Lists Library
; Copyright (C) 2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(include-book "alist-keys")
(include-book "alist-vals")

(local
 (encapsulate
   ()
   (in-theory (enable list-fix))

   (local (defthm l0
            (implies (subsetp x (cdr y))
                     (subsetp x y))))

   (defthm subsetp-equal-reflexive
     (subsetp-equal x x))

   (defthm hons-assoc-equal-of-list-fix
     (equal (hons-assoc-equal key (list-fix alist))
            (hons-assoc-equal key alist)))

   (defthm hons-assoc-equal-of-list-fix
     (equal (hons-assoc-equal key (list-fix alist))
            (hons-assoc-equal key alist)))

   (defthm hons-assoc-equal-append
     (equal (hons-assoc-equal x (append a b))
            (or (hons-assoc-equal x a)
                (hons-assoc-equal x b))))

   (defthm alist-keys-of-list-fix
     (equal (alist-keys (list-fix x))
            (alist-keys x)))))


(defsection alists-agree
  :parents (std/alists)
  :short "@(call alists-agree) determines if the alists @('al1') and @('al2')
agree on the value of every key in @('keys')."

  (defund alists-agree (keys al1 al2)
    (declare (xargs :guard t))
    (or (atom keys)
        (and (equal (hons-get (car keys) al1)
                    (hons-get (car keys) al2))
             (alists-agree (cdr keys) al1 al2))))

  (local (in-theory (enable alists-agree)))

  (local (defthmd l0
           (equal (alists-agree (list-fix keys) al1 al2)
                  (alists-agree keys al1 al2))))

  (defcong list-equiv equal (alists-agree keys al1 al2) 1
    :hints(("Goal"
            :in-theory (enable list-equiv)
            :use ((:instance l0)
                  (:instance l0 (keys keys-equiv))))))

  (defthmd alists-agree-hons-assoc-equal
    (implies (and (alists-agree keys a b)
                  (member-equal x keys))
             (equal (hons-assoc-equal x b)
                    (hons-assoc-equal x a))))

  (defthm alists-agree-self
    (alists-agree keys a a))

  (defthmd alists-agree-sym
    (implies (alists-agree keys a b)
             (alists-agree keys b a)))

  (defund alists-disagree-witness (keys al1 al2)
    (and (consp keys)
         (if (not (equal (hons-get (car keys) al1)
                         (hons-get (car keys) al2)))
             (car keys)
           (alists-disagree-witness (cdr keys) al1 al2))))

  (defthmd alists-agree-iff-witness
    (iff (alists-agree keys al1 al2)
         (let ((x (alists-disagree-witness keys al1 al2)))
           (implies (member-equal x keys)
                    (equal (hons-assoc-equal x al1)
                           (hons-assoc-equal x al2)))))
    :hints (("goal" :in-theory (enable alists-disagree-witness))))

  (defthmd alists-agree-trans
    (implies (and (alists-agree keys x y)
                  (alists-agree keys y z))
             (alists-agree keys x z))))



(defsection sub-alistp
  :parents (std/alists)
  :short "@(call sub-alistp) determines whether every @('key') bound in the
alist @('a') is also bound to the same value in the alist @('b')."

  (defund sub-alistp (a b)
    (declare (xargs :guard t))
    (mbe :logic
         (alists-agree (alist-keys a) a b)
         :exec
         (with-fast-alist a
           (with-fast-alist b
             (alists-agree (alist-keys a) a b)))))

  (local (in-theory (enable sub-alistp)))

  (defthm sub-alistp-self
    (sub-alistp x x))

  (defthmd sub-alistp-hons-assoc-equal
    (implies (and (sub-alistp a b)
                  (hons-assoc-equal x a))
             (equal (hons-assoc-equal x a)
                    (hons-assoc-equal x b)))
    :hints(("Goal" :in-theory (enable alists-agree-hons-assoc-equal))))

  (defun not-sub-alistp-witness (a b)
    (alists-disagree-witness (alist-keys a) a b))

  (defthmd sub-alistp-iff-witness
    (iff (sub-alistp a b)
         (let ((x (not-sub-alistp-witness a b)))
           (implies (hons-assoc-equal x a)
                    (equal (hons-assoc-equal x a)
                           (hons-assoc-equal x b)))))
    :hints(("Goal" :in-theory (e/d (alists-agree-iff-witness)
                                   (alists-agree)))))

  (defthmd sub-alistp-when-witness
    (implies (let ((x (not-sub-alistp-witness a b)))
               (implies (hons-assoc-equal x a)
                        (equal (hons-assoc-equal x a)
                               (hons-assoc-equal x b))))
             (sub-alistp a b))
    :hints (("goal" :use sub-alistp-iff-witness)))

  (defthmd sub-alistp-trans
    (implies (and (sub-alistp x y)
                  (sub-alistp y z))
             (sub-alistp x z))
    :hints(("Goal" :in-theory (e/d (sub-alistp-when-witness)
                                   (sub-alistp
                                    not-sub-alistp-witness))
            :use ((:instance sub-alistp-hons-assoc-equal
                             (x (not-sub-alistp-witness x z))
                             (a x) (b y))
                  (:instance sub-alistp-hons-assoc-equal
                             (x (not-sub-alistp-witness x z))
                             (a y) (b z)))))))


(defsection alist-equiv
  :parents (std/alists)
  :short "@(call alist-equiv) determines whether the alists @('a') and @('b')
are equivalent up to @(see hons-assoc-equal), i.e., whether they bind the same
value to every key."

  :long "<p>This is a fundamental equivalence relation for alists.  It allows
you to consider the equivalence of alists regardless of the order of their
elements, the presence of shadowed elements, etc.</p>

<p>Note that @(see list-equiv) is a @(see refinement) of @(see
alist-equiv); however the following example shows that the two are not the
same.</p>

 @({
  (alist-equiv '((0 . a) (0 . b)) '((0 . a) (0 . c))) ;; This is t.
  (set-equiv '((0 . a) (0 . b)) '((0 . a) (0 . c)))   ;; This is nil.
 })"

  (defund alist-equiv (a b)
    (declare (xargs :guard t))
    (mbe :logic (and (sub-alistp a b)
                     (sub-alistp b a))
         :exec
         ;; Silly, make them both fast once instead of twice.
         (with-fast-alist a
           (with-fast-alist b
             (and (sub-alistp a b)
                  (sub-alistp b a))))))

  (local (in-theory (enable alist-equiv alists-agree)))

  (defequiv alist-equiv
    :hints(("Goal" :in-theory (enable sub-alistp-trans))))

  (encapsulate
    ()
    (local (defthm l0
             (implies (and (not (equal (hons-assoc-equal a x)
                                       (hons-assoc-equal a y)))
                           (sub-alistp x y))
                      (not (sub-alistp y x)))
             :hints(("Goal"
                     :use ((:instance sub-alistp-hons-assoc-equal
                                      (x a) (a x) (b y))
                           (:instance sub-alistp-hons-assoc-equal
                                      (x a) (a y) (b x)))))))

    (defthmd alist-equiv-means-all-keys-agree
      (implies (alist-equiv x y)
               (alists-agree keys x y))))


  (defsection alist-equiv-refines-list-equiv

    (local (defthm l0
             (equal (alists-agree keys (list-fix al1) al2)
                    (alists-agree keys al1 al2))
             :hints(("Goal" :in-theory (enable alists-agree)))))

    (local (defthm l1
             (equal (alists-agree keys al1 (list-fix al2))
                    (alists-agree keys al1 al2))
             :hints(("Goal" :in-theory (enable alists-agree)))))

    (local (defthm l2
             (equal (sub-alistp (list-fix x) y)
                    (sub-alistp x y))
             :hints(("Goal" :in-theory (enable sub-alistp)))))

    (local (defthm l3
             (equal (sub-alistp x (list-fix y))
                    (sub-alistp x y))
             :hints(("Goal" :in-theory (enable sub-alistp)))))

    (local (defcong list-equiv equal (sub-alistp x y) 1
             ;; This seems nice but can just be local, because above we showed
             ;; that sub-alistp has an alist-equiv congruence here, which
             ;; combines with the refinement relation we show below.
             :hints(("Goal"
                     :in-theory (e/d (list-equiv) (l2))
                     :use ((:instance l2 (x x))
                           (:instance l2 (x x-equiv)))))))

    (local (defcong list-equiv equal (sub-alistp x y) 2
             ;; Similarly this seems nice but is redundant after we get the
             ;; refinement proved.
             :hints(("Goal"
                     :in-theory (e/d (list-equiv) (l3))
                     :use ((:instance l3 (y y))
                           (:instance l3 (y y-equiv)))))))

    (defrefinement list-equiv alist-equiv
      :hints(("Goal" :in-theory (enable alist-equiv))))))


(defsection basic-alist-equiv-congruences
  :parents (alist-equiv)
  :short "Some @(see congruence) rules about @(see alist-equiv) for basic alist
functions."

  (defcong alist-equiv equal (hons-assoc-equal x a) 2
    :hints (("goal"
             :in-theory (enable alist-equiv alists-agree)
             :use ((:instance alist-equiv-means-all-keys-agree
                              (keys (list x)) (x a) (y a-equiv)))))))


(defsection alist-equiv-bad-guy
  :parents (alist-equiv)
  :short "@(call alist-equiv-bad-guy) finds some key, if one exists, that
differs between the alists @('al1') and @('al2')."

  :long "<p>This is generally useful for doing pick-a-point style reasoning
about alist equivalence.</p>"

  (defchoose alist-equiv-bad-guy (bg) (al1 al2)
    (not (equal (hons-assoc-equal bg al1)
                (hons-assoc-equal bg al2))))

  (local (in-theory (enable alist-equiv alists-agree)))

  (local (defthm l0
           (implies (and (equal (hons-assoc-equal (alist-equiv-bad-guy al1 al2) al1)
                                (hons-assoc-equal (alist-equiv-bad-guy al1 al2) al2)))
                    (equal (hons-assoc-equal a al1)
                           (hons-assoc-equal a al2)))
           :hints(("goal" :use ((:instance alist-equiv-bad-guy (bg a)))))))

  (defthmd alists-agree-when-agree-on-alist-equiv-bad-guy
    (implies (let ((bg (alist-equiv-bad-guy al1 al2)))
               (equal (hons-assoc-equal bg al1)
                      (hons-assoc-equal bg al2)))
             (alists-agree keys al1 al2))
    :hints(("Goal" :induct (len keys))))

  (defthmd alists-agree-when-agree-on-alist-equiv-bad-guy1
    (implies (let ((bg (alist-equiv-bad-guy al1 al2)))
               (equal (hons-assoc-equal bg al1)
                      (hons-assoc-equal bg al2)))
             (alists-agree keys al2 al1))
    :hints(("Goal" :induct (len keys))))

  (defthmd sub-alistp-when-agree-on-alist-equiv-bad-guy
    (implies (let ((bg (alist-equiv-bad-guy al1 al2)))
               (equal (hons-assoc-equal bg al1)
                      (hons-assoc-equal bg al2)))
             (sub-alistp al1 al2))
    :hints(("Goal"
            :in-theory (enable alists-agree-when-agree-on-alist-equiv-bad-guy
                               sub-alistp))))

  (defthmd sub-alistp-when-agree-on-alist-equiv-bad-guy1
    (implies (let ((bg (alist-equiv-bad-guy al2 al1)))
               (equal (hons-assoc-equal bg al1)
                      (hons-assoc-equal bg al2)))
             (sub-alistp al1 al2))
    :hints(("Goal"
            :in-theory (enable alists-agree-when-agree-on-alist-equiv-bad-guy1
                               sub-alistp))))

  (defthmd alist-equiv-when-agree-on-bad-guy
    (implies (let ((bg (alist-equiv-bad-guy al1 al2)))
               (equal (hons-assoc-equal bg al1)
                      (hons-assoc-equal bg al2)))
             (equal (alist-equiv al1 al2) t))
    :hints(("Goal"
            :in-theory (enable sub-alistp-when-agree-on-alist-equiv-bad-guy
                               sub-alistp-when-agree-on-alist-equiv-bad-guy1))))

  (defthmd alist-equiv-iff-agree-on-bad-guy
    (iff (alist-equiv al1 al2)
         (let ((bg (alist-equiv-bad-guy al1 al2)))
           (equal (hons-assoc-equal bg al1)
                  (hons-assoc-equal bg al2))))
    :hints (("goal" :in-theory (e/d (alist-equiv-when-agree-on-bad-guy
                                     sub-alistp-hons-assoc-equal)
                                    (alist-equiv))))))


(defsection more-congruences
  :extension basic-alist-equiv-congruences

  (defcong alist-equiv equal (alists-agree keys a b) 2
    :hints (("goal" :in-theory (enable alists-agree))))

  (defcong alist-equiv equal (alists-agree keys a b) 3
    :hints (("goal" :in-theory (enable alists-agree))))


  (defcong alist-equiv equal (sub-alistp x y) 1
    :hints(("Goal"
            :in-theory (enable alist-equiv sub-alistp-trans)
            :cases ((sub-alistp x y)))))

  (defcong alist-equiv equal (sub-alistp x y) 2
    :hints(("Goal"
            :in-theory (enable alist-equiv sub-alistp-trans)
            :cases ((sub-alistp x y)))))

  #||

;; With the refinement in place, ACL2 will now complain if we try to submit any ;
;; of these, because they're implied by the above stronger congruences about ;
;; alist-equiv. ;

  (defcong list-equiv equal (alists-agree keys x y) 2)
  (defcong list-equiv equal (alists-agree keys x y) 3)
  (defcong list-equiv equal (sub-alistp x y) 1)
  (defcong list-equiv equal (sub-alistp x y) 2)

  ||#

  (encapsulate
    ()
    (local (in-theory (e/d (member alist-keys)
                           (alist-keys-member-hons-assoc-equal))))

    (local (defthm l0
             (implies (member (cons a b) x)
                      (member a (alist-keys x)))))

    (local (defthm l1
             (implies (and (subsetp x y)
                           (member a (alist-keys x)))
                      (member a (alist-keys y)))))

    (local (defthm l2
             (implies (subsetp x y)
                      (subsetp (alist-keys x)
                               (alist-keys y)))))

    (defcong set-equiv set-equiv (alist-keys x) 1
      :hints(("Goal" :in-theory (enable set-equiv)))))


  (encapsulate
    ()
    (local (in-theory (enable member alist-vals)))

    (local (defthm l0
             (implies (member (cons a b) x)
                      (member b (alist-vals x)))))

    (local (defthm l1
             (implies (and (subsetp x y)
                           (member a (alist-vals x)))
                      (member a (alist-vals y)))))

    (local (defthm l2
             (implies (subsetp x y)
                      (subsetp (alist-vals x)
                               (alist-vals y)))))

    (defcong set-equiv set-equiv (alist-vals x) 1
      :hints(("Goal" :in-theory (enable set-equiv)))))


  (defsection alist-keys-set-equivalence

    (local (defthm l1
             (implies (and (subsetp keys (alist-keys x))
                           (alist-equiv x y))
                      (subsetp keys (alist-keys y)))
             :hints(("Goal" :induct (len keys)))))

    (local (defthm l2
             (implies (alist-equiv x y)
                      (subsetp (alist-keys x) (alist-keys y)))
             :hints(("Goal"
                     :in-theory (disable l1)
                     :use ((:instance l1 (keys (alist-keys x))))))))

    (defcong alist-equiv set-equiv (alist-keys x) 1
      :hints(("Goal" :in-theory (enable set-equiv)))))

; Note that there is no similar set-equivalence for alist-vals, because
; shadowed values play a role in alist-vals but not in alist-equiv.  For
; instance, here is an example where equivalent alists have different
; alist-vals:

  #||
  (set-slow-alist-action nil)
  (let ((x '((a . 1) (a . 5)))
  (y '((a . 1))))
  (implies (alist-equiv x y)
  (set-equiv (alist-vals x)
  (alist-vals y))))
  ||#

  (defcong alist-equiv alist-equiv (cons a b) 2
    :hints (("goal" :in-theory (enable alist-equiv-when-agree-on-bad-guy))))

  (defcong alist-equiv alist-equiv (append a b) 1
    :hints(("Goal" :in-theory (enable alist-equiv-when-agree-on-bad-guy))))

  (defcong alist-equiv alist-equiv (append a b) 2
    :hints(("Goal" :in-theory (enable alist-equiv-when-agree-on-bad-guy)))))
