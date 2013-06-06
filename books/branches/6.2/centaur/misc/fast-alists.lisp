; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>


(in-package "ACL2")

;; A library about fast alists.

;; Conventions:

;; All accesses and updates within functions use hons-get and hons-acons rather
;; than hons-assoc-equal and cons (cons ...).  However, theorems are written in
;; terms of hons-assoc-equal and conses.  (Are there any situations in which we
;; might want to write rules about hons-acons?)

;; Functions are all written so as to ignore non-pair elements of alists.  This
;; way we shouldn't ever need an alistp hyp.


(include-book "alist-witness")
(include-book "equal-sets")
(include-book "universal-equiv")
(include-book "std/alists/top" :dir :system)





(defsection al-shrink
  (defthm hons-assoc-equal-hshrink-alist
    (equal (hons-assoc-equal key (hshrink-alist a b))
           (or (hons-assoc-equal key b)
               (hons-assoc-equal key a)))
    :hints(("Goal" :in-theory (enable hons-assoc-equal
                                      hons-shrink-alist))))

  (defthmd hons-assoc-equal-al-shrink
    (equal (hons-assoc-equal key (al-shrink a))
           (hons-assoc-equal key a))
    :hints(("Goal" :in-theory (enable al-shrink))))

  (defthm alist-equiv-al-shrink
    (alist-equiv (al-shrink a) a)
    :hints(("Goal" :in-theory
            (enable alist-equiv-iff-agree-on-bad-guy
                    hons-assoc-equal-al-shrink)))))


;; MAKE-FAL and APPEND

(defthm associativity-of-append
  (equal (append (append a b) c)
         (append a (append b c))))



(defthm hshrink-alist-alist-equiv-append
  (alist-equiv (hons-shrink-alist a b)
               (append b a))
  :hints(("Goal" :in-theory (enable alist-equiv-iff-agree-on-bad-guy))))


(defthm hons-assoc-equal-make-fal
  (equal (hons-assoc-equal x (make-fal a b))
         (or (hons-assoc-equal x a)
             (hons-assoc-equal x b))))

(defthm make-fal-alist-equiv-append
  (alist-equiv (make-fal a b)
               (append a b))
  :hints(("Goal" :in-theory (enable alist-equiv-iff-agree-on-bad-guy))))



(in-theory (disable car-hons-assoc-equal-split))




(defcong set-equiv alist-equiv (fal-extract keys al) 1
  :hints(("Goal" :in-theory (enable fal-extract
                                    alist-equiv-iff-agree-on-bad-guy))
         (set-reasoning)))





(defthm alist-keys-hons-put-list
  (set-equiv (alist-keys (hons-put-list vars vals rest))
             (union-equal vars (alist-keys rest)))
  :hints (("goal" :in-theory (enable alist-keys))
          (set-reasoning)))



(defn alist-fix (al)
  (if (atom al)
      nil
    (if (atom (car al))
        (alist-fix (cdr al))
      (cons (car al) (alist-fix (cdr al))))))

(defthmd hons-assoc-equal-alist-fix
  (equal (hons-assoc-equal k (alist-fix a))
         (hons-assoc-equal k a)))

(defthm alist-fix-alist-equiv
  (alist-equiv (alist-fix a) a)
  :hints(("Goal" :in-theory
          (enable alist-equiv-iff-agree-on-bad-guy
                  hons-assoc-equal-alist-fix))))


(defn nonempty-alistp (x)
  (and (consp x)
       (or (consp (car x))
           (nonempty-alistp (cdr x)))))


(defn first-key (x)
  (and (consp x)
       (if (consp (car x))
           (caar x)
         (first-key (cdr x)))))

(defthmd nonempty-alistp-first-key
  (iff (nonempty-alistp a)
       (hons-assoc-equal (first-key a) a)))

(defthmd empty-alist-hons-assoc-equal
  (implies (not (nonempty-alistp a))
           (not (hons-assoc-equal x a)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))


(defcong alist-equiv equal (nonempty-alistp a) 1
  :hints(("Goal"
          :use ((:instance nonempty-alistp-first-key)
                (:instance empty-alist-hons-assoc-equal
                           (x (first-key a))
                           (a a-equiv))
                (:instance nonempty-alistp-first-key
                           (a a-equiv))
                (:instance empty-alist-hons-assoc-equal
                           (x (first-key a-equiv)))))))





(defn al-covers-keys (keys al)
  (or (atom keys)
      (and (hons-get (car keys) al)
           (al-covers-keys (cdr keys) al))))

(defthm al-covers-keys-to-subset
  (equal (al-covers-keys keys al)
         (subsetp-equal keys (alist-keys al)))
  :hints(("Goal" :in-theory (enable subsetp-equal))))

(defcong alist-equiv equal (al-covers-keys keys al) 2)

(defcong set-equiv equal (al-covers-keys keys al) 1
  :hints (("goal" :in-theory (disable set-equiv))))



(defsection hons-acons-each
  (local (in-theory (enable hons-acons-each)))

  (defthm hons-assoc-equal-hons-acons-each
    (equal (hons-assoc-equal x (hons-acons-each keys val rest))
           (if (member-equal x keys)
               (cons x val)
             (hons-assoc-equal x rest))))

  (defthm alist-keys-hons-acons-each
    (equal (alist-keys (hons-acons-each keys val rest))
           (append keys (alist-keys rest)))))



(defsection keys-equiv
  ;; Note:  Keys-equiv is equivalent to (set-equiv (alist-keys x)...)
  ;; but sometimes it's convenient to have as its own equivalence relation.

  (def-universal-equiv keys-equiv
    :qvars k
    :equiv-terms ((iff (hons-assoc-equal k x)))
    :defquant t
    :witness-dcls ((declare (xargs :guard t
                                   :verify-guards nil))))

  (defexample keys-equiv-example
    :pattern (hons-assoc-equal k x)
    :templates (k)
    :instance-rulename keys-equiv-instancing)

  (verify-guards keys-equiv)

  (defcong keys-equiv iff (hons-assoc-equal k x) 2
    :hints ((witness)))

  (defcong keys-equiv set-equiv (alist-keys x) 1
    :hints(("Goal" :in-theory (e/d () (set-equiv)))
           (witness)))

  (defthm keys-equiv-when-alist-keys
    (implies (set-equiv (double-rewrite (alist-keys env1))
                         (double-rewrite (alist-keys env2)))
             (equal (keys-equiv env1 env2) t))
    :hints(("Goal" :in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                                   (set-equiv
                                    alist-keys-member-hons-assoc-equal)))
           (witness))))


(defsection sub-alistp-witness

  (defwitness sub-alistp-witnessing
    :predicate (not (sub-alistp a b))
    :expr (let ((x (not-sub-alistp-witness a b)))
            (not (implies (hons-assoc-equal x a)
                          (equal (hons-assoc-equal x a)
                                 (hons-assoc-equal x b)))))
    :hints ('(:use sub-alistp-when-witness
                   :in-theory nil))
    :generalize (((not-sub-alistp-witness a b) . key)))

  (definstantiate sub-alistp-instancing
    :predicate (sub-alistp a b)
    :expr (implies (hons-assoc-equal key a)
                   (equal (hons-assoc-equal key a)
                          (hons-assoc-equal key b)))
    :vars (key)
    :hints ('(:in-theory '(sub-alistp-hons-assoc-equal))))

  (defexample sub-alistp-hons-assoc-equal-ex
    :pattern (hons-assoc-equal k a)
    :templates (k)
    :instance-rulename sub-alistp-instancing))





