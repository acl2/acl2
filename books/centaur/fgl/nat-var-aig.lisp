; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FGL")

(include-book "std/util/deflist" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "centaur/aig/aig-vars" :dir :system)
;; (include-book "centaur/misc/fast-alist-pop" :dir :system)
(include-book "std/stobjs/absstobjs" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))

(local (std::add-default-post-define-hook :fix))

(define bounded-natp (x (bound natp))
  (and (natp x)
       (< x (nfix bound)))
  ///
  (defthm bounded-natp-implies-bound
    (implies (bounded-natp x bound)
             (< x (nfix bound)))
    :rule-classes :forward-chaining)

  (defthm bounded-natp-implies-natp
    (implies (bounded-natp x bound)
             (natp x))
    :rule-classes :forward-chaining)

  (defthm bounded-natp-of-nil
    (not (bounded-natp nil bound)))

  (defthm bounded-natp-when-bounded-by-less
    (implies (and (bounded-natp x bound1)
                  (<= (nfix bound1) (nfix bound)))
             (bounded-natp x bound))))

(define bounded-nat-listp (x (bound natp))
  (if (atom x)
      t
    (and (bounded-natp (car x) bound)
         (bounded-nat-listp (cdr x) bound)))
  ///
  (defthm bounded-nat-listp-when-bounded-by-lesser
    (implies (and (bounded-nat-listp x bound1)
                  (<= (nfix bound1) (nfix bound)))
             (bounded-nat-listp x bound)))

  (defthmd not-bounded-nat-listp-by-member
    (implies (and (member k x)
                  (not (bounded-natp k bound)))
             (not (bounded-nat-listp x bound))))

  (defthmd bounded-nat-listp-implies-not-member
    (implies (and (bounded-nat-listp x bound)
                  (not (bounded-natp k bound)))
             (not (member k x))))

  (defthm bounded-nat-listp-of-append
    (iff (bounded-nat-listp (append a b) bound)
         (and (bounded-nat-listp a bound)
              (bounded-nat-listp b bound))))

  (defthm bounded-nat-listp-of-nil
    (bounded-nat-listp nil bound))

  (defthm bounded-nat-listp-of-cons
    (iff (bounded-nat-listp (cons a b) bound)
         (and (bounded-natp a bound)
              (bounded-nat-listp b bound)))))

(local
 (define bounded-nat-listp-badguy (x bound)
   :verify-guards nil
   (if (atom x)
       nil
     (if (bounded-natp (car x) bound)
         (bounded-nat-listp-badguy (cdr x) bound)
       (car x)))
   ///
   (defthm bounded-nat-listp-badguy-is-bad
     (not (bounded-natp (bounded-nat-listp-badguy x bound) bound)))

   (defthmd bounded-nat-listp-when-nat-listp-badguy-not-member
     (implies (acl2::rewriting-positive-literal `(bounded-nat-listp ,x ,bound))
              (iff (bounded-nat-listp x bound)
                   (not (member (bounded-nat-listp-badguy x bound) x))))
     :hints(("Goal" :in-theory (enable bounded-nat-listp))))

   (defcong set-equiv equal (bounded-nat-listp x bound) 1
     :hints(("Goal" :in-theory (enable bounded-nat-listp-when-nat-listp-badguy-not-member)
             :cases ((bounded-nat-listp x bound))
             :use ((:instance not-bounded-nat-listp-by-member
                    (x x-equiv) (k (bounded-nat-listp-badguy x bound)))
                   (:instance not-bounded-nat-listp-by-member
                    (x x) (k (bounded-nat-listp-badguy x-equiv bound)))))))))

(define aig-p (x (var-bound natp))
  (cond ((atom x) (or (booleanp x) ;; const
                      (bounded-natp x var-bound))) ;; var
        ((eq (cdr x) 'nil) (aig-p (car x) var-bound))
        ;; this is weird because (nil . nil) is a valid aig but it makes it so 
        ;; nat-listp-aig-vars-when-aig-p holds
        ((eq (car x) 'nil) nil)
        (t (and (aig-p (car x) var-bound)
                (aig-p (cdr x) var-bound))))
  ///
  (local (defthm aig-p-is-bounded-nat-listp-aig-vars
           (iff (aig-p x var-bound)
                (bounded-nat-listp (acl2::aig-vars x) var-bound))))

  (defthm bounded-nat-listp-aig-vars-when-aig-p
    (iff (bounded-nat-listp (acl2::aig-vars x) var-bound)
         (aig-p x var-bound))
    :hints(("Goal" :in-theory (enable acl2::aig-atom-p))))
  (local (in-theory (disable bounded-nat-listp-aig-vars-when-aig-p)))

  (defthm aig-p-when-lesser-bound
    (implies (and (aig-p x bound1)
                  (<= (nfix bound1) (nfix bound)))
             (aig-p x bound)))


  (local (defthm member-aig-vars-aig-and
           (implies (and (not (member v (acl2::aig-vars x)))
                         (not (member v (acl2::aig-vars y))))
                    (not (member v (acl2::aig-vars (acl2::aig-and x y)))))
           :hints (("goal" :use ((:instance acl2::member-aig-vars-aig-and
                                  (v v) (x x)))
                    :in-theory (e/d (set::in-to-member)
                                    (acl2::member-aig-vars-aig-and))))))

  (defthm aig-p-of-aig-not
    (implies (aig-p x bound)
             (aig-p (acl2::aig-not x) bound)))

  (local (in-theory (enable bounded-nat-listp-when-nat-listp-badguy-not-member
                            bounded-nat-listp-implies-not-member)))

  (defthm aig-p-of-aig-and
    (implies (and (aig-p x bound) (aig-p y bound))
             (aig-p (acl2::aig-and x y) bound)))

  (local (in-theory (disable aig-p-is-bounded-nat-listp-aig-vars)))

  (defthm aig-p-of-aig-or
    (implies (and (aig-p x bound) (aig-p y bound))
             (aig-p (acl2::aig-or x y) bound))
    :hints(("Goal" :in-theory (enable acl2::aig-or))))

  (defthm aig-p-of-aig-xor
    (implies (and (aig-p x bound) (aig-p y bound))
             (aig-p (acl2::aig-xor x y) bound))
    :hints(("Goal" :in-theory (enable acl2::aig-xor))))

  (defthm aig-p-of-aig-iff
    (implies (and (aig-p x bound) (aig-p y bound))
             (aig-p (acl2::aig-iff x y) bound))
    :hints(("Goal" :in-theory (enable acl2::aig-iff))))

  (defthm aig-p-of-aig-ite
    (implies (and (aig-p x bound) (aig-p y bound) (aig-p z bound))
             (aig-p (acl2::aig-ite x y z) bound))
    :hints(("Goal" :in-theory (enable acl2::aig-ite))))

  (defthm aig-p-of-car
    (implies (aig-p x bound)
             (aig-p (car x) bound)))

  (defthm aig-p-of-cdr
    (implies (aig-p x bound)
             (aig-p (cdr x) bound)))

  (defthm aig-atom-p-when-aig-p
    (implies (aig-p x bound)
             (equal (acl2::aig-atom-p x)
                    (atom x))))
  (defthm aig-p-of-var
    (implies (natp x)
             (equal (aig-p x var-bound)
                    (< x (nfix var-bound))))
    :hints(("Goal" :in-theory (enable bounded-natp)))))

(define aig-fix ((x (aig-p x var-bound)) (var-bound natp))
  :returns (new-x (aig-p new-x var-bound) :hints(("Goal" :in-theory (enable aig-p))))
  :verify-guards nil
  (mbe :logic (cond ((atom x) (and (or (booleanp x)
                                       (bounded-natp x var-bound))
                                   x))
                    ((eq (cdr x) nil)
                     (cons (aig-fix (car x) var-bound) nil))
                    ((eq (car x) nil) nil)
                    (t (b* ((car (aig-fix (car x) var-bound))
                            (cdr (aig-fix (cdr x) var-bound)))
                         (and car cdr (cons car cdr)))))
       :exec x)
  ///
  (defthm aig-fix-when-aig-p
    (implies (aig-p x bound)
             (equal (aig-fix x bound) x))
    :hints(("Goal" :in-theory (enable aig-p))))

  (verify-guards aig-fix :hints(("Goal" :in-theory (enable aig-p)))))



;; (define aig-listp (x (var-bound natp))
;;   (if (atom x)
;;       (eq x nil)
;;     (and (aig-p (car x) var-bound)
;;          (aig-listp (cdr x) var-bound))))
        









