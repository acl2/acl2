; GL - A Symbolic Simulation Framework for ACL2
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

(std::deflist nat-listp (x) (natp x) :already-definedp t :true-listp t :elementp-of-nil nil)

(define aig-p (x)
  (cond ((atom x) (or (booleanp x) ;; const
                      (natp x))) ;; var
        ((eq (cdr x) 'nil) (aig-p (car x)))
        ;; this is weird because (nil . nil) is a valid aig but it makes it so 
        ;; nat-listp-aig-vars-when-aig-p holds
        ((eq (car x) 'nil) nil)
        (t (and (aig-p (car x))
                (aig-p (cdr x)))))
  ///
  (defthm nat-listp-aig-vars-when-aig-p
    (iff (nat-listp (acl2::aig-vars x))
         (aig-p x))
    :hints(("Goal" :in-theory (enable acl2::aig-atom-p))))

  (local (defthm aig-p-is-nat-listp-aig-vars
           (iff (aig-p x)
                (nat-listp (acl2::aig-vars x)))))
  (local (in-theory (disable nat-listp-aig-vars-when-aig-p)))

  (local (defun nat-listp-badguy (x)
           (if (atom x)
               nil
             (if (natp (car x))
                 (nat-listp-badguy (cdr x))
               (car x)))))

  (local (defthm nat-listp-when-nat-listp-badguy-not-member
           (implies (and (not (member (nat-listp-badguy x) x))
                         (true-listp x))
                    (nat-listp x))))

  (local (defthm not-natp-of-nat-listp-badguy
           (not (natp (nat-listp-badguy x)))
           :rule-classes :type-prescription))

  (local (defthm nat-listp-implies-not-member-of-non-nat
           (implies (and (nat-listp x)
                         (not (natp k)))
                    (not (member k x)))))

  (local (defthm member-aig-vars-aig-and
           (implies (and (not (member v (acl2::aig-vars x)))
                         (not (member v (acl2::aig-vars y))))
                    (not (member v (acl2::aig-vars (acl2::aig-and x y)))))
           :hints (("goal" :use ((:instance acl2::member-aig-vars-aig-and
                                  (v v) (x x)))
                    :in-theory (e/d (set::in-to-member)
                                    (acl2::member-aig-vars-aig-and))))))

  (defthm aig-p-of-aig-not
    (implies (aig-p x)
             (aig-p (acl2::aig-not x))))

  (defthm aig-p-of-aig-and
    (implies (and (aig-p x) (aig-p y))
             (aig-p (acl2::aig-and x y))))

  (local (in-theory (disable aig-p-is-nat-listp-aig-vars)))

  (defthm aig-p-of-aig-or
    (implies (and (aig-p x) (aig-p y))
             (aig-p (acl2::aig-or x y)))
    :hints(("Goal" :in-theory (enable acl2::aig-or))))

  (defthm aig-p-of-aig-xor
    (implies (and (aig-p x) (aig-p y))
             (aig-p (acl2::aig-xor x y)))
    :hints(("Goal" :in-theory (enable acl2::aig-xor))))

  (defthm aig-p-of-aig-iff
    (implies (and (aig-p x) (aig-p y))
             (aig-p (acl2::aig-iff x y)))
    :hints(("Goal" :in-theory (enable acl2::aig-iff))))

  (defthm aig-p-of-aig-ite
    (implies (and (aig-p x) (aig-p y) (aig-p z))
             (aig-p (acl2::aig-ite x y z)))
    :hints(("Goal" :in-theory (enable acl2::aig-ite))))

  (defthm aig-p-of-car
    (implies (aig-p x)
             (aig-p (car x))))

  (defthm aig-p-of-cdr
    (implies (aig-p x)
             (aig-p (cdr x)))))

(define aig-fix ((x aig-p))
  :returns (new-x aig-p :hints(("Goal" :in-theory (enable aig-p))))
  :verify-guards nil
  (mbe :logic (cond ((atom x) (and (or (booleanp x)
                                       (natp x))
                                   x))
                    ((eq (cdr x) nil)
                     (cons (aig-fix (car x)) nil))
                    ((eq (car x) nil) nil)
                    (t (b* ((car (aig-fix (car x)))
                            (cdr (aig-fix (cdr x))))
                         (and car cdr (cons car cdr)))))
       :exec x)
  ///
  (defthm aig-fix-when-aig-p
    (implies (aig-p x)
             (equal (aig-fix x) x))
    :hints(("Goal" :in-theory (enable aig-p))))

  (verify-guards aig-fix :hints(("Goal" :in-theory (enable aig-p))))
  (fty::deffixtype aig :pred aig-p :fix aig-fix :equiv aig-equiv :define t))


(fty::defalist constraint-alist :key-type aig :val-type bit :true-listp t)

(define alist-remove-dups (x)
  :hooks :fix
  :returns (new-x)
  (if (atom x)
      nil
    (if (and (consp (car x))
             (not (hons-assoc-equal (caar x) (cdr x))))
        (cons (car x) (alist-remove-dups (cdr x)))
      (alist-remove-dups (cdr x))))
  ///
  (defthm alist-remove-dups-when-no-duplicate-keys
    (implies (no-duplicatesp (alist-keys x))
             (equal (alist-remove-dups x) (acl2::alist-fix x)))
    :hints(("Goal" :in-theory (enable alist-keys))))


  (defthm constraint-alist-p-of-alist-remove-dups
    (implies (constraint-alist-p x)
             (constraint-alist-p (alist-remove-dups x)))
    :hints(("Goal" :in-theory (enable constraint-alist-p))))

  (defthm hons-assoc-equal-of-alist-remove-dups-under-iff
    (iff (hons-assoc-equal key (alist-remove-dups x))
         (hons-assoc-equal key x)))

  (defthm no-duplicate-keys-of-alist-remove-dups
    (no-duplicatesp (alist-keys (alist-remove-dups x)))
    :hints(("Goal" :in-theory (enable alist-keys)))))

(define calistp (x)
  (and (constraint-alist-p x)
       (no-duplicatesp-equal (alist-keys x)))
  ///
  (defthm calistp-of-cons
    (implies (and (calistp x)
                  (consp pair)
                  (aig-p (car pair))
                  (bitp (cdr pair))
                  (not (hons-assoc-equal (car pair) x)))
             (calistp (cons pair x))))

  (defthm calistp-of-cdr
    (implies (calistp x)
             (calistp (cdr x)))))

(define calist-fix ((x calistp))
  :prepwork ((local (in-theory (enable calistp)))
             (local (defthm alistp-when-constraint-alist-p-rw
                      (implies (constraint-alist-p x)
                               (alistp x)))))
  :returns (new-x calistp)
  (mbe :logic (alist-remove-dups (constraint-alist-fix x))
       :exec x)
  ///
  (defthm calist-fix-when-calistp
    (implies (calistp x)
             (equal (calist-fix x) x)))

  (fty::deffixtype calist :pred calistp :fix calist-fix :equiv calist-equiv :define t :forward t))

        









