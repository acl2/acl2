; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(include-book "centaur/ubdds/deps" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(local (include-book "centaur/fty/fixequiv" :dir :system))

(local (std::add-default-post-define-hook :fix))

(local
 #!acl2
 (defsection max-depth-in-terms-of-ubdd-deps

   (defthm len-of-or-lists
     (equal (len (or-lists x y))
            (max (len X) (len y)))
     :hints(("Goal" :in-theory (enable or-lists))))

   (defthm len-of-ubdd-deps
     (equal (len (ubdd-deps x))
            (max-depth x))
     :hints(("Goal" :in-theory (enable ubdd-deps max-depth))))

   (local (defun last-of-ubdd-deps-when-ubddp-ind (x)
            (if (atom x)
                nil
              (if (< (max-depth (car x)) (max-depth (cdr x)))
                  (last-of-ubdd-deps-when-ubddp-ind (cdr x))
                (last-of-ubdd-deps-when-ubddp-ind (car x))))))
            

   (defthm last-of-ubdd-deps-when-ubddp
     (implies (ubddp x)
              (iff (nth (+ -1 (max-depth x)) (ubdd-deps x))
                   (consp x)))
     :hints (("goal" :induct (last-of-ubdd-deps-when-ubddp-ind x)
              :in-theory (enable ubddp max-depth ubdd-deps))))

   (local (defthm len-equal-0
            (equal (equal (len x) 0)
                   (not (consp x)))))

   (local (defthm nth-of-gte-len
            (implies (<= (len x) (nfix n))
                     (not (nth n x)))))

   (defthmd nth-ubdd-dep-implies-less-than-max-depth
     (implies (nth n (ubdd-deps x))
              (<= (+ 1 (nfix n)) (max-depth x)))
     :hints (("goal" :use ((:instance len-of-ubdd-deps))
              :in-theory (e/d (len) (len-of-ubdd-deps)))))

   (defthm max-depth-when-not-consp
     (implies (not (consp x))
              (equal (max-depth x) 0))
     :hints(("Goal" :in-theory (enable max-depth))))))


#!acl2
(local
 (defsection max-depth-of-ubdd-ops
   (defthm max-depth-of-q-not
     (equal (max-depth (q-not x)) (max-depth x))
     :hints(("Goal" :in-theory (enable max-depth q-not))))

   (defthm max-depth-of-q-and
     (implies (and (ubddp x) (ubddp y))
              (<= (max-depth (q-binary-and x y)) (max (max-depth x) (max-depth y))))
     :hints (("goal" :use ((:instance q-and-no-new-deps
                            (n (+ -1 (max-depth (q-binary-and x y)))))
                           (:instance nth-ubdd-dep-implies-less-than-max-depth
                            (n (+ -1 (max-depth (q-binary-and x y))))
                            (x x))
                           (:instance nth-ubdd-dep-implies-less-than-max-depth
                            (n (+ -1 (max-depth (q-binary-and x y))))
                            (x y)))
              ;; :cases ((consp (q-binary-and x y)))
              :in-theory (disable q-and-no-new-deps)))
     :rule-classes ((:linear :trigger-terms ((max-depth (q-binary-and x y))))))

   (defthm max-depth-of-q-or
     (implies (and (ubddp x) (ubddp y))
              (<= (max-depth (q-binary-or x y)) (max (max-depth x) (max-depth y))))
     :hints (("goal" :use ((:instance q-or-no-new-deps
                            (n (+ -1 (max-depth (q-binary-or x y)))))
                           (:instance nth-ubdd-dep-implies-less-than-max-depth
                            (n (+ -1 (max-depth (q-binary-or x y))))
                            (x x))
                           (:instance nth-ubdd-dep-implies-less-than-max-depth
                            (n (+ -1 (max-depth (q-binary-or x y))))
                            (x y)))
              ;; :cases ((consp (q-binary-or x y)))
              :in-theory (disable q-or-no-new-deps)))
     :rule-classes ((:linear :trigger-terms ((max-depth (q-binary-or x y))))))

   (defthm max-depth-of-q-xor
     (implies (and (ubddp x) (ubddp y))
              (<= (max-depth (q-binary-xor x y)) (max (max-depth x) (max-depth y))))
     :hints (("goal" :use ((:instance q-xor-no-new-deps
                            (n (+ -1 (max-depth (q-binary-xor x y)))))
                           (:instance nth-ubdd-dep-implies-less-than-max-depth
                            (n (+ -1 (max-depth (q-binary-xor x y))))
                            (x x))
                           (:instance nth-ubdd-dep-implies-less-than-max-depth
                            (n (+ -1 (max-depth (q-binary-xor x y))))
                            (x y)))
              ;; :cases ((consp (q-binary-xor x y)))
              :in-theory (disable q-xor-no-new-deps)))
     :rule-classes ((:linear :trigger-terms ((max-depth (q-binary-xor x y))))))

   (defthm max-depth-of-q-iff
     (implies (and (ubddp x) (ubddp y))
              (<= (max-depth (q-binary-iff x y)) (max (max-depth x) (max-depth y))))
     :hints (("goal" :use ((:instance q-iff-no-new-deps
                            (n (+ -1 (max-depth (q-binary-iff x y)))))
                           (:instance nth-ubdd-dep-implies-less-than-max-depth
                            (n (+ -1 (max-depth (q-binary-iff x y))))
                            (x x))
                           (:instance nth-ubdd-dep-implies-less-than-max-depth
                            (n (+ -1 (max-depth (q-binary-iff x y))))
                            (x y)))
              ;; :cases ((consp (q-binary-iff x y)))
              :in-theory (disable q-iff-no-new-deps)))
     :rule-classes ((:linear :trigger-terms ((max-depth (q-binary-iff x y))))))

   (defthm max-depth-of-q-ite
     (implies (and (ubddp x) (ubddp y) (ubddp z))
              (<= (max-depth (q-ite x y z)) (max (max-depth x) (max (max-depth y) (max-depth z)))))
     :hints (("goal" :use ((:instance q-ite-no-new-deps
                            (n (+ -1 (max-depth (q-ite x y z)))))
                           (:instance nth-ubdd-dep-implies-less-than-max-depth
                            (n (+ -1 (max-depth (q-ite x y z))))
                            (x x))
                           (:instance nth-ubdd-dep-implies-less-than-max-depth
                            (n (+ -1 (max-depth (q-ite x y z))))
                            (x y))
                           (:instance nth-ubdd-dep-implies-less-than-max-depth
                            (n (+ -1 (max-depth (q-ite x y z))))
                            (x z)))
              ;; :cases ((consp (q-ite x y z)))
              :in-theory (disable q-ite-no-new-deps)))
     :rule-classes ((:linear :trigger-terms ((max-depth (q-ite x y z))))))


   (defthm max-depth-of-qv
     (equal (max-depth (qv n))
            (+ 1 (nfix n)))
     :hints(("Goal" :in-theory (enable qv max-depth))))))


(define ubddp (x (var-bound natp))
  (and (acl2::ubddp x)
       (<= (max-depth x) (lnfix var-bound)))
  ///

  (local (defthm max-<-bound
           (implies (and (<= x bound)
                         (<= y bound))
                    (<= (max x y) bound))
           :rule-classes :linear))

  (defthm ubddp-of-aig-not
    (implies (ubddp x bound)
             (ubddp (acl2::q-not x) bound)))

  (defthm ubddp-of-aig-and
    (implies (and (ubddp x bound) (ubddp y bound))
             (ubddp (acl2::q-and x y) bound)))

  (defthm ubddp-of-aig-or
    (implies (and (ubddp x bound) (ubddp y bound))
             (ubddp (acl2::q-or x y) bound))
    :hints(("Goal" :in-theory (enable acl2::q-or))))

  (defthm ubddp-of-aig-xor
    (implies (and (ubddp x bound) (ubddp y bound))
             (ubddp (acl2::q-xor x y) bound))
    :hints(("Goal" :in-theory (enable acl2::q-xor))))

  (defthm ubddp-of-aig-iff
    (implies (and (ubddp x bound) (ubddp y bound))
             (ubddp (acl2::q-iff x y) bound))
    :hints(("Goal" :in-theory (enable acl2::q-iff))))

  (defthm ubddp-of-aig-ite
    (implies (and (ubddp x bound) (ubddp y bound) (ubddp z bound))
             (ubddp (acl2::q-ite x y z) bound))
    :hints(("Goal" :in-theory (enable acl2::q-ite))))

  (defthm ubddp-of-qv
    (implies (< (nfix n) (nfix bound))
             (ubddp (acl2::qv n) bound)))

  (defthm ubddp-when-ubddp-of-lesser
    (implies (and (ubddp x bound1)
                  (<= (nfix bound1) (nfix bound)))
             (ubddp x bound))))

(define max-depth-fix (x (depth natp))
  (cond ((atom x) x)
        ((zp depth) nil)
        (t (acl2::qcons (max-depth-fix (car x) (1- depth))
                        (max-depth-fix (cdr x) (1- depth)))))
  ///
  (local (in-theory (enable max-depth)))

  (defthm max-depth-of-max-depth-fix
    (<= (max-depth (max-depth-fix x depth)) (nfix depth))
    :rule-classes :linear)

  (defthm max-depth-fix-when-max-depth-less
    (implies (and (acl2::ubddp x)
                  (<= (max-depth x) (nfix depth)))
             (equal (max-depth-fix x depth) x))
    :hints(("Goal" :in-theory (enable acl2::ubddp))))

  (defthm max-depth-fix-preserves-ubddp
    (implies (acl2::ubddp x)
             (acl2::ubddp (max-depth-fix x depth)))
    :hints(("Goal" :in-theory (enable acl2::ubddp)))))

(define ubdd-fix (x (depth natp))
  :returns (new-x (ubddp new-x depth))
  :prepwork ((local (in-theory (enable ubddp))))
  (max-depth-fix (acl2::ubdd-fix x) depth)
  ///
  (defthm ubdd-fix-when-ubddp
    (implies (ubddp x depth)
             (equal (ubdd-fix x depth) x))))


   
