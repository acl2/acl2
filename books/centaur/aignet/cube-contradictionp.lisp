; AIGNET - And-Inverter Graph Networks
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "AIGNET")

(include-book "semantics")
(include-book "maybe-litp")
(include-book "std/alists/alist-keys" :dir :system)

(local (std::add-default-post-define-hook :fix))

(define cube-contradictionp ((x lit-listp))
  :returns (contradictionp)
  (if (atom x)
      nil
    (if (member (lit-negate (car x)) (lit-list-fix (cdr x)))
        t
      (cube-contradictionp (cdr x))))
  ///
  (local (defthm aignet-eval-conjunction-when-member
           (implies (and (member x (lit-list-fix y))
                         (equal (lit-eval x invals regvals aignet) 0))
                    (equal (aignet-eval-conjunction y invals regvals aignet) 0))
           :hints(("Goal" :in-theory (enable aignet-eval-conjunction)))))
  
  (defret <fn>-correct
    (implies contradictionp
             (equal (aignet-eval-conjunction x invals regvals aignet)
                    0))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction))))

  (local (defthm lit-negate-when-equal-lit-negate
           (implies (equal (lit-negate x) (lit-fix y))
                    (equal (lit-negate y) (lit-fix x)))
           :hints(("Goal" :in-theory (enable lit-negate
                                             satlink::equal-of-make-lit)))))

  (local (defthm member-lit-list-fix-implies-litp
           (implies (member k (lit-list-fix x))
                    (litp k))
           :hints(("Goal" :in-theory (enable lit-list-fix)))))
  
  (defretd cube-contradictionp-by-member
    (implies (and (member k (lit-list-fix x))
                  (member (lit-negate k) (lit-list-fix x)))
             contradictionp)
    :hints(("Goal" :in-theory (enable lit-list-fix)))))


(local
 (defsection subsetp-lit-list-fix
   
   (defthm member-lit-fix-of-lit-list-fix
     (implies (member k x)
              (member (lit-fix k) (lit-list-fix x)))
     :hints(("Goal" :in-theory (enable lit-list-fix))))

   (defthm subsetp-equal-of-lit-list-fix
     (implies (subsetp-equal x y)
              (subsetp-equal (lit-list-fix x) (lit-list-fix y)))
     :hints(("Goal" :in-theory (enable lit-list-fix subsetp-equal))))

   (defcong acl2::set-equiv acl2::set-equiv (lit-list-fix x) 1
     :hints(("Goal" :in-theory (enable acl2::set-equiv lit-list-fix subsetp-equal)))
     :otf-flg t)

   (defthm member-when-subsetp-lit-list-fix
     (implies (and (subsetp x y)
                   (member-equal lit (lit-list-fix x)))
              (member-equal lit (lit-list-fix y)))
     :hints (("Goal" :use subsetp-equal-of-lit-list-fix
              :in-theory (disable subsetp-equal-of-lit-list-fix))))))

(defsection cube-contradictionp-set-equiv
  
  
  (defthmd cube-contradictionp-when-subsetp
    (implies (and (subsetp-equal x y)
                  (cube-contradictionp x))
             (cube-contradictionp y))
    :hints(("Goal" :in-theory (enable cube-contradictionp)
            :induct (cube-contradictionp x))
           (and stable-under-simplificationp
                '(:use ((:instance cube-contradictionp-by-member
                         (k (lit-fix (car x))) (x y)))))))
  
  (defcong acl2::set-equiv equal (cube-contradictionp x) 1
    :hints(("Goal" :in-theory (enable acl2::set-equiv
                                      cube-contradictionp-when-subsetp) 
            :cases ((cube-contradictionp x))))))

(define cube-contradiction-witness ((x lit-listp))
  :returns (contra litp :rule-classes :type-prescription)
  (if (atom x)
      0
    (if (member (lit-negate (car x)) (lit-list-fix (cdr x)))
        (lit-fix (car x))
      (cube-contradiction-witness (cdr x))))
  ///
  (local (in-theory (enable cube-contradictionp)))
  (defret <fn>-member-when-contradictionp
    (implies (and (cube-contradictionp x)
                  (lit-listp x))
             (and (member-equal contra x)
                  (member-equal (lit-negate contra) x))))

  (defret <fn>-member-when-contradictionp-fix
    (implies (cube-contradictionp x)
             (and (member-equal contra (lit-list-fix x))
                  (member-equal (lit-negate contra) (lit-list-fix x))))))


(define two-cubes-contradictionp ((x lit-listp) (y lit-listp))
  :returns (contradictionp)
  (if (atom x)
      nil
    (if (member (lit-negate (car x)) (lit-list-fix y))
        t
      (two-cubes-contradictionp (cdr x) y)))
  ///
  (local (defthm member-append
           (iff (member k (append x y))
                (or (member k x) (member k y)))))
  (defthmd cube-contradictionp-of-append
    (equal (cube-contradictionp (append x y))
           (or (cube-contradictionp x)
               (cube-contradictionp y)
               (two-cubes-contradictionp x y)))
    :hints(("Goal" :in-theory (enable cube-contradictionp))))

  (local (defthm equal-of-lit-negate
           (implies (equal (lit-negate x) (lit-fix y))
                    (equal (equal (lit-negate y) (lit-fix x)) t))))
  
  (defthm two-cubes-contradictionp-cons-second
    (equal (two-cubes-contradictionp x (cons lit y))
           (or (and (member (lit-negate lit) (lit-list-fix x)) t)
               (two-cubes-contradictionp x y)))
    :hints(("Goal" :in-theory (e/d (two-cubes-contradictionp
                                    lit-list-fix)
                                   (SATLINK::EQUAL-OF-LIT-NEGATE-COMPONENT-REWRITES)))))

  (defthm two-cubes-contradictionp-nil-second
    (equal (two-cubes-contradictionp x nil) nil)
    :hints(("Goal" :in-theory (e/d (two-cubes-contradictionp
                                    lit-list-fix)))))

  (defthm two-cubes-contradictionp-when-subsetp-1
    (implies (and (subsetp-equal x y)
                  (two-cubes-contradictionp x z))
             (two-cubes-contradictionp y z)))
  (defthm two-cubes-contradictionp-when-subsetp-2
    (implies (and (subsetp-equal y z)
                  (two-cubes-contradictionp x y))
             (two-cubes-contradictionp x z)))
  
  (defcong acl2::set-equiv equal (two-cubes-contradictionp x y) 1
    :hints(("Goal" :in-theory (enable acl2::set-equiv)
            :cases ((two-cubes-contradictionp x y)))))

  (defcong acl2::set-equiv equal (two-cubes-contradictionp x y) 2
    :hints(("Goal" :in-theory (enable acl2::set-equiv)
            :cases ((two-cubes-contradictionp x y))))))



(fty::defalist id-neg-alist :key-type natp :val-type bitp :true-listp t)

(define id-neg-alist-to-lit-list ((x id-neg-alist-p))
  :returns (lits lit-listp)
  (if (atom x)
      nil
    (if (mbt (consp (car x)))
        (cons (make-lit (caar x) (cdar x))
              (id-neg-alist-to-lit-list (cdr x)))
      (id-neg-alist-to-lit-list (cdr x))))
  ///
  (defthm eval-of-id-neg-alist-to-lit-list-when-false
    (implies (and (hons-assoc-equal id (id-neg-alist-fix x))
                  ;; literal equivalent evaluates to 0
                  (equal (id-eval id invals regvals aignet)
                         (bfix (cdr (hons-assoc-equal id (id-neg-alist-fix x))))))
             (equal (aignet-eval-conjunction (id-neg-alist-to-lit-list x)
                                             invals regvals aignet)
                    0))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction
                                      id-neg-alist-fix
                                      lit-eval))))

  (local (in-theory (enable id-neg-alist-fix)))

  (defret member-of-id-neg-alist-to-lit-list
    (implies (no-duplicatesp-equal (alist-keys (id-neg-alist-fix x)))
             (iff (member lit lits)
                  (and (litp lit)
                       (equal (cdr (hons-assoc-equal (lit->var lit) (id-neg-alist-fix x)))
                              (lit->neg lit)))))
    :hints(("Goal" :in-theory (e/d (satlink::equal-of-make-lit)
                                   (hons-assoc-equal))
            :induct <call>
            :expand ((:free (a b c) (hons-assoc-equal a (cons b c)))
                     (:free (a) (hons-assoc-equal a nil))
                     (:free (a b) (alist-keys (cons a b))))))))


(define fast-cube-contradictionp-aux ((x lit-listp) (y id-neg-alist-p))
  :returns (contradictionp)
  (b* (((when (atom x))
        (fast-alist-free y)
        nil)
       (y (id-neg-alist-fix y))
       (lit (car x))
       (id (lit->var lit))
       (neg (lit->neg lit))
       (look (hons-get id y))
       ((unless look)
        (fast-cube-contradictionp-aux
         (cdr x) (hons-acons id neg y)))
       ((when (eql neg (cdr look)))
        (fast-cube-contradictionp-aux (cdr x) y)))
    (fast-alist-free y)
    t)
  ///
  

  (local (defthm bitp-of-cdr-assoc-id-neg-alist-fix
           (implies (hons-assoc-equal k (id-neg-alist-fix x))
                    (bitp (cdr (hons-assoc-equal k (id-neg-alist-fix x)))))
           :hints(("Goal" :in-theory (enable id-neg-alist-fix)))
           :rule-classes :type-prescription))

  (fty::deffixequiv fast-cube-contradictionp-aux)
  
  (local (defthm fast-cube-contradictionp-aux-when-member
           (implies (and (not (fast-cube-contradictionp-aux x y))
                         (member (lit-negate lit) (lit-list-fix x)))
                    (not (equal (lit->neg lit)
                                (cdr (hons-assoc-equal (lit->var lit)
                                                       (id-neg-alist-fix y))))))
           :hints(("Goal" :in-theory (enable lit-list-fix)))))
  
  (defret <fn>-correct
    (implies (no-duplicatesp-equal (alist-keys (id-neg-alist-fix y)))
             (equal contradictionp
                    (or (cube-contradictionp x)
                        (two-cubes-contradictionp x (id-neg-alist-to-lit-list y)))))
    :hints(("Goal" :in-theory (enable cube-contradictionp two-cubes-contradictionp
                                      ;; id-neg-alist-fix
                                      id-neg-alist-to-lit-list)
            :induct <call>
            :expand (;; (id-neg-alist-fix y)
                     (two-cubes-contradictionp x (id-neg-alist-to-lit-list y))
                     (:free (a b) (alist-keys (cons a b))))))))


(define longer-or-equal ((n natp) x)
  :enabled t
  (mbe :logic (<= (nfix n) (len x))
       :exec (if (zp n)
                 t
               (and (consp x)
                    (longer-or-equal (1- n) (cdr x))))))

(define fast-cube-contradictionp ((x lit-listp))
  :enabled t
  (mbe :logic (cube-contradictionp x)
       :exec (if (longer-or-equal 300 x) ;; bozo do perf tests
                 (fast-cube-contradictionp-aux x nil)
               (cube-contradictionp x))))

#||
(include-book
 "centaur/misc/numlist" :dir :system)
(local (defthm lit-listp-of-numlist
         (implies (and (litp start) (natp by))
                  (lit-listp (acl2::numlist start by n)))))

(define loop-fast-cube-contradictionp ((m natp) (lits lit-listp))
  (if (zp m)
      nil
    (cons (fast-cube-contradictionp lits)
          (loop-fast-cube-contradictionp (1- m) lits))))

(define loop-cube-contradictionp ((m natp) (lits lit-listp))
  (if (zp m)
      nil
    (cons (cube-contradictionp lits)
          (loop-cube-contradictionp (1- m) lits))))

(define loop-fast-cube-contradictionp-aux ((m natp) (lits lit-listp))
  (if (zp m)
      nil
    (cons (fast-cube-contradictionp-aux lits nil)
          (loop-fast-cube-contradictionp-aux (1- m) lits))))

(define test-cube-contradictionp ((n natp) (m natp))
  (let ((lits (acl2::numlist 2 2 n)))
    (progn$ (time$ (loop-fast-cube-contradictionp m lits))
            (time$ (loop-cube-contradictionp m lits))
            (time$ (loop-fast-cube-contradictionp-aux m lits))
            nil)))
       
||#
