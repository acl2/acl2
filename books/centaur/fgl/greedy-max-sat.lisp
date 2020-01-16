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

(include-book "sat-binder-defs")
(include-book "centaur/fty/baselists" :dir :system)
(include-book "centaur/misc/numlist" :dir :system)
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/append" :dir :system))

(local (std::add-default-post-define-hook :fix))

(defun-sk indices-all-true (indices x)
  (forall idx
          (implies (member (nfix idx) (acl2::nat-list-fix indices))
                   (nth idx x))))

(defun-sk non-indices-all-false (indices x)
  (forall idx
          (implies (not (member (nfix idx) (acl2::nat-list-fix indices)))
                   (not (nth idx x)))))

(local (in-theory (disable indices-all-true
                           non-indices-all-false)))

(defthm indices-all-true-of-no-indices
  (indices-all-true nil x)
  :hints(("Goal" :in-theory (enable indices-all-true))))

(defthm non-indices-all-false-of-atom
  (implies (not (consp x))
           (non-indices-all-false indices x))
  :hints(("Goal" :in-theory (enable non-indices-all-false))))

(defthm indices-all-true-of-cons
  (iff (indices-all-true (cons a b) x)
       (and (nth a x)
            (indices-all-true b x)))
  :hints (("goal" :use ((:instance indices-all-true-necc
                         (indices (cons a b))
                         (idx (indices-all-true-witness b x)))
                        (:instance indices-all-true-necc
                         (indices b)
                         (idx (indices-all-true-witness (cons a b) x)))
                        (:instance indices-all-true-necc
                         (indices (cons a b))
                         (idx a)))
           :in-theory (e/d* (indices-all-true
                             acl2::arith-equiv-forwarding)
                            (indices-all-true-necc))
           :do-not-induct t)))
                        
(defthm non-indices-all-false-of-append-to-atom
  (implies (not (consp x))
           (non-indices-all-false indices (append (acl2::repeat n nil) x)))
  :hints(("Goal" :in-theory (enable non-indices-all-false))))


(defthm my-nth-of-append
  (equal (nth n (append a b))
         (if (< (nfix n) (len a))
             (nth n a)
           (nth (- (nfix n) (len a)) b)))
  :hints(("Goal" :cases ((zp n))
          :do-not-induct t)))

(defthmd my-nth
  (equal (nth n x)
         (if (zp n)
             (car x)
           (nth (- (nfix n) 1) (cdr x))))
  :hints(("Goal" :in-theory (enable nth)))
  :rule-classes :definition)

(local (in-theory (disable acl2::nth-of-append)))

(defthm indices-all-true-of-cons-nil-append-repeat-cdr
  (implies (indices-all-true indices (append (acl2::repeat n nil) x))
           (iff (indices-all-true indices (cons nil (append (acl2::repeat n nil) (cdr x))))
                (not (member (nfix n) (acl2::nat-list-fix indices)))))
  :hints (("goal" :use ((:instance indices-all-true-necc
                         (x (append (acl2::repeat n nil) x))
                         (idx n))
                        (:instance indices-all-true-necc
                         (x (append (acl2::repeat n nil) x))
                         (idx (indices-all-true-witness
                               indices (cons nil (append (acl2::repeat n nil) (cdr x))))))
                        (:instance indices-all-true-necc
                         (x (cons nil (append (acl2::repeat n nil) (cdr x))))
                         (idx n)))
           :in-theory (e/d* (acl2::arith-equiv-forwarding)
                            (indices-all-true-necc nth))
           :expand ((indices-all-true indices (cons nil (append (acl2::repeat n nil) (cdr x))))
                    (:free (n) (nth n x))
                    (:free (n x) (nth n (cons nil x)))))
          (and stable-under-simplificationp
               '(:cases ((natp (indices-all-true-witness indices (cons nil (append (acl2::repeat n nil) (cdr x))))))))))


(defthm non-indices-all-false-of-cons
  (implies (non-indices-all-false indices x)
           (non-indices-all-false (cons a indices) x))
  :hints (("goal" :use ((:instance non-indices-all-false-necc
                         (idx (non-indices-all-false-witness (cons a indices) x))))
           :expand ((non-indices-all-false (cons a indices) x))
           :in-theory (e/d (member)
                           (non-indices-all-false-necc)))))

(defthm non-indices-all-false-of-cons-append-repeat
  (implies (non-indices-all-false indices (cons nil (append (acl2::repeat n nil) (cdr x))))
           (non-indices-all-false (cons (nfix n) indices) (append (acl2::repeat n nil) x)))
  :hints (("goal" :use ((:instance non-indices-all-false-necc
                         (x (cons nil (append (acl2::repeat n nil) (cdr x))))
                         (idx (non-indices-all-false-witness (cons (nfix n) indices)
                                                             (append (acl2::repeat n nil) x)))))
           :expand ((non-indices-all-false (cons (nfix n) indices) (append (acl2::repeat n nil) x))
                    (:free (n x) (nth n (cons nil x))))
           :in-theory (e/d (member)
                           (non-indices-all-false-necc)))
          (and stable-under-simplificationp
               '(:cases ((natp
                          (non-indices-all-false-witness (cons (nfix n) indices)
                                                         (append (acl2::repeat n nil) x))))))))


(defthm numlist-of-0
  (equal (numlist start by 0) nil)
  :hints(("Goal" :in-theory (enable numlist))))


(defthm numlist-of-plus-1
  (implies (natp n)
           (equal (numlist start by (+ 1 n))
                  (cons start (numlist (+ start by) by n))))
  :hints(("Goal" :in-theory (enable numlist))))

(defthm nat-listp-of-numlist
  (implies (and (natp start) (natp by))
           (nat-listp (numlist start by n)))
  :hints(("Goal" :in-theory (enable numlist))))

(defthm member-of-numlist
  (implies (natp start)
           (iff (member k (numlist start 1 n))
                (and (integerp k)
                     (<= start k)
                     (< k (+ start (nfix n))))))
  :hints(("Goal" :in-theory (enable numlist member))))

(defthm non-indices-all-false-of-numlist-append-repeat
  (implies (not (car x))
           (non-indices-all-false (numlist (+ 1 (nfix n)) 1 (len (cdr x)))
                                  (append (acl2::repeat n nil) x)))
  :hints(("Goal" :in-theory (enable non-indices-all-false
                                    acl2::nth-when-too-large))))

(defthm non-indices-all-false-of-numlist
  (non-indices-all-false (numlist 0 1 (len x)) x)
  :hints(("Goal" :in-theory (enable non-indices-all-false))))

(local (in-theory (disable member-equal nfix not
                           indices-all-true
                           non-indices-all-false
                           len numlist)))



(define nat-list-all-gte ((n natp) (x nat-listp))
  (if (atom x)
      t
    (and (<= (lnfix n) (lnfix (car x)))
         (nat-list-all-gte n (cdr x))))
  ///
  (defthm nat-list-all-gte-of-cons
    (equal (nat-list-all-gte n (cons a b))
           (and (<= (nfix n) (nfix a))
                (nat-list-all-gte n b))))

  (defthm nat-list-all-gte-of-plus-1
    (implies (natp n)
             (equal (nat-list-all-gte (+ 1 n) x)
                    (and (nat-list-all-gte n x)
                         (not (member n (acl2::nat-list-fix x))))))
    :hints(("Goal" :in-theory (enable acl2::nat-list-fix
                                      member))))

  (defthm nat-list-all-gte-of-numlist
    (implies (and (<= (nfix n) start)
                  (natp start))
             (nat-list-all-gte n (numlist start 1 k)))
    :hints(("Goal" :in-theory (enable numlist)))))

(define greedy-max-sat-aux (ans x sat-config start-index assumption)
  :verify-guards nil
  (declare (ignore sat-config))
  (let ((x+ (append (make-list start-index) x)))
    (if (and (nat-list-all-gte start-index ans)
             (implies (and (indices-all-true ans x+)
                           assumption)
                      (non-indices-all-false ans x+)))
        ans
      (numlist (nfix start-index) 1 (len x))))
  ///
  (defmacro greedy-max-sat-aux! (&rest args)
    `(binder (greedy-max-sat-aux . ,args)))
  (defthm greedy-max-sat-aux-binder-rule
    (implies (equal ans (b* (((when (atom x)) nil)
                             (test (and (car x) assumption))
                             (sat (sat-check! sat-res sat-config test))
                             (new-assumption (if (eq sat :unsat) assumption test))
                             (rest (greedy-max-sat-aux!
                                    ans1 (cdr x) sat-config (+ 1 (nfix start-index))
                                    new-assumption)))
                          (if (eq sat :unsat)
                              rest
                            (cons (nfix start-index) rest))))
             (equal (greedy-max-sat-aux ans x sat-config start-index assumption) ans))
    :hints(("Goal" :in-theory (enable sat-check-raw)
            :Expand ((len x)))))

  (add-fgl-brewrite greedy-max-sat-aux-binder-rule))

(define greedy-max-sat (ans x sat-config)
  :verify-guards nil
  (declare (ignore sat-config))
  (if (implies (indices-all-true ans x)
               (non-indices-all-false ans x))
      ans
    (numlist 0 1 (len x)))
  ///
  (defmacro greedy-max-sat! (&rest args)
    `(binder (greedy-max-sat . ,args)))

  (defthm greedy-max-sat-correct
    (let ((ans (greedy-max-sat ans x sat-config)))
      (implies (indices-all-true ans x)
               (non-indices-all-false ans x))))

  (defthm greedy-max-sat-empty-implies
    (implies (not (greedy-max-sat ans x sat-config))
             (not (nth n x)))
    :hints (("goal" :expand ((numlist 0 1 (len x)))
             :in-theory (enable member)
             :use ((:instance non-indices-all-false-necc
                    (indices nil)
                    (idx n))))))

  (defthm greedy-max-sat-binder-rule
    (implies (equal ans (greedy-max-sat-aux! ans2 x sat-config 0 t))
             (equal (greedy-max-sat ans x sat-config)
                    ans))
    :hints(("Goal" :in-theory (enable greedy-max-sat-aux))))

  (add-fgl-brewrite greedy-max-sat-binder-rule))


