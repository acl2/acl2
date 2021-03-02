; Copyright (C) 2014-2015 Centaur Technology
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


(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "std/lists/index-of" :dir :system)
;; (include-book "std/osets/primitives" :dir :system)
(include-book "std/alists/alist-defuns" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/lists/sets" :dir :system))

(define dup-witness ((x true-listp))
  (if (atom x)
      nil
    (if (member-equal (car x) (cdr x))
        (car x)
      (dup-witness (cdr x))))
  ///

   ;; (local (defthmd no-duplicatesp-implies-not-member-cdr-member
   ;;          (implies (no-duplicatesp x)
   ;;                   (not (member k (cdr (member k x)))))))

   (defthmd no-duplicatesp-by-dup-witness
     (implies (let ((k (dup-witness x)))
                (not (member k (cdr (member k x)))))
              (no-duplicatesp x))
     :hints(("Goal" :in-theory (enable no-duplicatesp))))

   (defthm indices-of-dup-witness
     (implies (and (member j x)
                   (member k (cdr (member j x))))
              (equal (nth (+ 1
                             (index-of j x)
                             (index-of k (cdr (member j x))))
                          x)
                     k))
     :hints(("Goal" :in-theory (enable index-of nth)
             :induct (member j x))))

   (defund dup-index-1 (x)
     (index-of (dup-witness x) x))

   (defthm len-member
     (implies (member k x)
              (equal (len (cdr (member k x)))
                     (- (len x) (+ 1 (index-of k x)))))
     :hints(("Goal" :in-theory (enable index-of))))

   (defund dup-index-2 (x)
     (+ 1 (dup-index-1 x)
        (index-of (dup-witness x)
                        (cdr (member (dup-witness x) x)))))

   (defthmd no-duplicatesp-by-indices-of-dup-witness
     (implies (let* ((i (dup-index-1 x))
                     (j (dup-index-2 x)))
                (not (and (natp i)
                          (natp j)
                          (< i (len x))
                          (< j (len x))
                          (not (equal i j))
                          (equal (nth i x) (nth j x)))))
              (no-duplicatesp x))
     :hints (("Goal" :use no-duplicatesp-by-dup-witness
              :in-theory (enable dup-index-1
                                 dup-index-2)
              :do-not-induct t
              :cases ((member (Dup-witness x) x)))))

   (defthm dup-indices-unequal
     (not (equal (dup-index-1 x) (dup-index-2 x)))
     :hints(("Goal" :in-theory (enable dup-index-2)))))



(defsection duplicates
  (defthm remove-preserves-no-duplicates
    (implies (no-duplicatesp x)
             (no-duplicatesp (remove y x))))

  (defthm remove-when-not-member
    (implies (not (member k x))
             (equal (remove k x)
                    (list-fix x)))))

(define remove-later-duplicates (x)
  :verify-guards nil
  (if (atom x)
      nil
    (cons (car x)
          (remove-equal (car x)
                        (remove-later-duplicates (cdr x)))))
  ///
  (verify-guards remove-later-duplicates)

  (defcong list-equiv equal (remove-later-duplicates x) 1
    :hints (("goal" :induct (acl2::fast-list-equiv x x-equiv)
             :in-theory (enable (:i acl2::fast-list-equiv)))))

  (defthm remove-of-remove
    (equal (remove b (remove a c))
           (remove a (remove b c))))

  (defthm remove-later-of-remove
    (equal (remove-later-duplicates (remove a b))
           (remove a (remove-later-duplicates b))))

  (defthm remove-later-of-set-diff
    (equal (remove-later-duplicates (set-difference$ a b))
           (set-difference$ (remove-later-duplicates a) b)))

  (defthm set-difference-of-cons-second
    (equal (set-difference$ a (cons b c))
           (remove b (set-difference$ a c))))


  (local (defthm set-difference-of-atom
           (implies (not (consp a))
                    (list-equiv (set-difference$ b a)
                                b))))
  (local (defthm set-difference-of-remove-common
           (equal (set-difference$ (remove x a)
                                   (remove x b))
                  (set-difference$ a
                                   (cons x b)))))

  (local (defthm remove-equal-of-append
           (equal (remove a (append b c))
                  (append (remove a b) (remove a c)))))

  (local (defthm remove-of-equal-to-append
           (implies (equal b (append c d))
                    (equal (remove a b)
                           (append (remove a c)
                                   (remove a d))))))

  ;; (local (defun ind (a b)
  ;;          (if (atom a)
  ;;              b
  ;;            (ind (remove (car a) (cdr a))
  ;;                 (remove (car a) b)))))

  (defthm remove-later-duplicates-of-append
    (equal (remove-later-duplicates (append a b))
           (append (remove-later-duplicates a)
                   (set-difference$
                    (remove-later-duplicates b) a))))
    ;; :hints (("goal" :induct (ind a b)
    ;;          :expand ((:free (a b) (remove-later-duplicates (cons a b)))))))

  ;; Mihir M. mod: a subgoal hint was necessary below after list-fix was
  ;; migrated to the sources and renamed.

  ;; Matt K. comment: After tracing acl2::rewrite in a couple of ways, I
  ;; noticed that both the type-alist and linear pot are affected by the
  ;; ordering of two terms: one is (REMOVE-LATER-DUPLICATES (CDR X))), and the
  ;; other is either (ACL2::TRUE-LIST-FIX (CDR X)) after the change to list-fix
  ;; or (LIST-FIX (CDR X)) before that change.  It seems reasonable to assume
  ;; that this term-order change is responsible for the failure to prove this
  ;; theorem without hints.  Moreover, the proof fails if "Subgoal *1/3''" is
  ;; replaced by "Goal", so avoiding a subgoal hint isn't as trivial as that.
  ;; We can live with Mihir's fix, so that's what we'll do.

  (defthm remove-later-duplicates-when-no-duplicates
    (implies (no-duplicatesp x)
             (equal (remove-later-duplicates x)
                    (list-fix x)))
    :hints (("Subgoal *1/3''" :in-theory (e/d (list-equiv)
                                              (acl2::list-equiv-implies-equal-remove-2))
             :use (:instance acl2::list-equiv-implies-equal-remove-2
                             (acl2::a (car x))
                             (x (remove-later-duplicates (cdr x)))
                             (acl2::x-equiv (cdr x))))))

  (defthm no-duplicatesp-of-remove-later-duplicates
    (no-duplicatesp (remove-later-duplicates x)))
  )


(defthmd no-duplicates-of-append
  (equal (no-duplicatesp-equal (append a b))
         (and (no-duplicatesp-equal a)
              (no-duplicatesp-equal b)
              (not (intersection$ a b)))))


;; (local (defthm not-member-when-setp
;;          (implies (and (<< k (car x))
;;                        (set::setp x))
;;                   (not (member k x)))
;;          :hints(("Goal" :in-theory (enable set::setp
;;                                            <<-irreflexive
;;                                            <<-transitive)))))


;; (defthm no-duplicatesp-when-setp
;;   (implies (set::setp x)
;;            (no-duplicatesp x))
;;   :hints(("Goal" :in-theory (enable set::setp))))g



