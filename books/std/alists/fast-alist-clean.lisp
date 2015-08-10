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
; Original authors: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)
(include-book "alist-keys")
(include-book "alist-fix")
(include-book "hons-remove-assoc")
(include-book "hons-assoc-equal")
(local (include-book "std/lists/append" :dir :system))

(defsection fast-alist-fork-basics
  (defthm hons-assoc-equal-in-fast-alist-fork
    (equal (hons-assoc-equal k (fast-alist-fork x y))
           (or (hons-assoc-equal k y)
               (hons-assoc-equal k x))))

  (defthm alistp-of-fast-alist-fork
    (implies (alistp y)
             (alistp (fast-alist-fork x y))))

  (defthm fast-alist-fork-of-alist-fix
    (equal (fast-alist-fork (alist-fix x) y)
           (fast-alist-fork x y)))

  (defthm alist-fix-of-fast-alist-fork
    (equal (alist-fix (fast-alist-fork x y))
           (fast-alist-fork x (alist-fix y)))))

(defsection hons-remove-assocs

  (defund hons-remove-assocs (keys al)
    ;; NOTE: Slow.
    (declare (xargs :guard t))
    (if (atom keys)
        (alist-fix al)
      (hons-remove-assoc
       (car keys)
       (hons-remove-assocs (cdr keys) al))))

  (local (in-theory (enable hons-remove-assocs)))

  (defthm hons-assoc-equal-remove-assocs
    (equal (hons-assoc-equal k (hons-remove-assocs keys al))
           (and (not (member k keys))
                (hons-assoc-equal k al))))

  (defthm hons-remove-assocs-of-cons-key
    (equal (hons-remove-assocs (cons k keys) al)
           (hons-remove-assoc k (hons-remove-assocs keys al))))

  (defthm hons-remove-assocs-of-atom-keys
    (implies (not (consp keys))
             (equal (hons-remove-assocs keys al)
                    (alist-fix al)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm hons-remove-assocs-of-cons-al
    (equal (hons-remove-assocs keys (cons pair al))
           (if (and (consp pair)
                    (not (member (car pair) keys)))
               (cons pair (hons-remove-assocs keys al))
             (hons-remove-assocs keys al)))
    :hints (("goal" :induct (hons-remove-assocs keys al))))

  (defthm hons-remove-assocs-of-atom-al
    (implies (not (consp al))
             (equal (hons-remove-assocs keys al) nil))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm hons-remove-assocs-of-fast-alist-fork
    (equal (hons-remove-assocs y (fast-alist-fork x z))
           (fast-alist-fork (hons-remove-assocs y x) (hons-remove-assocs y z))))

  (defthm hons-remove-assocs-of-append
    (equal (hons-remove-assocs keys (append x y))
           (append (hons-remove-assocs keys x)
                   (hons-remove-assocs keys y))))

  (defthm hons-remove-assocs-of-hons-remove-assoc
    (equal (hons-remove-assocs keys (hons-remove-assoc k x))
           (hons-remove-assoc k (hons-remove-assocs keys x))))

  (defthm alistp-of-hons-remove-assocs
    (alistp (hons-remove-assocs keys x))))



(defsection fast-alist-clean

  (local (defthm hons-remove-assocs-of-equal-append
           (implies (equal x (append y z))
                    (equal (hons-remove-assocs keys x)
                           (append (hons-remove-assocs keys y)
                                   (hons-remove-assocs keys z))))))

  (defthm atom-of-cdr-last
    (atom (cdr (last x)))
    :rule-classes :type-prescription)


  (local
   (defun fast-alist-fork-redef-ind (x y)
     (if (atom x)
         y
       (if (or (atom (car x))
               (hons-assoc-equal (caar x) y))
           (fast-alist-fork-redef-ind (cdr x) y)
         (list (fast-alist-fork-redef-ind (cdr x) (cons (car x) y))
               (fast-alist-fork-redef-ind (cdr x) (list (car x))))))))

  (local
   (defthmd fast-alist-fork-in-terms-of-hons-remove-assocs
     (equal (fast-alist-fork x y)
            (append (hons-remove-assocs (alist-keys y) (fast-alist-fork x nil)) y))
     :hints (("goal" :induct (fast-alist-fork-redef-ind x y)
              :do-not-induct t))))

  (local (defthm last-of-cdr
           (implies (consp (cdr x))
                    (equal (last (cdr x))
                           (last x)))))

  (defthmd fast-alist-clean-by-remove-assoc
    (equal (fast-alist-clean x)
           (if (atom x)
               x
             (if (atom (car x))
                 (fast-alist-clean (cdr x))
               (append (hons-remove-assoc (caar x) (fast-alist-clean (cdr x)))
                       (cons (car x) (cdr (last x)))))))
    :hints (("goal" :use ((:instance fast-alist-fork-in-terms-of-hons-remove-assocs
                           (y (if (consp x) (cdr (last x)) nil)))
                          (:instance fast-alist-fork-in-terms-of-hons-remove-assocs
                           (y (list (car x))) (x (cdr x)))
                          (:instance fast-alist-fork-in-terms-of-hons-remove-assocs
                           (y (if (consp (cdr x)) (cdr (last x)) nil))
                           (x (cdr x))))
             :expand ((fast-alist-fork x x)
                      (fast-alist-fork x (cdr x))
                      (fast-alist-fork x nil))
             :do-not-induct t
             :in-theory (disable fast-alist-fork
                                 hons-remove-assocs-of-fast-alist-fork
                                 hons-remove-assoc-of-fast-alist-fork)))
    :rule-classes ((:definition :controller-alist ((fast-alist-clean t)))))

  (defthm fast-alist-clean-by-remove-assoc-ind
    t
    :rule-classes ((:induction :pattern (fast-alist-clean x)
                    :scheme (len x))))

  (defthm hons-assoc-equal-in-fast-alist-clean
    ;; this would be easy enough to prove by opening it up and using what we've
    ;; already proved about fast-alist-fork, but we'll try it the other way
    (equal (hons-assoc-equal k (fast-alist-clean x))
           (hons-assoc-equal k x))
    :hints (("goal" :in-theory (e/d (fast-alist-clean-by-remove-assoc)
                                    (fast-alist-clean)))))

  (defthm fast-alist-clean-of-nil
    ;; normally this would just execute but the executable-counterpart is turned off by default
    (equal (fast-alist-clean nil) nil)))
