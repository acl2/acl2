; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "defs")
(local (include-book "arithmetic"))


(defthmd rev-of-cdr-to-butlast
  (equal (rev (cdr x))
         (butlast (rev x) 1))
  :hints(("Goal" :in-theory (enable rev butlast))))



(defthm take-len-when-prefix
  (implies (prefixp a b)
           (equal (take (len a) a)
                  (take (len a) b)))
  :hints(("Goal" :in-theory (enable prefixp))))



(defsection prefix-len

  (defund prefix-len (a b)
    (declare (xargs :guard t))
    (cond ((or (atom a)
               (atom b))
           0)
          ((not (equal (car a) (car b)))
           0)
          (t
           (+ 1 (prefix-len (cdr a) (cdr b))))))

  (local (in-theory (enable prefix-len)))

  (defthm prefix-len-when-atom-left
    (implies (atom a)
             (equal (prefix-len a b)
                    0)))

  (defthm prefix-len-when-atom-right
    (implies (atom b)
             (equal (prefix-len a b)
                    0)))

  (defthm prefix-len-of-cons
    (equal (prefix-len (cons a x) b)
           (if (and (consp b)
                    (equal a (car b)))
               (+ 1 (prefix-len x (cdr b)))
             0)))


  (defthm prefix-len-when-prefixp
    (implies (prefixp a b)
             (equal (prefix-len a b)
                    (len a)))
    :hints(("Goal" :in-theory (enable prefixp))))

  (defthm prefix-len-upper-bound-1
    (<= (prefix-len a b)
        (len a))
    :rule-classes ((:rewrite) (:linear)))

  (defthm prefix-len-upper-bound-2
    (<= (prefix-len a b)
        (len b))
    :rule-classes ((:rewrite) (:linear)))

  (defthm prefixp-of-take-prefix-len-1
    (prefixp (take (prefix-len a b) a) a)
    :hints(("Goal" :in-theory (enable prefixp acl2::take))))

  (defthm prefixp-of-take-prefix-len-2
    (prefixp (take (prefix-len a b) a) b)
    :hints(("Goal" :in-theory (enable prefixp acl2::take))))

  (defthm prefix-len-of-take
    (implies (and (natp n)
                  (<= n (len x)))
             (equal (prefix-len a (take n x))
                    (if (< (prefix-len a x) n)
                        (prefix-len a x)
                      n)))
    :hints(("Goal" :in-theory (enable acl2::take))))

  (defthm prefix-len-of-butlast
    ;; The hyp is ugly, but butlast has terrible behavior when N is not a natural
    (implies (force (natp n))
             (equal (prefix-len a (butlast b n))
                    (if (> n (len b))
                        0
                      (let ((chopped-len (- (len b) n)))
                        (if (< (prefix-len a b) chopped-len)
                            (prefix-len a b)
                          chopped-len)))))
    :hints(("Goal" :in-theory (enable butlast)))))




(defsection recursive-butlast-1

  (defund recursive-butlast-1 (x)
    (if (atom x)
        nil
      (if (atom (cdr x))
          nil
        (cons (car x)
              (recursive-butlast-1 (cdr x))))))

  (local (in-theory (enable recursive-butlast-1)))

  (defthm recursive-butlast-1-when-atom
    (implies (atom x)
             (equal (recursive-butlast-1 x)
                    nil)))

  (defthm recursive-butlast-1-when-singleton
    (implies (atom (cdr x))
             (equal (recursive-butlast-1 x)
                    nil)))

  (defthm recursive-butlast-1-of-cons
    (equal (recursive-butlast-1 (cons a x))
           (if (atom x)
               nil
             (cons a (recursive-butlast-1 x)))))

  (encapsulate
    ()
    (local (defthm l0
             (implies (consp b)
                      (equal (butlast (cons a b) 1)
                             (cons a (butlast b 1))))
             :hints(("Goal" :in-theory (enable butlast)))))

    (defthm butlast-1-removal
      (equal (butlast a 1)
             (recursive-butlast-1 a)))))


(defthm equal-by-prefix-and-not-prefix-of-butlast
  (implies (and (not (prefixp a (recursive-butlast-1 b)))
                (prefixp a b)
                (true-listp a)
                (true-listp b))
           (equal (equal a b)
                  t))
  :hints(("Goal" :in-theory (enable recursive-butlast-1 prefixp)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))
