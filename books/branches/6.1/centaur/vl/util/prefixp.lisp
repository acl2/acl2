; VL Verilog Toolkit
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "defs")
(local (include-book "arithmetic"))


(defthmd rev-of-cdr-to-butlast
  (equal (rev (cdr x))
         (butlast (rev x) 1))
  :hints(("Goal" :in-theory (enable rev butlast))))



(defthm take-len-when-prefix
  (implies (prefixp a b)
           (equal (simpler-take (len a) a)
                  (simpler-take (len a) b)))
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
    (prefixp (simpler-take (prefix-len a b) a) a)
    :hints(("Goal" :in-theory (enable prefixp simpler-take))))

  (defthm prefixp-of-take-prefix-len-2
    (prefixp (simpler-take (prefix-len a b) a) b)
    :hints(("Goal" :in-theory (enable prefixp simpler-take))))

  (defthm prefix-len-of-simpler-take
    (implies (and (natp n)
                  (<= n (len x)))
             (equal (prefix-len a (simpler-take n x))
                    (if (< (prefix-len a x) n)
                        (prefix-len a x)
                      n)))
    :hints(("Goal" :in-theory (enable simpler-take))))

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






