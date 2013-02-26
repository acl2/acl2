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

  (defthm equal-of-len-and-prefix-len
    (equal (equal (prefix-len a b) (len a))
           (prefixp a b))
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

  (defthm acl2-count-recursive-butlast-1
    (implies (consp x)
             (< (acl2-count (recursive-butlast-1 x))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (enable acl2-count))))

  (encapsulate
    ()
    (local (defthm l0
             (implies (consp b)
                      (equal (butlast (cons a b) 1)
                             (cons a (butlast b 1))))
             :hints(("Goal" :in-theory (enable butlast)))))

    (defthm butlast-1-removal
      (equal (butlast a 1)
             (recursive-butlast-1 a))))

  (defthmd rev-of-cdr-to-butlast
    (equal (rev (cdr x))
           (butlast (rev x) 1))
    :hints(("Goal" :in-theory (enable rev append butlast))))

  (defthmd butlast-to-rev-of-cdr
    (equal (recursive-butlast-1 (rev x))
           (rev (cdr x)))
    :hints(("Goal" :in-theory (enable rev-of-cdr-to-butlast))))

  (theory-invariant (incompatible (:rewrite rev-of-cdr-to-butlast)
                                  (:rewrite butlast-to-rev-of-cdr))))


(defthm equal-by-prefix-and-not-prefix-of-butlast
  (implies (and (not (prefixp a (recursive-butlast-1 b)))
                (prefixp a b)
                (force (true-listp a))
                (force (true-listp b)))
           (equal (equal a b)
                  t))
  :rule-classes ((:rewrite)
                 (:forward-chaining :trigger-terms ((prefixp a (recursive-butlast-1 b)))))
  :hints(("Goal" :in-theory (enable recursive-butlast-1 prefixp))))





(defsection all-prefixes

  (defund all-prefixes-aux (n x)
    (declare (xargs :guard (and (natp n)
                                (<= n (len x))
                                (true-listp x))))
    (if (zp n)
        (list nil)
      (cons (simpler-take n x)
            (all-prefixes-aux (- n 1) x))))

  (defund all-prefixes (x)
    (declare (xargs :guard (true-listp x)))
    (all-prefixes-aux (mbe :logic (len x) :exec (length x)) x))

  (local (defthm c0
           (implies (< (nfix n) (len a))
                    (equal (member-equal a (all-prefixes-aux n x))
                           nil))
           :hints(("Goal"
                   :in-theory (enable all-prefixes-aux)
                   :induct (all-prefixes-aux n x)))))

  (local (defthm c1
           (no-duplicatesp-equal (all-prefixes-aux n x))
           :hints(("Goal" :in-theory (enable all-prefixes-aux)))))

  (defthm no-duplicatesp-equal-of-all-prefixes
    (no-duplicatesp-equal (all-prefixes x))
    :hints(("Goal" :in-theory (enable all-prefixes))))

  (local (defthm l0
           (implies (and (member-equal p (all-prefixes-aux n x))
                         (natp n)
                         (<= n (len x)))
                    (prefixp p x))
           :hints(("Goal" :in-theory (enable all-prefixes-aux)))))

  (local (defthm l1
           (implies (member-equal p (all-prefixes x))
                    (prefixp p x))
           :hints(("Goal" :in-theory (enable all-prefixes)))))

  (local (defthm l2
           (implies (and (prefixp p x)
                         (true-listp p))
                    (equal (simpler-take (len p) x)
                           p))
           :hints(("Goal" :in-theory (enable prefixp simpler-take)))))

  (local (defthm l3
           (implies (and (prefixp p x)
                         (<= (len p) n)
                         (natp n)
                         (<= n (len x))
                         (true-listp p))
                    (member-equal p (all-prefixes-aux n x)))
           :hints(("Goal"
                   :in-theory (enable all-prefixes-aux)
                   :induct (all-prefixes-aux n x)
                   :do-not '(generalize fertilize eliminate-destructors)))))

  (local (defthm l4
           (implies (and (true-listp p)
                         (prefixp p x))
                    (member-equal p (all-prefixes x)))
           :hints(("Goal"
                   :use ((:instance l3 (p p) (n (len x)) (x x)))
                   :in-theory (enable all-prefixes)
                   :do-not '(generalize fertilize eliminate-destructors)
                   :do-not-induct t
                   ))))

  (local (defthm l5
           (implies (member-equal p (all-prefixes-aux n x))
                    (true-listp p))
           :hints(("Goal" :in-theory (enable all-prefixes-aux)))))

  (local (defthm l6
           (implies (member-equal p (all-prefixes x))
                    (true-listp p))
           :hints(("Goal" :in-theory (enable all-prefixes)))))

  (defthm member-equal-of-all-prefixes
    (iff (member-equal p (all-prefixes x))
         (and (true-listp p)
              (prefixp p x)))))




; BUCKET ALISTS
;
; A "bucket alist" is one that associates keys to lists of values (buckets).

(defsection hons-bucket-insert

  (defund hons-bucket-insert (key val alist)
    ;; Add VAL to the bucket associated with KEY
    (declare (xargs :guard t))
    (hons-acons key
                (cons val (cdr (hons-get key alist)))
                alist))

  (local (in-theory (enable hons-bucket-insert)))

  (defthm hons-assoc-equal-of-hons-bucket-insert
    (equal (hons-assoc-equal a (hons-bucket-insert key val alist))
           (if (equal a key)
               (cons key (cons val (cdr (hons-assoc-equal key alist))))
             (hons-assoc-equal a alist)))))


(defsection hons-multibucket-insert

  (defund hons-multibucket-insert (keys val alist)
    ;; Add VAL to the buckets associated with each KEY in KEYS.
    (declare (xargs :guard t))
    (if (atom keys)
        alist
      (let ((alist (hons-bucket-insert (car keys) val alist)))
        (hons-multibucket-insert (cdr keys) val alist))))

  (local (in-theory (enable hons-multibucket-insert)))

  (defthm hons-assoc-equal-of-hons-multibucket-insert
    ;; This forcing might sometimes be inappropriate.  However, I think it might
    ;; often be that you want to realize that this is a hyp you need to add.
    (implies (force (no-duplicatesp-equal keys))
             (equal (hons-assoc-equal a (hons-multibucket-insert keys val alist))
                    (if (member-equal a keys)
                        (cons a (cons val (cdr (hons-assoc-equal a alist))))
                      (hons-assoc-equal a alist))))))


(defsection prefix-hash-insert

  (defund prefix-hash-insert (key val alist)
    ;; Add VAL to the bucket for every prefix of KEY
    (declare (xargs :guard (true-listp key)))
    (hons-multibucket-insert (all-prefixes key) val alist))

  (local (in-theory (enable prefix-hash-insert)))

  (defthm hons-assoc-equal-of-prefix-hash-insert
    (equal (hons-assoc-equal a (prefix-hash-insert key val alist))
           (if (and (true-listp a)
                    (prefixp a key))
               (cons a (cons val (cdr (hons-assoc-equal a alist))))
             (hons-assoc-equal a alist)))))


