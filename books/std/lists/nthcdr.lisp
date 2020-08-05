; Nthcdr lemmas
; Copyright (C) 2005-2013 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>
;
; nthcdr.lisp
; This file was originally part of the Unicode library.

(in-package "ACL2")
(include-book "list-fix")
(local (include-book "take"))

(local (defthm equal-len-0
         (equal (equal (len x) 0)
                (atom x))))

(defsection std/lists/nthcdr
  :parents (std/lists nthcdr)
  :short "Lemmas about @(see nthcdr) available in the @(see std/lists)
library."

  (defthm nthcdr-when-zp
    (implies (zp n)
             (equal (nthcdr n x)
                    x)))

  (defthm nthcdr-when-atom
    (implies (atom x)
             (equal (nthcdr n x)
                    (if (zp n)
                        x
                      nil))))

  (defthm nthcdr-of-cons
    (equal (nthcdr n (cons a x))
           (if (zp n)
               (cons a x)
             (nthcdr (- n 1) x))))


  (encapsulate
    ()
    (local (defthm lemma
             (iff (true-listp (nthcdr n x))
                    (or (true-listp x)
                        (< (len x) (nfix n))))
             :hints(("Goal" :in-theory (enable nthcdr)))))

    (defthm true-listp-of-nthcdr
      (equal (true-listp (nthcdr n x))
             (or (true-listp x)
                 (< (len x) (nfix n))))
      :rule-classes ((:rewrite)
; Commented out by Matt K. after ACL2 Version 6.5 with the addition of new
; built-in rule true-listp-nthcdr-type-prescription.
;                    (:type-prescription :corollary (implies (true-listp x)
;                                                            (true-listp
;                                                             (nthcdr n x))))
                     )))

  (defthm len-of-nthcdr
    (equal (len (nthcdr n l))
           (nfix (- (len l) (nfix n))))
    :hints (("Goal" :in-theory (enable nthcdr))))

  (defthm consp-of-nthcdr
    (equal (consp (nthcdr n x))
           (< (nfix n) (len x)))
    :hints(("Goal" :in-theory (disable len-of-nthcdr)
            :use ((:instance len-of-nthcdr (l x)))
            :expand (len (nthcdr n x)))))

  (defthm open-small-nthcdr
    (implies (syntaxp (and (quotep n)
                           (natp (unquote n))
                           (< (unquote n) 5)))
             (equal (nthcdr n x)
                    (if (zp n)
                        x
                      (nthcdr (+ -1 n) (cdr x)))))
    :hints(("Goal" :in-theory (enable nthcdr))))


  ;; BOZO we haven't done much with acl2-count through the rest of the library.
  ;; centaur/vl/util/arithmetic has a nicer acl2-count rule about nthcdr than
  ;; this, but we'll need to tie into take stuff, too.  Later.

  (local (defthm acl2-count-of-cdr
           (implies (consp x)
                    (< (acl2-count (cdr x))
                       (acl2-count x)))
           :rule-classes :linear))

  (local (defthm acl2-count-of-cdr-weak
           (<= (acl2-count (cdr x))
               (acl2-count x))
           :rule-classes :linear))

  (local (defthm acl2-count-of-consp-positive
           (implies (consp x)
                    (< 0 (acl2-count x)))
           :rule-classes :linear))

  (defthm acl2-count-of-nthcdr-rewrite
    (equal (< (acl2-count (nthcdr n x))
              (acl2-count x))
           (if (zp n)
               nil
             (or (consp x)
                 (< 0 (acl2-count x))))))

  (defthm acl2-count-of-nthcdr-linear
    (implies (and (not (zp n))
                  (consp x))
             (< (acl2-count (nthcdr n x))
                (acl2-count x)))
    :rule-classes :linear)

  (defthm acl2-count-of-nthcdr-linear-weak
    (<= (acl2-count (nthcdr n x))
        (acl2-count x))
    :rule-classes :linear)



  (defthm car-of-nthcdr
    (equal (car (nthcdr i x))
           (nth i x)))

  (defthm nthcdr-of-cdr
    (equal (nthcdr i (cdr x))
           (cdr (nthcdr i x))))

  (defthm nthcdr-when-less-than-len-under-iff
    (implies (< (nfix n) (len x))
             (iff (nthcdr n x)
                  t)))

  (defthm nthcdr-of-nthcdr
    (equal (nthcdr a (nthcdr b x))
           (nthcdr (+ (nfix a) (nfix b)) x))
    :hints(("Goal" :induct (nthcdr b x))))


  (defthm append-of-take-and-nthcdr
    (implies (<= (nfix n) (len x))
             (equal (append (take n x)
                            (nthcdr n x))
                    x)))



  (defthm nthcdr-of-list-fix
    ;; This looks redundant with the list-equiv, but it's stronger since it
    ;; targets equal
    (equal (nthcdr n (list-fix x))
           (list-fix (nthcdr n x))))


  (def-listp-rule element-list-p-of-nthcdr
    (implies (element-list-p (double-rewrite x))
             (element-list-p (nthcdr n x))))


  (def-projection-rule nthcdr-of-elementlist-projection
    (equal (nthcdr n (elementlist-projection x))
           (elementlist-projection (nthcdr n x))))

  (encapsulate
    ()

    (local
     (defthm subsetp-trans
       (implies (and (subsetp x y) (subsetp y z))
                (subsetp x z))))

    (local
     (defthm
       subsetp-member
       (implies (and (member a x) (subsetp x y))
                (member a y))
       :rule-classes
       ((:rewrite)
        (:rewrite :corollary (implies (and (subsetp x y) (member a x))
                                      (member a y)))
        (:rewrite
         :corollary (implies (and (not (member a y)) (subsetp x y))
                             (not (member a x))))
        (:rewrite
         :corollary (implies (and (subsetp x y) (not (member a y)))
                             (not (member a x)))))))

    (defthm
      subsetp-of-nthcdr
      (subsetp-equal (nthcdr n l) l)
      :hints (("Goal" :induct (nthcdr n l)
               :in-theory
               (disable
                (:rewrite nthcdr-of-cons)
                (:rewrite nthcdr-when-atom)
                (:rewrite nthcdr-when-zp)
                (:rewrite open-small-nthcdr)))))))


(defsection rest-n
  :parents (std/lists nthcdr)
  :short "@(see rest-n) is identical to @(see nthcdr), but its guard does not
require @('(true-listp x)')."

  :long "<p><b>Reasoning Note.</b> We leave @('rest-n') enabled, so it will
just get rewritten into @('nthcdr').  You should typically never write a
theorem about @('rest-n'): write theorems about @('nthcdr') instead.</p>"

  (defun rest-n (n x)
    (declare (xargs :guard (natp n)))
    (mbe :logic (nthcdr n x)
         :exec
         (cond ((zp n)
                x)
               ((atom x)
                nil)
               (t
                (rest-n (- n 1) (cdr x)))))))
