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

(in-package "STR")
(include-book "std/basic/defs" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))


(local (defthm character-listp-of-make-character-list
         (character-listp (make-character-list x))))

(local (defthm coerce-inverse-better
         (equal (coerce (coerce x 'string) 'list)
                (make-character-list x))
         :hints (("goal" :use ((:instance acl2::completion-of-coerce
                                (x x) (y 'string)))))))

(local (defthm equal-of-coerce-string
         (equal (equal (coerce x 'string) (coerce y 'string))
                (equal (make-character-list x)
                       (make-character-list y)))
         :hints (("goal" :use ((:instance coerce-inverse-better
                                (x (make-character-list x)))
                               (:instance coerce-inverse-better
                                (x (make-character-list y)))
                               (:instance acl2::completion-of-coerce
                                (x x) (y 'string))
                               (:instance acl2::completion-of-coerce
                                (x y) (y 'string)))
                  :in-theory (disable coerce-inverse-better)
                  :do-not-induct t))
         :otf-flg t))


(local (defthm coerce-of-str-fix
         (equal (coerce (str-fix x) 'list)
                (coerce x 'list))
         :hints(("Goal" :in-theory (enable str-fix)
                 :use ((:instance acl2::completion-of-coerce
                        (y 'list)))))))

(defsection strrange-equiv
  (defund strrange-equiv (len x xidx y yidx)
    (declare (xargs :guard (and (stringp x)
                                (stringp y)
                                (natp xidx)
                                (natp yidx)
                                (natp len)
                                (<= (+ len xidx) (length x))
                                (<= (+ len yidx) (length y)))
                    :measure (nfix len)))
    (if (zp len)
        t
      (and (eql (mbe :logic (char-fix (char x xidx)) :exec (char x xidx))
                (mbe :logic (char-fix (char y yidx)) :exec (char y yidx)))
           (strrange-equiv (1- len)
                           x (+ 1 (lnfix xidx))
                           y (+ 1 (lnfix yidx))))))

  (local (in-theory (enable strrange-equiv)))

  (local (include-book "std/lists/take" :dir :system))
  (local (include-book "std/lists/nthcdr" :dir :system))

  (local (in-theory (disable nth nthcdr acl2::take
                             acl2::take-of-len-free nfix)))

  (local (defthm make-character-list-redef
           (equal (make-character-list x)
                  (if (atom x)
                      nil
                    (cons (char-fix (car x))
                          (make-character-list (cdr x)))))
           :rule-classes ((:definition :controller-alist ((make-character-list t))))))

  (defthmd strrange-equiv-equals-charlist-subseqs-equal
    (equal (strrange-equiv len x xidx y yidx)
           (equal (make-character-list (take len (nthcdr xidx (coerce x 'list))))
                  (make-character-list (take len (nthcdr yidx (coerce y 'list))))))
    :hints (("goal" :induct (strrange-equiv len x xidx y yidx)
             :expand ((:free (x) (take len x))
                      (:free (x) (nth xidx x))
                      (:free (x) (nth yidx x))
                      (:free (x y) (nthcdr (+ 1 x) y)))
             :do-not-induct t)))


  (defthmd strrange-equiv-equals-subseqs-equal
    (equal (strrange-equiv len x xidx y yidx)
           (equal (subseq (str-fix x) (nfix xidx) (+ (nfix len) (nfix xidx)))
                  (subseq (str-fix y) (nfix yidx) (+ (nfix len) (nfix yidx)))))
    :hints(("Goal" :in-theory (enable strrange-equiv-equals-charlist-subseqs-equal
                                      subseq)
            :do-not-induct t))))
