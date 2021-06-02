; Centaur regular expression library
; Copyright (C) 2014 Centaur Technology
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

(in-package "ACRE")

(include-book "types")
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/alists/alist-keys" :dir :system)
(include-book "std/strings/ieqv" :dir :system)

(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/sets" :dir :system))

(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable take (tau-system))))

(local (xdoc::set-default-parents acre-internals))

(local (Defthm explode-of-str-fix
         (equal (acl2::explode (acl2::str-fix x))
                (acl2::explode x))))


(define rev-keys ((x alistp) (acc true-listp))
  :returns (keys true-listp)
  (if (atom x)
      (mbe :logic (list-fix acc) :exec acc)
    (rev-keys (cdr x)
              (mbe :logic (if (consp (car x))
                              (cons (caar x) acc)
                            acc)
                   :exec (cons (caar x) acc))))
  ///
  (defret rev-keys-is-revappend-of-keys
    (equal (rev-keys x acc)
           (revappend (alist-keys x) (list-fix acc)))))


(define undup-exec ((x true-listp) (acc alistp))
  :enabled t
  :returns (new-x true-listp)
  (if (atom x)
      (rev-keys (fast-alist-free acc) nil)
    (undup-exec (cdr x)
                (b* ((x1 (car x)))
                  (if (hons-get x1 acc)
                      acc
                    (hons-acons x1 nil acc))))))




(local (defthm set-difference-of-nil
         (equal (set-difference$ x nil)
                (list-fix x))
         :hints(("Goal" :in-theory (enable set-difference$)))))

(define undup ((x true-listp))
  :verify-guards nil
  :returns (new-x true-listp)
  ;; :prepwork ((local (include-book "centaur/misc/equal-sets" :dir :system)))
  (mbe :logic (if (atom x)
                  nil
                (cons (car x)
                      (undup (remove-equal (car x) (cdr x)))))
       :exec (undup-exec x nil))
  ///
  ;; (local (in-theory (disable acl2::revappend-removal)))
  (local (defthm set-diff-of-cons
           (equal (set-difference$ y (cons x z))
                  (remove x (set-difference$ y z)))
           :hints(("Goal" :in-theory (enable set-difference$ remove)))))
  (local (defthm set-difference$-of-list-fix
           (equal (set-difference$ (list-fix x) y)
                  (set-difference$ x y))
           :hints(("Goal" :in-theory (enable set-difference$)))))

  (defret undup-exec-is-undup
    (equal new-x
           (revappend (alist-keys acc)
                      (undup (set-difference-equal x (alist-keys acc)))))
    :hints(("Goal" :in-theory (enable revappend set-difference-equal alist-keys)
            :induct <call>
            :expand ((:free (a b) (undup (cons a b))))))
    :fn undup-exec)

  (verify-guards undup
    :hints (("goal" :expand ((:free (x y) (undup (cons x y)))))))

  (local (include-book "std/lists/remove" :dir :system))

  (acl2::def-listp-rule element-list-p-of-undup
    (implies (acl2::element-list-p x)
             (acl2::element-list-p (undup x))))

  (defret consp-of-undup
    (iff (consp new-x) (consp x)))

  (local (defthmd remove-of-remove
           (Equal (remove b (remove a x))
                  (remove a (remove b x)))
           :hints(("Goal" :in-theory (enable remove)))))

  (local (defthm remove-of-remove-same
           (Equal (remove a (remove a x))
                  (remove a x))))

  (defthm undup-of-remove
    (equal (remove k (undup x))
           (undup (remove k x)))
    :hints(("Goal" :in-theory (enable undup remove remove-of-remove)
            :induct (undup x)
            :expand ((:free (a b) (undup (cons a b)))))))

  (defthm undup-of-undup
    (equal (undup (undup x))
           (undup x))
    :hints(("Goal" :in-theory (enable undup)
            :induct (undup x)
            :expand ((:free (a b) (undup (cons a b)))))))

  (local (defun undup-of-append-ind (x y)
           (if (atom x)
               y
             (undup-of-append-ind (remove (car x) (Cdr x))
                                            (remove (car x) y)))))

  ;; (local (defthm set-difference-of-remove
  ;;          (equal (set-difference$ (remove k x) y)
  ;;                 (set-difference$ x (cons k y)))
  ;;          :hints(("Goal" :in-theory (enable set-difference$)))))

  (local (defthm set-difference-when-consp-second
           (implies (consp y)
                    (equal (set-difference$ x y)
                           (set-difference$ (remove (car y) x) (cdr y))))))

  (local (defthm set-difference-when-not-consp-second
           (implies (not (consp y))
                    (equal (set-difference$ x y)
                           (list-fix x)))
           :hints(("Goal" :in-theory (enable set-difference$)))))

  (local (defthm set-difference-of-remove-when-not-member
           (implies (not (member k x))
                    (equal (set-difference$ x (remove k y))
                           (set-difference$ x y)))
           :hints(("Goal" :in-theory (enable set-difference$)))))

  (local (in-theory (disable set-difference$ member)))

  (defthm undup-of-append
    (equal (undup (append x y))
           (append (undup x)
                   (undup (set-difference$ y x))))
    :hints(("Goal" :in-theory (enable undup)
            :induct (undup-of-append-ind x y)
            :expand ((undup x)
                     (:free (a b) (undup (cons a b))))
            :do-not '(preprocess))))

  (defthm member-of-undup
    (iff (member k (undup x))
         (member k x)))

  (defthm undup-under-set-equiv
    (set-equiv (undup x) x)
    :hints(("goal" :in-theory (enable acl2::set-unequal-witness-rw))))

  (local (Defthm set-difference-of-remove-when-member
           (implies (member a y)
                    (equal (set-difference$ (remove a x) y)
                           (set-difference$ x y)))
           :hints(("Goal" :in-theory (enable set-difference$)))))

  (defthm undup-of-set-difference
    (equal (undup (set-difference$ x y))
           (set-difference$ (undup x) y))
    :hints(("Goal" :in-theory (enable set-difference$)))))



(define undup-equiv ((x true-listp) (y true-listp))
  :enabled t
  ;; :prepwork ((local (include-book "centaur/misc/equal-sets" :dir :system)))
  (equal (undup x) (undup y))
  ///
  (defequiv undup-equiv)

  (defthm undup-under-undup-equiv
    (undup-equiv (undup x) x))

  (defthm append-of-undup-under-undup-equiv-1
    (undup-equiv (append (undup x) y)
                 (append x y))
    :hints(("Goal" :in-theory (enable undup))))

  (defthm append-of-undup-under-undup-equiv-2
    (undup-equiv (append x (undup y))
                 (append x y))
    :hints(("Goal" :in-theory (enable undup))))

  (defrefinement undup-equiv set-equiv
    :hints (("goal" :use ((:instance undup-under-set-equiv)
                          (:instance undup-under-set-equiv
                           (x y)))
             :in-theory (disable undup-under-set-equiv))))

  (defcong undup-equiv undup-equiv (append a b) 1
    :hints (("goal" :use ((:instance append-of-undup-under-undup-equiv-1
                           (x a) (y b))
                          (:instance append-of-undup-under-undup-equiv-1
                           (x a-equiv) (y b)))
             :in-theory (disable append-of-undup-under-undup-equiv-1))))

  (defcong undup-equiv undup-equiv (append a b) 2)
  (defcong undup-equiv undup-equiv (append a b) 2)

  (defcong undup-equiv equal (undup x) 1))


(defprod backref
  ((loc natp :rule-classes :type-prescription)
   (len natp :rule-classes :type-prescription))
  :layout :tree
  :hons t)

(defmap backref-alist :val-type backref :true-listp t)

(defprod matchstate
  ((index natp :rule-classes :type-prescription)
   (backrefs backref-alist))
  :layout :tree
  :hons t)

(deflist matchstatelist :elt-type matchstate :true-listp t)


(defprod matchmode
  ((case-insens booleanp :rule-classes :type-prescription))
  :layout :tree)

(define match-exact ((pat stringp)
                     (x stringp)
                     (index natp)
                     (mode matchmode-p))
  :returns (new-index maybe-natp :rule-classes :type-prescription)
  (b* ((index (lnfix index))
       (pat (lstrfix pat))
       (x (lstrfix x))
       ((matchmode mode))
       (patlen (strlen pat))
       (new-index (+ index patlen)))
    (and (<= new-index (strlen x))
         (if mode.case-insens
             (str::istreqv pat (subseq x index new-index))
           (equal pat (subseq x index new-index)))
         new-index))
  ///
  (defret bound-of-match-exact
    (implies new-index
             (<= (nfix index) new-index))
    :rule-classes :linear)

  (defret upper-bound-of-match-exact
    (implies new-index
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear))


(define matchstatelist-indices-gte ((n natp)
                                (x matchstatelist-p))
  :returns (gte)
  (if (atom x)
      t
    (and (<= (lnfix n) (matchstate->index (car x)))
         (matchstatelist-indices-gte n (cdr x))))
  ///
  (defret <fn>-implies-car
    (implies (and gte (consp x))
             (<= (nfix n) (matchstate->index (car x))))
    :rule-classes :linear)

  (defret <fn>-implies-cdr
    (implies gte
             (matchstatelist-indices-gte n (cdr x))))

  (defthm matchstatelist-indices-gte-of-append
    (iff (matchstatelist-indices-gte n (append x y))
         (and (matchstatelist-indices-gte n x)
              (matchstatelist-indices-gte n y))))

  (defthm matchstatelist-indices-gte-of-rev
    (iff (matchstatelist-indices-gte n (rev x))
         (matchstatelist-indices-gte n x))
    :hints(("Goal" :in-theory (enable rev))))

  (defthm matchstatelist-indices-gte-of-nil
    (matchstatelist-indices-gte n nil))

  (defthm matchstatelist-indices-gte-of-remove
    (implies (matchstatelist-indices-gte n x)
             (matchstatelist-indices-gte n (remove k x))))

  (defthm matchstatelist-indices-gte-of-undup
    (implies (matchstatelist-indices-gte n x)
             (matchstatelist-indices-gte n (undup x)))
    :hints(("Goal" :in-theory (enable undup))))

  (defthm matchstatelist-indices-gte-of-set-difference
    (implies (matchstatelist-indices-gte n x)
             (matchstatelist-indices-gte n (set-difference$ x y)))))

(define matchstatelist-indices-lte ((n natp)
                                (x matchstatelist-p))
  :returns (lte)
  (if (atom x)
      t
    (and (<= (matchstate->index (car x)) (lnfix n))
         (matchstatelist-indices-lte n (cdr x))))
  ///
  (defret <fn>-implies-car
    (implies (and lte (consp x))
             (<= (matchstate->index (car x)) (nfix n)))
    :rule-classes :linear)

  (defret <fn>-implies-cdr
    (implies lte
             (matchstatelist-indices-lte n (cdr x))))

  (defthm matchstatelist-indices-lte-of-append
    (iff (matchstatelist-indices-lte n (append x y))
         (and (matchstatelist-indices-lte n x)
              (matchstatelist-indices-lte n y))))

  (defthm matchstatelist-indices-lte-of-rev
    (iff (matchstatelist-indices-lte n (rev x))
         (matchstatelist-indices-lte n x))
    :hints(("Goal" :in-theory (enable rev))))

  (defthm matchstatelist-indices-lte-of-nil
    (matchstatelist-indices-lte n nil))

  (defthm matchstatelist-indices-lte-of-remove
    (implies (matchstatelist-indices-lte n x)
             (matchstatelist-indices-lte n (remove k x))))

  (defthm matchstatelist-indices-lte-of-undup
    (implies (matchstatelist-indices-lte n x)
             (matchstatelist-indices-lte n (undup x)))
    :hints(("Goal" :in-theory (enable undup))))

  (defthm matchstatelist-indices-lte-of-set-difference
    (implies (matchstatelist-indices-lte n x)
             (matchstatelist-indices-lte n (set-difference$ x y)))))

(define match-add-backref ((name)
                           (start-index natp)
                           (match matchstate-p))
  :guard (<= start-index (matchstate->index match))
  :returns (new-match matchstate-p)
  :prepwork ((local (defthm alistp-of-backref-alist
                      (implies (backref-alist-p x)
                               (alistp x))
                      :hints(("Goal" :in-theory (enable backref-alist-p))))))
  (b* (((matchstate match))
       (start-index (lnfix start-index))
       ((when (assoc-equal name match.backrefs))
        (matchstate-fix match)))
    (change-matchstate match
                       :backrefs (cons (cons name (make-backref :loc start-index :len (- match.index start-index)))
                                       match.backrefs)))
  ///
  (defret match-index-of-<fn>
    (equal (matchstate->index new-match)
           (matchstate->index match))))


(define matches-add-backref ((name)
                             (start-index natp)
                             (matches matchstatelist-p))
  :guard (matchstatelist-indices-gte start-index matches)
  :returns (new-matches matchstatelist-p)
  :prepwork ((local (in-theory (enable matchstatelist-indices-gte))))
  (if (atom matches)
      nil
    (cons (match-add-backref name start-index (car matches))
          (matches-add-backref name start-index (cdr matches))))
  ///
  (defret <fn>-preserves-matchstatelist-indices-gte
    (implies (matchstatelist-indices-gte n matches)
             (matchstatelist-indices-gte n new-matches)))

  (defret consp-of-<fn>
    (equal (consp new-matches) (consp matches)))

  (defthm matchstatelist-indices-gte-of-add-backref
    (iff (matchstatelist-indices-gte n (matches-add-backref name start x))
         (matchstatelist-indices-gte n x))
    :hints(("Goal" :in-theory (enable matchstatelist-indices-gte))))

  (defthm matchstatelist-indices-lte-of-add-backref
    (iff (matchstatelist-indices-lte n (matches-add-backref name start x))
         (matchstatelist-indices-lte n x))
    :hints(("Goal" :in-theory (enable matchstatelist-indices-lte)))))




(define matchstatelist-min-index ((sts matchstatelist-p))
  :guard (consp sts)
  :returns (index natp :rule-classes :type-prescription)
  (if (atom (cdr sts))
      (matchstate->index (car sts))
    (min (matchstate->index (car sts))
         (matchstatelist-min-index (cdr sts))))
  ///
  (defthmd matchstatelist-min-index-of-append
    (implies (or (consp a) (consp b))
             (equal (matchstatelist-min-index (append a b))
                    (if (consp a)
                        (if (consp b)
                            (min (matchstatelist-min-index a)
                                 (matchstatelist-min-index b))
                          (matchstatelist-min-index a))
                      (matchstatelist-min-index b))))
    :hints(("Goal" :in-theory (enable matchstatelist-min-index))))

  (defthm matchstatelist-min-index-of-rev
    (equal (matchstatelist-min-index (rev x))
           (matchstatelist-min-index x))
    :hints(("Goal" :in-theory (enable matchstatelist-min-index-of-append rev))))

  (defthm matchstatelist-min-index-of-matches-add-backref
    (equal (matchstatelist-min-index (matches-add-backref name start-index matches))
           (matchstatelist-min-index matches))
    :hints(("Goal" :in-theory (enable matches-add-backref))))

  (defthm matchstatelist-indices-gte-by-matchstatelist-min-index
    (implies (<= (nfix idx) (matchstatelist-min-index x))
             (matchstatelist-indices-gte idx x))
    :hints(("Goal" :in-theory (enable matchstatelist-indices-gte)))))



(define matchstate-measure ((x stringp)
                            (st matchstate-p))
  :returns (meas natp :rule-classes :type-prescription)
  (nfix (- (strlen x) (matchstate->index st))))


(define matchstatelist-measure ((x stringp)
                                (sts matchstatelist-p))
  :returns (meas natp :rule-classes :type-prescription)
  (if (atom sts)
      0
    (max (matchstate-measure x (car sts))
         (matchstatelist-measure x (cdr sts))))
  ///
  (defret matchstatelist-measure-gte-car
    (implies (consp sts)
             (<= (matchstate-measure x (car sts)) meas))
    :hints(("Goal" :in-theory (enable matchstate-measure
                                      matchstatelist-min-index)))
    :rule-classes :linear)

  (defret matchstatelist-measure-gte-cdr
    (implies (consp sts)
             (<= (matchstatelist-measure x (cdr sts)) meas))
    :hints(("Goal" :in-theory (enable matchstatelist-min-index)))
    :rule-classes :linear)

  (defthm matchstatelist-measure-of-append
    (equal (matchstatelist-measure x (append a b))
           (max (matchstatelist-measure x a)
                (matchstatelist-measure x b))))

  (defthm matchstatelist-measure-of-nil
    (equal (matchstatelist-measure x nil) 0))

  (defthm matchstatelist-measure-of-rev
    (equal (matchstatelist-measure x (rev sts))
           (matchstatelist-measure x sts))
    :hints(("Goal" :in-theory (enable rev))))

  (Defthm matchstatelist-meassure-of-matches-add-backref
    (equal (matchstatelist-measure x (matches-add-backref name start sts))
           (matchstatelist-measure x sts))
    :hints(("Goal" :in-theory (enable matches-add-backref matchstate-measure))))

  (defthm matchstatelist-measure-of-remove
    (<= (matchstatelist-measure x (remove k sts)) (matchstatelist-measure x sts))
    :rule-classes :linear)

  (defthm matchstatelist-measure-of-set-diff
    (<= (matchstatelist-measure x (set-difference$ sts y)) (matchstatelist-measure x sts))
    :rule-classes :linear)

  (defthm matchstatelist-measure-of-remove-strong-1
    (implies (< (matchstatelist-measure x y) (matchstate-measure x k))
             (equal (matchstatelist-measure x (remove k y))
                    (matchstatelist-measure x y))))

  (defthm matchstatelist-measure-of-remove-strong-2
    (implies (< (matchstate-measure x k) (matchstatelist-measure x y))
             (equal (matchstatelist-measure x (remove k y))
                    (matchstatelist-measure x y))))

  ;; (defthm matchstatelist-measure-of-remove-less-than-removed
  ;;   (implies (<= (matchstate-measure x k) (matchstatelist-measure x (remove k y)))
  ;;            (equal (matchstatelist-measure x (remove k y))
  ;;                   (matchstatelist-measure x y))))


  (local (defthm undup-of-remove-rev
           (equal (undup (remove k x))
                  (remove k (undup x)))))

  (local (in-theory (disable undup-of-remove)))

  (defthm matchstatelist-measure-of-undup
    (equal (matchstatelist-measure x (undup sts)) (matchstatelist-measure x sts))
    :hints(("Goal" :in-theory (enable undup)
            :induct (matchstatelist-measure x sts)
            :expand ((undup sts)))
           (and stable-under-simplificationp
                '(:cases ((< (matchstate-measure x (car sts)) (matchstatelist-measure x (cdr sts)))
                          (< (matchstatelist-measure x (cdr sts)) (matchstate-measure x (car sts))))))))



  (defcong undup-equiv equal (matchstatelist-measure x sts) 2
    :hints (("goal" :use ((:instance matchstatelist-measure-of-undup)
                          (:instance matchstatelist-measure-of-undup
                           (sts sts-equiv)))
             :in-theory (disable matchstatelist-measure-of-undup)))))

(define matches-remove-zero-length ((start-index natp)
                                    (matches matchstatelist-p))
  :returns (new-matches matchstatelist-p)
  (if (atom matches)
      nil
    (if (< (lnfix start-index) (matchstate->index (car matches)))
        (cons (matchstate-fix (car matches))
              (matches-remove-zero-length start-index (cdr matches)))
      (matches-remove-zero-length start-index (cdr matches))))
  ///
  ;; (defret matchstatelist-min-index-of-<fn>
  ;;   (implies (consp new-matches)
  ;;            (< (nfix start-index) (matchstatelist-min-index new-matches)))
  ;;   :hints(("Goal" :in-theory (enable matchstatelist-min-index)))
  ;;   :rule-classes :linear)

  (defret matchstatelist-measure-of-<fn>
    (implies (< (nfix start-index) (strlen x))
             (< (matchstatelist-measure x new-matches)
                (- (strlen x) (nfix start-index))))
    :hints(("Goal" :in-theory (e/d (matchstatelist-measure matchstate-measure))))
    :rule-classes :linear)

  (defthm matchstatelist-measure-of-matches-remove-zero-length-of-matchstate->index
    (b* ((new-matches (matches-remove-zero-length (matchstate->index st) matches)))
      (implies (< (matchstate->index st) (strlen x))
               (< (matchstatelist-measure x new-matches)
                  (matchstate-measure x st))))
    :hints(("Goal" :in-theory (e/d (matchstate-measure)
                                   (matches-remove-zero-length
                                       matchstatelist-measure-of-matches-remove-zero-length))
            :use ((:instance matchstatelist-measure-of-matches-remove-zero-length
                   (start-index (matchstate->index st))))))
    :rule-classes :linear)

  (defthm matchstatelist-measure-of-matches-remove-zero-length-of-matchstate->index-weak
    (b* ((new-matches (matches-remove-zero-length (matchstate->index st) matches)))
      (<= (matchstatelist-measure x new-matches)
          (matchstate-measure x st)))
    :hints(("Goal" :in-theory (e/d (matchstatelist-measure matchstate-measure))))
    :rule-classes :linear)

  (defthm matches-remove-zero-length-of-nil
    (equal (matches-remove-zero-length start-index nil) nil))

  (defret matches-remove-zero-length-preserves-gte
    (implies (matchstatelist-indices-gte n matches)
             (matchstatelist-indices-gte n new-matches))
    :hints(("Goal" :in-theory (enable matchstatelist-indices-gte))))

  (defret matches-remove-zero-length-preserves-lte
    (implies (matchstatelist-indices-lte n matches)
             (matchstatelist-indices-lte n new-matches))
    :hints(("Goal" :in-theory (enable matchstatelist-indices-lte)))))

;; (local (defthm coerce-list-of-str-fix
;;          (equal (coerce (acl2::str-fix x) 'list)
;;                 (coerce x 'list))
;;          :hints(("Goal" :in-theory (enable acl2::str-fix)))))

(define match-charset ((set stringp)
                       (set-index natp)
                       (char characterp)
                       (mode matchmode-p))
  :measure (nfix (- (strlen set) (nfix set-index)))
  :guard (<= set-index (strlen set))
  (b* ((set (lstrfix set))
       (set-index (lnfix set-index))
       ((matchmode mode))
       (char (mbe :logic (acl2::char-fix char) :exec char))
       ((when (mbe :logic (zp (- (strlen set) set-index))
                   :exec (eql set-index (strlen set))))
        nil)
       ((when (if mode.case-insens
                  (str::ichareqv (char set set-index) char)
                (eql (char set set-index) char)))
        t))
    (match-charset set (1+ set-index) char mode))
  ///
  (deffixequiv match-charset
    :hints (("goal" :expand ((:free (set) (match-charset set set-index char mode))
                             (:free (char) (match-charset set set-index char mode))
                             (match-charset set (nfix set-index) char mode))))))



(define backref-in-bounds ((x backref-p) (str stringp))
  (b* (((backref x)))
    (<= (+ x.loc x.len) (strlen str)))
  ///
  (defthm backref-in-bounds-of-make-backref
    (equal (backref-in-bounds (backref loc len) str)
           (<= (+ (nfix loc) (nfix len)) (strlen str)))))

(define backref-alist-in-bounds ((x backref-alist-p) (str stringp))
  (if (atom x)
      t
    (and (or (not (mbt (consp (car x))))
             (backref-in-bounds (cdar x) str))
         (backref-alist-in-bounds (cdr x) str)))
  ///
  (fty::deffixequiv backref-alist-in-bounds
    :hints(("Goal" :in-theory (enable backref-alist-fix))))

  (defthm backref-alist-in-bounds-of-cons
    (equal (backref-alist-in-bounds (cons (cons key backref) rest) str)
           (and (backref-in-bounds backref str)
                (backref-alist-in-bounds rest str))))

  (defthm backref-alist-in-bounds-of-nil
    (backref-alist-in-bounds nil str))

  (defthm backref-in-bounds-of-lookup
    (implies (and (backref-alist-in-bounds x str)
                  (cdr (assoc name x)))
             (backref-in-bounds (cdr (assoc name x)) str))))

(define matchstate-in-bounds ((st matchstate-p) (str stringp))
  (b* (((matchstate st)))
    (and (<= (matchstate->index st) (strlen str))
         (backref-alist-in-bounds st.backrefs str)))
  ///
  (defthm matchstate-in-bounds-of-make-matchstate
    (equal (matchstate-in-bounds (make-matchstate :index index :backrefs backrefs) str)
           (and (<= (nfix index) (strlen str))
                (backref-alist-in-bounds backrefs str))))

  (defthm matchstate-in-bounds-implies-backref-alist-in-bounds
    (implies (matchstate-in-bounds st str)
             (backref-alist-in-bounds (matchstate->backrefs st) str)))

  (defthm matchstate-in-bounds-implies-index-in-bounds
    (implies (matchstate-in-bounds st str)
             (<= (matchstate->index st) (len (acl2::explode str))))
    :rule-classes ((:linear :trigger-terms ((matchstate->index st))))))

(define matchstatelist-in-bounds ((sts matchstatelist-p) (str stringp))
  (if (atom sts)
      t
    (and (matchstate-in-bounds (car sts) str)
         (matchstatelist-in-bounds (cdr sts) str)))
  ///
  (defthm matchstatelist-in-bounds-of-cons
    (equal (matchstatelist-in-bounds (cons st rest) str)
           (and (matchstate-in-bounds st str)
                (matchstatelist-in-bounds rest str))))

  (defthm matchstatelist-in-bounds-of-nil
    (matchstatelist-in-bounds nil str))

  (defthm matchstatelist-in-bounds-of-remove
    (implies (matchstatelist-in-bounds sts x)
             (matchstatelist-in-bounds (remove st sts) x)))

  (defthm matchstatelist-in-bounds-of-set-diff
    (implies (matchstatelist-in-bounds sts x)
             (matchstatelist-in-bounds (set-difference$ sts sts2) x)))

  (defthm matchstatelist-in-bounds-of-undup
    (implies (matchstatelist-in-bounds sts x)
             (matchstatelist-in-bounds (undup sts) x))
    :hints(("Goal" :in-theory (enable undup))))

  (defthm matchstatelist-in-bounds-of-append
    (implies (and (matchstatelist-in-bounds a x)
                  (matchstatelist-in-bounds b x))
             (matchstatelist-in-bounds (append a b) x)))

  (defthm matchstatelist-in-bounds-of-rev
    (implies (matchstatelist-in-bounds sts x)
             (matchstatelist-in-bounds (rev sts) x)))

  (defthm matchstatelist-in-bounds-of-matches-add-backref
    (implies (and (matchstatelist-in-bounds sts str)
                  (matchstatelist-indices-gte index sts))
             (matchstatelist-in-bounds
              (matches-add-backref name index sts)
              str))
    :hints(("Goal" :in-theory (enable matches-add-backref matchstatelist-indices-gte
                                      matchstate-in-bounds
                                      match-add-backref))))

  (defthm matchstatelist-in-bounds-of-remove-zero-length
    (implies (matchstatelist-in-bounds sts str)
             (matchstatelist-in-bounds (matches-remove-zero-length index sts) str))
    :hints(("Goal" :in-theory (enable matches-remove-zero-length))))

  (defthm matchstate-in-bounds-of-car-of-matchstatelist
    (implies (and (matchstatelist-in-bounds sts str)
                  (consp sts))
             (matchstate-in-bounds (car sts) str))))






(defines match-regex-rec
  :flag-local nil
  (define match-regex-rec ((pat regex-p)
                           (x stringp)
                           (st matchstate-p)
                           (mode matchmode-p))
    :guard (matchstate-in-bounds st x)
    :measure (list (regex-count pat) 0 (matchstate-measure x st) 0)
    :well-founded-relation acl2::nat-list-<
    :verify-guards nil
    :returns (matches matchstatelist-p)
    :prepwork (;; (local (include-book "centaur/misc/equal-sets" :dir :system))
               (local (defthm maybe-natp-fix-when-x
                        (implies x (equal (maybe-natp-fix x) (nfix x)))
                        :hints(("Goal" :in-theory (enable maybe-natp-fix))))))
    (b* ((x (mbe :logic (acl2::str-fix x) :exec x))
         ((matchstate st) (matchstate-fix st)))
      (regex-case pat
        :exact (b* ((new-idx (match-exact pat.str x st.index mode)))
                 (and new-idx
                      (list (change-matchstate st :index new-idx))))
        ;; ((pat regex)
        ;; (min acl2::maybe-natp)
        ;; (max acl2::maybe-natp))
        :repeat (match-repeat-rec pat.max pat.min pat.pat x st mode)

        :concat (match-concat-rec pat.lst x st mode)

        :disjunct (undup (match-disjunct-rec pat.lst x st mode))

        :charset (b* (;; charset has to match something, so we can't be past the end
                      ((unless (< st.index (strlen x))) nil))
                   (and (xor (match-charset pat.chars 0 (char x st.index) mode) pat.negp)
                        (list (change-matchstate st :index (+ 1 st.index)))))


        :start (and (eql st.index 0)
                    (list st))

        :end (and (eql st.index (strlen x))
                  (list st))

        :group (b* ((rec-matches (match-regex-rec pat.pat x st mode)))
                 (matches-add-backref pat.index st.index rec-matches))

        :backref (b* ((backref (cdr (assoc-equal pat.index st.backrefs)))
                      ((unless backref) nil)
                      ((backref backref))
                      (str (and (<= backref.loc (strlen x))
                                (<= (+ backref.loc backref.len) (strlen x))
                                (subseq x backref.loc (+ backref.loc backref.len))))
                      ((unless str) nil)
                      (new-idx (match-exact str x st.index mode)))
                   (and new-idx
                        (list (change-matchstate st :index new-idx))))

        :reverse-pref (b* ((rec-matches (match-regex-rec pat.pat x st mode)))
                        (rev rec-matches))

        :no-backtrack (b* ((rec-matches (match-regex-rec pat.pat x st mode)))
                        (and (consp rec-matches)
                             (list (car rec-matches))))

        :case-sens (b* ((mode (change-matchmode mode :case-insens pat.case-insens)))
                     (match-regex-rec pat.pat x st mode))

        :zerolength (b* ((back-index (- st.index pat.lookback))
                         ((when (< back-index 0)) nil)
                         (back-st (change-matchstate st :index back-index))
                         (rec-matches (match-regex-rec pat.pat x back-st mode)))
                      (and (xor (consp rec-matches) pat.negp)
                           (list st))))))

  (define match-concat-rec ((pat regexlist-p)
                            (x stringp)
                            (st matchstate-p)
                            (mode matchmode-p))
    :returns (matches matchstatelist-p)
    :guard (matchstate-in-bounds st x)
    :measure (list (regexlist-count pat) 0 (matchstate-measure x st) 0)
    (b* ((st (matchstate-fix st))
         ((when (atom pat))
          (list st))
         (matches (match-regex-rec (car pat) x st mode)))
      (undup (match-concat-sts-rec (cdr pat) x matches mode))))

  (define match-concat-sts-rec ((pat regexlist-p)
                                (x stringp)
                                (sts matchstatelist-p)
                                (mode matchmode-p))
    :guard (matchstatelist-in-bounds sts x)
    :returns (matches matchstatelist-p)
    :measure (list (regexlist-count pat) 0 (matchstatelist-measure x sts) (len sts))
    (if (atom sts)
        nil
      (append (match-concat-rec pat x (car sts) mode)
              (match-concat-sts-rec pat x (cdr sts) mode))))

  (define match-disjunct-rec ((pat regexlist-p)
                              (x stringp)
                              (st matchstate-p)
                              (mode matchmode-p))
    :guard (matchstate-in-bounds st x)
    :returns (matches matchstatelist-p)
    :measure (list (regexlist-count pat) 0 (matchstate-measure x st) 0)
    (b* (((when (atom pat))
          nil)
         (matches1 (match-regex-rec (car pat) x st mode))
         (matches2 (match-disjunct-rec (cdr pat) x st mode)))
      (append matches1 matches2)))

  (define match-regex-sts-nonzero-rec ((pat regex-p)
                                       (x stringp)
                                       (sts matchstatelist-p)
                                       (mode matchmode-p))
    :guard (matchstatelist-in-bounds sts x)
    :returns (matches matchstatelist-p)
    :measure (list (regex-count pat) 0 (matchstatelist-measure x sts) (len sts))
    (if (atom sts)
        nil
      (append (b* (((matchstate st1) (car sts))
                   ((unless (< st1.index (strlen x))) nil)
                   (matches (match-regex-rec pat x (car sts) mode)))
                (matches-remove-zero-length st1.index matches))
              (match-regex-sts-nonzero-rec pat x (cdr sts) mode))))

  (define match-regex-sts-rec ((pat regex-p)
                               (x stringp)
                               (sts matchstatelist-p)
                               (mode matchmode-p))
    :guard (matchstatelist-in-bounds sts x)
    :returns (matches matchstatelist-p)
    :measure (list (regex-count pat) 0 (matchstatelist-measure x sts) (len sts))
    (if (atom sts)
        nil
      (append (match-regex-rec pat x (car sts) mode)
              (match-regex-sts-rec pat x (cdr sts) mode))))


  (define match-repeat-sts-minimum-rec ((min natp)
                                        (pat regex-p)
                                        (x stringp)
                                        (sts matchstatelist-p)
                                        (mode matchmode-p))
    :guard (matchstatelist-in-bounds sts x)
    :returns (matches matchstatelist-p)
    :measure (list (regex-count pat) 1 (matchstatelist-measure x sts) min)
    (b* ((min (lnfix min))
         ((when (eql min 0))
          (matchstatelist-fix sts))
         (next-sts (undup
                    (match-regex-sts-rec pat x sts mode)))
         ((unless (consp next-sts)) nil)
         ((unless (mbt (<= (matchstatelist-measure x next-sts)
                           (matchstatelist-measure x sts))))
          nil))
      (match-repeat-sts-minimum-rec (1- min) pat x next-sts mode)))

  (define match-repeat-sts-rec ((max maybe-natp)
                                (pat regex-p)
                                (x stringp)
                                (sts matchstatelist-p)
                                (mode matchmode-p))
    :guard (matchstatelist-in-bounds sts x)
    :returns (matches matchstatelist-p)
    :measure (list (regex-count pat) 1 (matchstatelist-measure x sts) max)
    (b* ((max (maybe-natp-fix max))
         (base-matches (matchstatelist-fix sts))
         ((when (eql max 0))
          base-matches)
         (next-sts (undup
                    (if max
                        (match-regex-sts-rec pat x sts mode)
                      (match-regex-sts-nonzero-rec pat x sts mode))))
         ((unless (consp next-sts)) base-matches)
         ((unless (mbt (if max
                           (<= (matchstatelist-measure x next-sts)
                               (matchstatelist-measure x sts))
                         (< (matchstatelist-measure x next-sts)
                            (matchstatelist-measure x sts)))))
          base-matches)
         (rest-sts (match-repeat-sts-rec (and max (1- max))
                                         pat x next-sts mode)))
      (append rest-sts base-matches)))

  (define match-repeat-sts-rec-exec ((max maybe-natp)
                                     (pat regex-p)
                                     (x stringp)
                                     (sts matchstatelist-p)
                                     (mode matchmode-p)
                                     (acc matchstatelist-p))
    :enabled t
    :guard (matchstatelist-in-bounds sts x)
    :measure (list (regex-count pat) 2 (matchstatelist-measure x sts) max)
    (mbe :logic (append (match-repeat-sts-rec max pat x sts mode)
                        (matchstatelist-fix acc))
         :exec
         (b* ((max (maybe-natp-fix max))
              (acc (matchstatelist-fix acc))
              (base-matches (matchstatelist-fix sts))
              (new-acc (append base-matches acc))
              ((when (eql max 0)) new-acc)
              (next-sts (undup
                         (if max
                             (match-regex-sts-rec pat x sts mode)
                           (match-regex-sts-nonzero-rec pat x sts mode))))
              ((when (atom next-sts)) new-acc)
              ((unless (mbt (if max
                                (<= (matchstatelist-measure x next-sts)
                                   (matchstatelist-measure x sts))
                              (< (matchstatelist-measure x next-sts)
                                 (matchstatelist-measure x sts)))))
               new-acc))
           (match-repeat-sts-rec-exec (and max (1- max))
                                      pat x next-sts mode new-acc))))

  (define match-repeat-rec ((max maybe-natp)
                            (min natp)
                            (pat regex-p)
                            (x stringp)
                            (st matchstate-p)
                            (mode matchmode-p))
    :guard (matchstate-in-bounds st x)
    :returns (matches matchstatelist-p)
    :measure (list (regex-count pat) 3 (matchstate-measure x st) 0)
    (b* ((min-matches (match-repeat-sts-minimum-rec min pat x (list st) mode))
         (max (maybe-natp-fix max))
         (max (and max (nfix (- max (lnfix min)))))
         (matches (mbe :logic (match-repeat-sts-rec max pat x min-matches mode)
                       :exec (match-repeat-sts-rec-exec max pat x min-matches mode nil)))
         ((when max) (undup matches))
         ;; allow a single zero-length match for the last one
         (last-matches (match-regex-sts-rec pat x matches mode)))
      (undup (append last-matches matches)))

    ;; (b* ((max (maybe-natp-fix max))
    ;;      (min (lnfix min))
    ;;      (base-matches (and (eql min 0) (list (matchstate-fix st))))
    ;;      ((when (eql max 0)) base-matches)
    ;;      (next-sts (match-regex-rec pat x st))
    ;;      ((unless (consp next-sts)) base-matches)
    ;;      ((unless (mbt (<= (matchstatelist-measure x next-sts) (matchstate-measure x st))))
    ;;       base-matches))
    ;;   (mbe :logic (append (match-repeat-sts-rec (and max (1- max))
    ;;                                             (if (eql 0 min) 0 (1- min))
    ;;                                             pat x next-sts)
    ;;                       base-matches)
    ;;        :exec (match-repeat-sts-rec-exec  (and max (1- max))
    ;;                                          (if (eql 0 min) 0 (1- min))
    ;;                                          pat x next-sts base-matches)))
    )


  ///

  (local (make-event
          `(defconst *match-regex-fns*
             ',(remove 'match-repeat-sts-rec-exec
                       (acl2::getpropc 'match-regex-rec 'acl2::recursivep nil (w state))))))

  (local (make-event `(in-theory (disable . ,*match-regex-fns*))))

  (local (defun match-regex-mr-fns (name body-when-takes-st body-when-takes-sts hints rule-classes fns wrld)
           (if (atom fns)
               nil
             (cons `(defret ,name
                      ,(if (member 'st (acl2::formals (car fns) wrld))
                           body-when-takes-st
                         body-when-takes-sts)
                      :hints ,hints :rule-classes ,rule-classes :fn ,(car fns))
                   (match-regex-mr-fns name body-when-takes-st body-when-takes-sts hints rule-classes (cdr fns) wrld)))))

  (local (defun match-regex-mutual-recursion (name body-when-takes-st body-when-takes-sts hints rule-classes omit wrld)
           `(defret-mutual ,name
              ,@(match-regex-mr-fns name body-when-takes-st body-when-takes-sts hints rule-classes
                                    (set-difference-eq *match-regex-fns* omit)
                                    wrld)
              :skip-others t)))

  (defmacro def-match-regex-thm (name body-when-takes-st body-when-takes-sts &key hints (rule-classes ':rewrite) omit)
    `(make-event (match-regex-mutual-recursion ',name ',body-when-takes-st ',body-when-takes-sts ',hints ',rule-classes ',omit (w state))))



  ;; (local (in-theory (disable match-regex-rec
  ;;                            match-concat-rec
  ;;                            match-concat-sts-rec
  ;;                            match-disjunct-rec
  ;;                            match-regex-sts-nonzero-rec
  ;;                            match-repeat-sts-minimum-rec
  ;;                            match-repeat-sts-rec
  ;;                            ;; match-repeat-sts-rec-exec
  ;;                            match-repeat-rec)))

  (local (in-theory (enable matchstatelist-min-index-of-append)))

  (defthm consp-of-match-regex-sts-nonzero-rec
    (implies (not (consp sts))
             (not (consp (match-regex-sts-nonzero-rec pat x sts mode))))
    :hints (("goal" :expand ((match-regex-sts-nonzero-rec pat x sts mode)))))

  (defthm consp-of-match-concat-sts-rec
    (implies (not (consp sts))
             (not (consp (match-concat-sts-rec pat x sts mode))))
    :hints (("goal" :expand ((match-concat-sts-rec pat x sts mode)))))

  (def-match-regex-thm matchstatelist-indices-gte-of-<fn>
    (implies (<= (nfix n) (matchstate->index st))
             (matchstatelist-indices-gte n matches))
    (implies (matchstatelist-indices-gte n sts)
               (matchstatelist-indices-gte n matches))
    :hints ('(:expand (<call>
                       (:free (st) (matchstatelist-indices-gte n (list st)))
                       (matchstatelist-indices-gte n sts)
                       (match-repeat-sts-rec nil pat x sts mode)
                       (match-repeat-rec nil min pat x st mode)))))

  (def-match-regex-thm matchstatelist-in-bounds-of-<fn>
    (implies (matchstate-in-bounds st x)
             (matchstatelist-in-bounds matches x))
    (implies (matchstatelist-in-bounds sts x)
             (matchstatelist-in-bounds matches x))
    :hints ('(:expand (<call>
                       (match-repeat-sts-rec nil pat x sts mode)
                       (match-repeat-rec nil min pat x st mode)))))

  (def-match-regex-thm matchstatelist-indices-lte-of-<fn>
    (implies (<= (matchstate->index st) (len (acl2::explode x)))
             (matchstatelist-indices-lte (len (acl2::explode x)) matches))
    (implies (matchstatelist-indices-lte (len (acl2::explode x)) sts)
               (matchstatelist-indices-lte (len (acl2::explode x)) matches))
    :hints ('(:expand (<call>
                       (:free (n st) (matchstatelist-indices-lte n (list st)))
                       (:free (n) (matchstatelist-indices-lte n sts))
                       (match-repeat-sts-rec nil pat x sts mode)
                       (match-repeat-rec nil min pat x st mode)))))

  (local (defthm matchstatelist-in-bounds-implies-indices-lte
           (implies (matchstatelist-in-bounds sts x)
                    (matchstatelist-indices-lte (len (acl2::explode x)) sts))
           :hints(("Goal" :in-theory (enable matchstatelist-in-bounds
                                             matchstatelist-indices-lte
                                             matchstate-in-bounds)))))


  ;; (defret-mutual matchstatelist-indices-lte-of-match-regex-rec
  ;;   (defret matchstatelist-indices-lte-of-<fn>
  ;;     (implies (<= (matchstate->index st) (len (acl2::explode x)))
  ;;              (matchstatelist-indices-lte (len (acl2::explode x)) matches))
  ;;     :hints ('(:expand (<call>
  ;;                        (:free (x st) (matchstatelist-indices-lte x (list st)))))
  ;;             (and stable-under-simplificationp
  ;;                  '(:in-theory (enable matchstatelist-indices-lte
  ;;                                       matchstate-measure))))
  ;;     :fn match-regex-rec)

  ;;   (defret matchstatelist-indices-lte-of-<fn>
  ;;     (implies (<= (matchstate->index st) (len (acl2::explode x)))
  ;;              (matchstatelist-indices-lte (len (acl2::explode x)) matches))
  ;;     :hints ('(:expand (<call>
  ;;                        (:free (x) (matchstatelist-indices-lte x (list st))))))
  ;;     :fn match-concat-rec)

  ;;   (defret matchstatelist-indices-lte-of-<fn>
  ;;     (implies (<= (matchstate->index st) (len (acl2::explode x))) (matchstatelist-indices-lte (len (acl2::explode x)) matches))
  ;;     :hints ('(:expand (<call>)))
  ;;     :fn match-disjunct-rec)

  ;;   (defret matchstatelist-indices-lte-of-<fn>
  ;;     (implies (matchstatelist-indices-lte (len (acl2::explode x)) sts)
  ;;              (matchstatelist-indices-lte (len (acl2::explode x)) matches))
  ;;     :hints ('(:expand (<call>
  ;;                        (:free (x) (matchstatelist-indices-lte x sts)))))
  ;;     :fn match-concat-sts-rec)

  ;;   (defret matchstatelist-indices-lte-of-<fn>
  ;;     (implies (matchstatelist-indices-lte (len (acl2::explode x)) sts) (matchstatelist-indices-lte (len (acl2::explode x)) matches))
  ;;     :hints ('(:expand (<call>
  ;;                        (:free (x) (matchstatelist-indices-lte x sts)))))
  ;;     :fn match-regex-sts-nonzero-rec)

  ;;   (defret matchstatelist-indices-lte-of-<fn>
  ;;     (implies (matchstatelist-indices-lte (len (acl2::explode x)) sts)
  ;;              (matchstatelist-indices-lte (len (acl2::explode x)) matches))
  ;;     :hints ('(:expand (<call>
  ;;                        (:free (x) (matchstatelist-indices-lte x sts)))))
  ;;     :fn match-regex-sts-rec)

  ;;   (defret matchstatelist-indices-lte-of-<fn>
  ;;     (implies (matchstatelist-indices-lte (len (acl2::explode x)) sts)
  ;;              (matchstatelist-indices-lte (len (acl2::explode x)) matches))
  ;;     :hints ('(:expand ((:free (max) <call>))))
  ;;     :fn match-repeat-sts-rec)

  ;;   (defret matchstatelist-indices-lte-of-<fn>
  ;;     (implies (matchstatelist-indices-lte (len (acl2::explode x)) sts)
  ;;              (matchstatelist-indices-lte (len (acl2::explode x)) matches))
  ;;     :hints ('(:expand (<call>)))
  ;;     :fn match-repeat-sts-minimum-rec)

  ;;   (defret matchstatelist-indices-lte-of-<fn>
  ;;     (implies (<= (matchstate->index st) (len (acl2::explode x)))
  ;;              (matchstatelist-indices-lte (len (acl2::explode x)) matches))
  ;;     :hints ('(:expand ((:free (max min) <call>)
  ;;                        (:free (x) (matchstatelist-indices-lte x (list st))))))
  ;;     :fn match-repeat-rec)
  ;;   :hints (("goal" :do-not-induct t))
  ;;   :skip-others t)


  (defret-mutual matchstatelist-measure-of-match-regex-rec
    (defret matchstatelist-measure-of-<fn>
      (>= (matchstate-measure x st) (matchstatelist-measure x matches))
      :rule-classes :linear
      :hints ('(:expand (<call>
                         (:free (st) (matchstatelist-measure x (list st)))))
              (and stable-under-simplificationp
                   '(:in-theory (enable matchstatelist-measure
                                        matchstate-measure))))
      :fn match-regex-rec)

    (defret matchstatelist-measure-of-<fn>
      (>= (matchstate-measure x st) (matchstatelist-measure x matches))
      :rule-classes :linear
      :hints ('(:expand (<call>
                         (matchstatelist-measure x (list st)))))
      :fn match-concat-rec)

    (defret matchstatelist-measure-of-<fn>
      (>= (matchstate-measure x st) (matchstatelist-measure x matches))
      :rule-classes :linear
      :hints ('(:expand (<call>)))
      :fn match-disjunct-rec)

    (defret matchstatelist-measure-of-<fn>
      (>= (matchstatelist-measure x sts) (matchstatelist-measure x matches))
      :rule-classes :linear
      :hints ('(:expand (<call>
                         (matchstatelist-measure x sts))))
      :fn match-concat-sts-rec)

    (defret matchstatelist-measure-of-<fn>
      (>= (matchstatelist-measure x sts) (matchstatelist-measure x matches))
      :rule-classes :linear
      :hints ('(:expand (<call>
                         (matchstatelist-measure x sts))))
      :fn match-regex-sts-nonzero-rec)

    (defret matchstatelist-measure-of-<fn>
      (>= (matchstatelist-measure x sts) (matchstatelist-measure x matches))
      :rule-classes :linear
      :hints ('(:expand (<call>
                         (matchstatelist-measure x sts))))
      :fn match-regex-sts-rec)

    (defret matchstatelist-measure-of-<fn>
      (>= (matchstatelist-measure x sts) (matchstatelist-measure x matches))
      :rule-classes :linear
      :hints ('(:expand ((:free (max) <call>))))
      :fn match-repeat-sts-rec)

    (defret matchstatelist-measure-of-<fn>
      (>= (matchstatelist-measure x sts) (matchstatelist-measure x matches))
      :rule-classes :linear
      :hints ('(:expand (<call>)))
      :fn match-repeat-sts-minimum-rec)

    (defret matchstatelist-measure-of-<fn>
      (>= (matchstate-measure x st) (matchstatelist-measure x matches))
      :rule-classes :linear
      :hints ('(:expand ((:free (max min) <call>)
                         (:free (x) (matchstatelist-measure x (list st))))))
      :fn match-repeat-rec)
    :hints (("goal" :do-not-induct t))
    :skip-others t)




  (defret matchstatelist-indices-gte-of-match-regex-rec-rw
    (matchstatelist-indices-gte (matchstate->index st) matches)
    :hints (("goal" :use ((:instance matchstatelist-indices-gte-of-match-regex-rec
                           (n (matchstate->index st))))))
    :fn match-regex-rec)

  (local (defthm alistp-of-backref-alist
           (implies (backref-alist-p x)
                    (alistp x))
           :hints(("Goal" :in-theory (enable backref-alist-p)))))

  (local (defthm consp-assoc-equal-when-alistp
           (implies (alistp x)
                    (iff (consp (assoc-equal k x))
                         (assoc-equal k x)))))

  (local (defthm backref-p-cdr-assoc-of-backref-alistp
           (implies (and (backref-alist-p backrefs)
                         (cdr (assoc k backrefs)))
                    (backref-p (cdr (assoc k backrefs))))))


  (defret matchstatelist-measure-of-match-regex-sts-nonzero-rec-strong
    (implies (and (consp matches)
                  (matchstatelist-indices-lte (len (acl2::explode x)) sts))
             (< (matchstatelist-measure x matches)
                (matchstatelist-measure x sts)))
    :hints (("goal" :induct (len sts)
             :expand (<call>
                      (matchstatelist-measure x sts)
                      (:free (a b) (matchstatelist-measure x (cons a b)))
                      (:free (x a b) (matchstatelist-indices-lte x (cons a b))))))
    :rule-classes :linear
    :fn match-regex-sts-nonzero-rec)



  (verify-guards match-regex-rec
    :hints(("Goal" :in-theory (enable matchstatelist-measure matchstate-measure))
           (and stable-under-simplificationp
                '(:expand ((:free (max) (match-repeat-sts-rec max pat x sts mode))
                           (:free (x) (matchstatelist-indices-lte x (list st))))))
           (and stable-under-simplificationp
                '(:in-theory (enable nfix))))
    :otf-flg t)

  (fty::deffixequiv-mutual match-regex-rec)

  (local (defthm set-difference-of-append
           (equal (set-difference$ (append a b) c)
                  (append (set-difference$ a c)
                          (set-difference$ b c)))
           :hints(("Goal" :in-theory (enable set-difference$)))))


  (local (Defthm set-difference-of-undup-self
           (not (consp (set-difference$ (undup a) a)))
           ;; :hints ((acl2::set-reasoning))
           :hints(("Goal" :use ((:instance (:theorem (implies (consp x)
                                                              (member (car x) x)))
                                 (x (set-difference$ (undup a) a))))))
           :rule-classes ((:rewrite :corollary (not (set-difference$ (undup a) a))))))

  (local (defthm set-difference-idempotent
           (equal (set-difference$ (set-difference$ a b) b)
                  (set-difference$ a b))
           :hints(("Goal" :in-theory (enable set-difference$)))))

  (local (defthm commute-set-difference
           (equal (set-difference$ (set-difference$ a c) b)
                  (set-difference$ (set-difference$ a b) c))
           :hints(("Goal" :in-theory (enable set-difference$)))))

  (local (defthm match-concat-sts-rec-of-remove-equal
           (EQUAL
            (SET-DIFFERENCE-EQUAL
             (UNDUP
              (MATCH-CONCAT-STS-REC PAT
                                    X (REMOVE-EQUAL k sts) mode))
             (MATCH-CONCAT-REC PAT X k mode))
            (SET-DIFFERENCE-EQUAL
             (UNDUP (MATCH-CONCAT-STS-REC PAT X sts mode))
             (MATCH-CONCAT-REC PAT X k mode)))
           :hints (("goal" :induct (remove-equal k sts)
                    :in-theory (enable remove-equal)
                    :expand ((:free (a b) (match-concat-sts-rec pat x (cons a b) mode))
                             (match-concat-sts-rec pat x sts mode)
                             (match-concat-sts-rec pat x nil mode))))))

  (defthm match-concat-sts-rec-of-undup
    (undup-equiv (match-concat-sts-rec pat x (undup sts) mode)
                 (match-concat-sts-rec pat x sts mode))
    :hints (("goal" :induct (undup sts)
             :in-theory (enable (:i undup))
             :expand ((match-concat-sts-rec pat x sts mode)
                      (match-concat-sts-rec pat x nil mode)
                      (undup sts)
                      (:free (a b)
                       (match-concat-sts-rec pat x (cons a b) mode))))))

  (defcong undup-equiv undup-equiv (match-concat-sts-rec pat x sts mode) 3
    :hints (("goal" :use ((:instance match-concat-sts-rec-of-undup)
                          (:instance match-concat-sts-rec-of-undup
                           (sts sts-equiv)))
             :in-theory (disable match-concat-sts-rec-of-undup))))

  (local (defthm match-regex-sts-rec-of-remove-equal
           (EQUAL
            (SET-DIFFERENCE-EQUAL
             (UNDUP
              (MATCH-REGEX-STS-REC PAT
                                    X (REMOVE-EQUAL k sts) mode))
             (MATCH-REGEX-REC PAT X k mode))
            (SET-DIFFERENCE-EQUAL
             (UNDUP (MATCH-REGEX-STS-REC PAT X sts mode))
             (MATCH-REGEX-REC PAT X k mode)))
           :hints (("goal" :induct (remove-equal k sts)
                    :in-theory (enable remove-equal)
                    :expand ((:free (a b) (match-regex-sts-rec pat x (cons a b) mode))
                             (match-regex-sts-rec pat x sts mode)
                             (match-regex-sts-rec pat x nil mode))))))

  (defthm match-regex-sts-rec-of-undup
    (undup-equiv (match-regex-sts-rec pat x (undup sts) mode)
                 (match-regex-sts-rec pat x sts mode))
    :hints (("goal" :induct (undup sts)
             :in-theory (enable (:i undup))
             :expand ((match-regex-sts-rec pat x sts mode)
                      (match-regex-sts-rec pat x nil mode)
                      (undup sts)
                      (:free (a b)
                       (match-regex-sts-rec pat x (cons a b) mode))))))

  (defcong undup-equiv undup-equiv (match-regex-sts-rec pat x sts mode) 3
    :hints (("goal" :use ((:instance match-regex-sts-rec-of-undup)
                          (:instance match-regex-sts-rec-of-undup
                           (sts sts-equiv)))
             :in-theory (disable match-regex-sts-rec-of-undup))))

  (local (defthm match-regex-sts-nonzer-rec-of-remove-bad-index
           (implies (<= (len (acl2::explode x)) (matchstate->index k))
                    (equal (match-regex-sts-nonzero-rec pat x (remove k sts) mode)
                           (match-regex-sts-nonzero-rec pat x sts mode)))
           :hints (("goal" :induct (len sts)
             :expand ((match-regex-sts-nonzero-rec pat x sts mode)
                      (match-regex-sts-nonzero-rec pat x nil mode)
                      (:free (a b)
                       (match-regex-sts-nonzero-rec pat x (cons a b) mode)))))))

  (local (defthm match-regex-sts-nonzero-rec-of-remove
           (EQUAL
            (SET-DIFFERENCE-EQUAL
             (UNDUP
              (MATCH-REGEX-STS-NONZERO-REC PAT
                                           X (REMOVE-EQUAL K STS) mode))
             (MATCHES-REMOVE-ZERO-LENGTH (MATCHSTATE->INDEX K)
                                         (MATCH-REGEX-REC PAT X K mode)))
            (SET-DIFFERENCE-EQUAL
             (UNDUP (MATCH-REGEX-STS-NONZERO-REC PAT X STS mode))
             (MATCHES-REMOVE-ZERO-LENGTH (MATCHSTATE->INDEX K)
                                         (MATCH-REGEX-REC PAT X K mode))))
           :hints (("goal" :induct (remove-equal k sts)
                    :in-theory (enable remove-equal)
                    :expand ((:free (a b) (match-regex-sts-nonzero-rec pat x (cons a b) mode))
                             (match-regex-sts-nonzero-rec pat x sts mode)
                             (match-regex-sts-nonzero-rec pat x nil mode)
                             (:free (x) (set-difference-equal nil x)))))))


  (defthm match-regex-sts-nonzero-rec-of-undup
    (undup-equiv (match-regex-sts-nonzero-rec pat x (undup sts) mode)
                 (match-regex-sts-nonzero-rec pat x sts mode))
    :hints (("goal" :induct (undup sts)
             :in-theory (enable (:i undup))
             :expand ((match-regex-sts-nonzero-rec pat x sts mode)
                      (match-regex-sts-nonzero-rec pat x nil mode)
                      (undup sts)
                      (:free (a b)
                       (match-regex-sts-nonzero-rec pat x (cons a b) mode))))))

  (defcong undup-equiv undup-equiv (match-regex-sts-nonzero-rec pat x sts mode) 3
    :hints (("goal" :use ((:instance match-regex-sts-nonzero-rec-of-undup)
                          (:instance match-regex-sts-nonzero-rec-of-undup
                           (sts sts-equiv)))
             :in-theory (disable match-regex-sts-nonzero-rec-of-undup))))



  (local (defthm undup-of-remove-rev
           (equal (UNDUP (REMOVE-EQUAL k x))
                  (remove-equal k
                                (undup x)))))
  (local (in-theory (disable undup-of-remove)))

  (local (defthm remove-of-remove-same
           (Equal (remove k (remove k x))
                  (remove k x))))

  (local (defthmd commute-remove-equal
           (Equal (Remove k (remove j x))
                  (remove j (remove k x)))))

  (local (defthm remove-undup-of-matchstatelist-fix
           (EQUAL
            (REMOVE-EQUAL (matchstate-fix k)
             (UNDUP (MATCHSTATELIST-FIX (REMOVE-EQUAL k x))))
            (REMOVE-EQUAL (MATCHSTATE-FIX k)
                          (UNDUP (MATCHSTATELIST-FIX x))))
           :hints(("Goal" :in-theory (enable remove matchstatelist-fix undup
                                             commute-remove-equal)
                   :induct (len x)
                   :expand ((:free (a b) (undup (cons a b))))))))

  (local (defthm undup-of-matchstatelist-fix
           (undup-equiv (matchstatelist-fix (undup x))
                        (matchstatelist-fix x))
           :hints(("Goal" :in-theory (enable undup matchstatelist-fix)
                   :induct (len x)
                   :expand ((:free (a b) (undup (cons a b)))
                            (undup x))))))

  (defret-mutual match-repeat-sts-rec-of-undup
    (defret  match-repeat-sts-rec-of-undup
      (undup-equiv (match-repeat-sts-rec max pat x (undup sts) mode)
                   (match-repeat-sts-rec max pat x sts mode))
      :hints ('( ;; :induct (undup sts)
                ;; :in-theory (enable (:i undup))
                :expand ((:free (max) (match-repeat-sts-rec max pat x sts mode))
                         (:free (max) (match-repeat-sts-rec max pat x (undup sts) mode)))))
    :fn match-repeat-sts-rec)
    :skip-others t)


  (defcong undup-equiv undup-equiv (match-repeat-sts-rec max pat x sts mode) 4
    :hints (("goal" :use ((:instance match-repeat-sts-rec-of-undup)
                          (:instance match-repeat-sts-rec-of-undup
                           (sts sts-equiv)))
             :in-theory (disable match-repeat-sts-rec-of-undup))))

  (defret-mutual match-repeat-sts-minimum-rec-of-undup
    (defret  match-repeat-sts-minimum-rec-of-undup
      (undup-equiv (match-repeat-sts-minimum-rec min pat x (undup sts) mode)
                   (match-repeat-sts-minimum-rec min pat x sts mode))
      :hints ('( ;; :induct (undup sts)
                ;; :in-theory (enable (:i undup))
                :expand ((:free (sts) (match-repeat-sts-minimum-rec min pat x sts mode))
                         (:free (sts) (match-repeat-sts-minimum-rec 0 pat x sts mode)))))
    :fn match-repeat-sts-minimum-rec)
    :skip-others t)

  (defcong undup-equiv undup-equiv (match-repeat-sts-minimum-rec min pat x sts mode) 4
    :hints (("goal" :use ((:instance match-repeat-sts-minimum-rec-of-undup)
                          (:instance match-repeat-sts-minimum-rec-of-undup
                           (sts sts-equiv)))
             :in-theory (disable match-repeat-sts-minimum-rec-of-undup)))))




(defprod matchresult
  :parents (acre-internals)
  :short "Result of matching a regular expression"
  ((loc maybe-natp :rule-classes :type-prescription)
   (len natp :rule-classes :type-prescription)
   (str stringp :rule-classes :type-prescription)
   (backrefs backref-alist-p))
  :layout :list
  :extra-binder-names (matchedp matched-substr))

(define matchresult-in-bounds ((x matchresult-p))
  (b* (((matchresult x)))
    (and (mbe :logic (<= (+ x.loc x.len) (strlen x.str))
              :exec (if x.loc
                        (<= (+ x.loc x.len) (strlen x.str))
                      (<= x.len (strlen x.str))))
         (backref-alist-in-bounds x.backrefs x.str))))


(define backref-extract-substr ((x backref-p) (str stringp))
  :guard (backref-in-bounds x str)
  :guard-hints (("goal" :in-theory (enable backref-in-bounds)))
  :returns (substr stringp :rule-classes :type-prescription)
  (b* (((backref x)))
    (subseq (lstrfix str) x.loc (+ x.loc x.len))))

(fty::defoption maybe-backref backref)

(define maybe-backref-in-bounds ((x maybe-backref-p) (str stringp))
  (or (not x) (backref-in-bounds x str))
  ///
  (defthm backref-in-bounds-when-maybe-backref-in-bounds
    (implies x
             (iff (maybe-backref-in-bounds x str)
                  (backref-in-bounds x str)))))

(define maybe-backref-extract-substr ((x maybe-backref-p) (str stringp))
  :guard (maybe-backref-in-bounds x str)
  :returns (substr acl2::maybe-stringp :rule-classes :type-prescription)
  (and x (backref-extract-substr x str))
  ///
  (defret maybe-backref-extract-substr-exists
    (iff substr x))

  (defret maybe-backref-extract-substr-is-string
    (iff (stringp substr) x)))

(defthm maybe-backref-p-of-lookup-in-backref-alist
  (implies (backref-alist-p x)
           (maybe-backref-p (cdr (assoc name x)))))

(defthm maybe-backref-in-bounds-of-lookup-in-backref-alist
  (implies (backref-alist-in-bounds x str)
           (maybe-backref-in-bounds (cdr (assoc name x)) str))
  :hints(("Goal" :in-theory (enable backref-alist-in-bounds
                                    maybe-backref-in-bounds))))


(define match-regex-locs ((pat regex-p)
                          (x stringp)
                          (index natp)
                          (mode matchmode-p))
  :guard (<= index (strlen x))
  :measure (nfix (- (strlen x) (nfix index)))
  :returns (match (matchresult-p match))
  :prepwork ((local (defret matchstate->index-of-first-match-lower-bound
                      (implies matches
                               (<= (matchstate->index st) (matchstate->index (car matches))))
                      :hints (("goal" :use ((:instance matchstatelist-indices-gte-of-match-regex-rec
                                             (n (matchstate->index st))))
                               :in-theory (disable matchstatelist-indices-gte-of-match-regex-rec
                                                   matchstatelist-indices-gte-of-match-regex-rec-rw)))
                      :fn match-regex-rec
                      :rule-classes :linear))
             (local (defret matchstate->index-of-first-match-upper-bound
                      (implies (and matches
                                    (matchstate-in-bounds st x))
                               (<= (matchstate->index (car matches)) (strlen x)))
                      :hints (("goal" :use ((:instance matchstatelist-in-bounds-of-match-regex-rec))
                               :in-theory (e/d ()
                                               (matchstatelist-in-bounds-of-match-regex-rec))
                               :expand ((matchstatelist-in-bounds matches x))))
                      :fn match-regex-rec
                      :rule-classes :linear)))
  ;; :guard-hints (("goal" :use ((:instance matchstatelist-indices-gte-of-match-regex-rec
  ;;                              (st (make-matchstate :index index))
  ;;                              (n index)))
  ;;                :expand ((matchstatelist-indices-gte
  ;;                          index
  ;;                          (match-regex-rec pat x (make-matchstate :index index) mode)))
  ;;                :in-theory (e/d ()
  ;;                                (matchstatelist-indices-gte-of-match-regex-rec))))
  (b* ((matches1 (match-regex-rec pat x (make-matchstate :index index) mode))
       ((when matches1)
        (b* (((matchstate m1) (car matches1)))
          (make-matchresult :loc (lnfix index) :len (- m1.index (lnfix index)) :str x :backrefs m1.backrefs)))
       ((when (mbe :logic (zp (- (strlen x) (nfix index)))
                   :exec (eql (strlen x) (lnfix index))))
        (make-matchresult :loc nil :len 0 :str x :backrefs nil)))
    (match-regex-locs pat x (+ 1 (lnfix index)) mode))
  ///

  (defret matchresult-in-bounds-of-match-regex-locs
    (implies (<= (nfix index) (strlen x))
             (matchresult-in-bounds match))
    :hints(("Goal" :in-theory (enable matchresult-in-bounds))))

  (defret matchresult->str-of-match-regex-locs
    (equal (matchresult->str match) (lstrfix x))))



(define match-regex ((regex regex-p "Regular expression to match")
                     (x stringp "String to match against")
                     &key
                     ((case-insens booleanp "Match case-insensitively") 'nil))
  :parents (acre)
  :short "Perform regular expression matching on a string."
  :returns (match matchresult-p "Result of matching, including whether it matched,
                                 which part matched, and capture group matches")
  (b* ((ans (match-regex-locs regex x 0 (make-matchmode :case-insens case-insens))))
    ;; (clear-memoize-table 'match-regex-rec)
    ans)
  ///
  (defret matchresult-in-bounds-of-<fn>
    (matchresult-in-bounds match))

  (defret matchresult->str-of-<fn>
    (equal (matchresult->str match) (lstrfix x))))


(define matchresult->matchedp ((x matchresult-p))
  :returns (matchedp booleanp :rule-classes :type-prescription)
  :parents (acre matchresult)
  :short "Boolean flag indicating whether the regular expression matched the string"
  (and (matchresult->loc x) t)
  ///
  (fty::deffixequiv matchresult->matchedp)

  (defthm matchresult->matchedp-of-matchresult
    (iff (matchresult->matchedp (make-matchresult :loc loc :len len :str str :backrefs backrefs))
         loc))

  (defthm natp-of-matchresult->loc
    (iff (natp (matchresult->loc x))
         (matchresult->matchedp x))
    :rule-classes (:rewrite
                   (:type-prescription :corollary
                    (implies (matchresult->matchedp x)
                             (natp (matchresult->loc x))))))

  (defthm matchresult->loc-under-iff
    (iff (matchresult->loc x) (matchresult->matchedp x))))

(define matchresult->matched-substr ((x matchresult-p))
  :guard (matchresult-in-bounds x)
  :prepwork ((local (in-theory (enable matchresult-in-bounds))))
  :returns (substr acl2::maybe-stringp :rule-classes :type-prescription)
  :short "When the regular expression matched the string, returns the substring that it matched"
  (b* (((matchresult x))
       ((unless x.loc) nil))
    (subseq x.str x.loc (+ x.loc x.len)))
  ///
  (defret matchresult->matched-substr-under-iff
    (iff substr (matchresult->matchedp x))))

(define matchresult->captured-substr ((index) (x matchresult-p))
  :guard (matchresult-in-bounds x)
  :prepwork ((local (in-theory (enable matchresult-in-bounds)))
             (local (defthm alistp-when-backref-alist-p-rw
                      (implies (backref-alist-p x)
                               (alistp x))))
             (local (defthm consp-of-assoc-equal
                      (implies (alistp x)
                               (iff (consp (assoc-equal k x))
                                    (assoc-equal k x))))))
  :returns (substr acl2::maybe-stringp :rule-classes :type-prescription)
  :short "Returns the substring matched by the capture group with the given name
          or index, or NIL if the capture group was not matched"
  (b* (((matchresult x)))
    (maybe-backref-extract-substr (cdr (assoc-equal index x.backrefs)) x.str)))

(define matchresult->captured-substr! ((index) (x matchresult-p))
  :guard (matchresult-in-bounds x)
  :prepwork ((local (in-theory (enable matchresult-in-bounds)))
             (local (defthm alistp-when-backref-alist-p-rw
                      (implies (backref-alist-p x)
                               (alistp x))))
             (local (defthm consp-of-assoc-equal
                      (implies (alistp x)
                               (iff (consp (assoc-equal k x))
                                    (assoc-equal k x))))))
  :returns (substr stringp :rule-classes :type-prescription)
  :short "Returns the substring matched by the capture group with the given name
          or index, or the empty string if the capture group was not matched"
  (b* (((matchresult x)))
    (or (maybe-backref-extract-substr (cdr (assoc-equal index x.backrefs)) x.str) "")))


(define captures-bindings (args index matchresult !)
  :mode :program
  (b* (((when (atom args)) nil)
       (arg (car args))
       (fn (if ! 'matchresult->captured-substr! 'matchresult->captured-substr))
       ((when (symbolp arg))
        (cons `(,arg (,fn ,index ,matchresult))
              (captures-bindings (cdr args) (+ 1 index) matchresult !))))
    (case-match arg
      ((var name)
       (cons `(,var (,fn ,name ,matchresult))
              (captures-bindings (cdr args) (+ 1 index) matchresult !)))
      (& (er hard? 'captures-bindings "Bad capture element: ~x0" arg)))))

(acl2::def-b*-binder captures
  :body
  (b* ((args acl2::args)
       (forms acl2::forms)
       ((unless (atom (cdr forms)))
        (er hard? 'captures "Too many forms: ~x0" forms))
       (bindings (captures-bindings args 1 (car forms) nil)))
    `(b* ,bindings ,acl2::rest-expr)))

(acl2::def-b*-binder captures!
  :body
  (b* ((args acl2::args)
       (forms acl2::forms)
       ((unless (atom (cdr forms)))
        (er hard? 'captures "Too many forms: ~x0" forms))
       (bindings (captures-bindings args 1 (car forms) t)))
    `(b* ,bindings ,acl2::rest-expr)))

(define named-captures-bindings (args matchresult !)
  :mode :program
  (b* (((when (atom args)) nil)
       (arg (car args))
       (fn (if ! 'matchresult->captured-substr! 'matchresult->captured-substr))
       ((when (symbolp arg))
        (cons `(,arg (,fn ,(str::downcase-string (symbol-name arg)) ,matchresult))
              (named-captures-bindings (cdr args) matchresult !))))
    (case-match arg
      ((var name)
       (cons `(,var (,fn ,name ,matchresult))
              (named-captures-bindings (cdr args) matchresult !)))
      (& (er hard? 'named-captures-bindings "Bad capture element: ~x0" arg)))))



(acl2::def-b*-binder named-captures
  :body
  (b* ((args acl2::args)
       (forms acl2::forms)
       ((unless (atom (cdr forms)))
        (er hard? 'named-captures "Too many forms: ~x0" forms))
       (bindings (named-captures-bindings args (car forms) nil)))
    `(b* ,bindings ,acl2::rest-expr)))

(acl2::def-b*-binder named-captures!
  :body
  (b* ((args acl2::args)
       (forms acl2::forms)
       ((unless (atom (cdr forms)))
        (er hard? 'named-captures "Too many forms: ~x0" forms))
       (bindings (named-captures-bindings args (car forms) t)))
    `(b* ,bindings ,acl2::rest-expr)))



(encapsulate nil
  (local (include-book "std/lists/take" :dir :system))
  (local (include-book "arithmetic/top" :dir :system))

  (local (defthm equal-of-implode
           (implies (character-listp x)
                    (equal (equal (acl2::implode x) y)
                           (and (stringp y)
                                (equal x (acl2::explode y)))))))

  (local (defun eoa-ind (a c)
           (if (atom a)
               c
             (eoa-ind (cdr a) (cdr c)))))

  (local (defthmd equal-cons-strong
           (equal (equal (cons a b) c)
                  (and (consp c) (equal a (car c)) (equal b (cdr c))))))

  (local (defthm append-under-iff
           (iff (append a b)
                (or (consp a) b))))

  (local (defthm equal-of-append
           (iff (equal (append a b) c)
                (and (<= (len a) (len c))
                     (equal (take (len a) c) (list-fix a))
                     (equal (nthcdr (len a) c) b)))
           :hints(("Goal" :in-theory (enable append acl2::take nthcdr len list-fix
                                             equal-cons-strong)
                   :induct (eoa-ind a c)))))

  (local (defthmd icharlisteqv-cons-strong
           (equal (str::icharlisteqv (cons a b) c)
                  (and (consp c) (str::ichareqv a (car c)) (str::icharlisteqv b (cdr c))))))

  (local (defthm icharlisteqv-of-append
           (iff (str::icharlisteqv (append a b) c)
                (and (<= (len a) (len c))
                     (str::icharlisteqv (take (len a) c) (list-fix a))
                     (str::icharlisteqv (nthcdr (len a) c) b)))
           :hints(("Goal" :in-theory (enable append acl2::take nthcdr len list-fix
                                             icharlisteqv-cons-strong)
                   :induct (eoa-ind a c)))))

  ;; (local (defthmd not-equal-by-len
  ;;          (implies (not (equal (len x) (len y)))
  ;;                   (not (equal x y)))))

  (local (defthm len-of-nthcdr
           (implies (force (<= (nfix n) (len x)))
                    (equal (len (nthcdr n x))
                           (- (len x) (nfix n))))
           :hints(("Goal" :in-theory (enable nthcdr)))))

  (local (defthm equal-of-cat
           (iff (equal (concatenate 'string x y) z)
                (and (stringp z)
                     (<= (len (acl2::explode x)) (len (acl2::explode z)))
                     (equal (take (len (acl2::explode x)) (acl2::explode z))
                            (acl2::explode x))
                     (equal (nthcdr (len (acl2::explode x)) (acl2::explode z))
                            (acl2::explode y))))))

  (local (defthm character-listp-of-take
           (implies (and (character-listp x)
                         (<= (nfix n) (len x)))
                    (character-listp (take n x)))
           :hints (("Goal" :in-theory (enable take)))))

  (local (defthm character-listp-of-nthcdr
           (implies (character-listp x)
                    (character-listp (nthcdr n x)))))

  (local (defun nthcdr-of-take-ind (n m x)
           (if (zp n)
               (list m x)
             (nthcdr-of-take-ind (1- n) (1- (nfix m)) (cdr x)))))


  (local (defthm nthcdr-of-too-many
           (implies (< (len x) (nfix n))
                    (equal (nthcdr n x) nil))))


  (local (defthm nthcdr-of-take
           (equal (nthcdr n (take m x))
                  (and (<= (nfix n) (nfix m))
                       (take (- (nfix m) (nfix n))
                             (nthcdr n x))))
           :hints(("Goal" :in-theory (enable nthcdr take)
                   :induct (nthcdr-of-take-ind n m x))
                  (and stable-under-simplificationp
                       '(:in-theory (enable nfix))))))

  (local (defthm nthcdr-of-nthcdr
           (equal (nthcdr n (nthcdr m x))
                  (nthcdr (+ (nfix n) (nfix m)) x))))

  (defthm match-exact-of-cat
    (Equal (match-exact (concatenate 'string x y) str index mode)
           (let ((x-index (match-exact x str index mode)))
             (and x-index
                  (match-exact y str x-index mode))))
    :hints(("Goal" :in-theory (enable match-exact)))))

(local (in-theory (disable string-append)))


(local
 (encapsulate nil
   (local (include-book "tools/easy-simplify" :dir :system))

   ;; (local (defun def-regex-simp-fn (fn pat state)
   ;;          (declare (xargs :mode :program :stobjs state))
   ;;          (b* ((thmname (intern$ (str::cat (symbol-name fn) "-OF-"
   ;;                                           (if (consp pat)
   ;;                                               (symbol-name (car pat))
   ;;                                             (symbol-name pat)))
   ;;                                 "ACRE"))
   ;;               (formals (acl2::formals fn (w state)))
   ;;               (term (cons fn (cons pat (cdr formals)))))
   ;;            (value `(acl2::defopen ,thmname ,term :hint (:expand ,term))))))

   ;; (defmacro def-regex-simp (fn pat)
   ;;   `(make-event (def-regex-simp-fn ',fn ',pat state)))


   ;; (def-regex-simp match-regex-rec (regex-exact str))
   ;; (def-regex-simp match-regex-rec (regex-concat lst))
   ;; (def-regex-simp match-concat-rec (cons a b))
   ;; (def-regex-simp match-concat-rec nil)
   (local (deflabel before-match-regex-openers))
   (make-event
    '(acl2::defopen match-regex-rec-when-exact (match-regex-rec x str st mode)
       :hyp (regex-case x :exact)
       :hint (:expand ((match-regex-rec x str st mode)))))

   (make-event
    '(acl2::defopen match-regex-rec-when-concat (match-regex-rec x str st mode)
       :hyp (regex-case x :concat)
       :hint (:expand ((match-regex-rec x str st mode)))))

   (make-event
    '(acl2::defopen match-concat-rec-when-consp (match-concat-rec x str sts mode)
       :hyp (consp x)
       :hint (:expand ((match-concat-rec x str sts mode)))))

   (make-event
    '(acl2::defopen match-concat-rec-when-not-consp (match-concat-rec x str sts mode)
       :hyp (not (consp x))
       :hint (:expand ((match-concat-rec x str sts mode)))))

   (make-event
    '(acl2::defopen match-regex-rec-when-disjunct (match-regex-rec x str st mode)
       :hyp (regex-case x :disjunct)
       :hint (:expand ((match-regex-rec x str st mode)))))

   (make-event
    '(acl2::defopen match-disjunct-rec-when-consp (match-disjunct-rec x str sts mode)
       :hyp (consp x)
       :hint (:expand ((match-disjunct-rec x str sts mode)))))

   (make-event
    '(acl2::defopen match-disjunct-rec-when-not-consp (match-disjunct-rec x str sts mode)
       :hyp (not (consp x))
       :hint (:expand ((match-disjunct-rec x str sts mode)))))

   (make-event
    '(acl2::defopen match-concat-sts-rec-of-cons (match-concat-sts-rec x str (cons a b) mode)
       :hint (:expand ((match-concat-sts-rec x str (cons a b) mode)))))

   (make-event
    '(acl2::defopen match-regex-sts-rec-of-cons (match-regex-sts-rec x str (cons a b) mode)
       :hint (:expand ((match-regex-sts-rec x str (cons a b) mode)))))

   (make-event
    '(acl2::defopen match-concat-sts-rec-of-nil (match-concat-sts-rec x str nil mode)
       :hint (:expand ((match-concat-sts-rec x str nil mode)))))


   (make-event
    '(acl2::defopen match-regex-sts-rec-of-nil (match-regex-sts-rec x str nil mode)
       :hint (:expand ((match-regex-sts-rec x str nil mode)))))

   (def-ruleset! match-regex-openers
     (set-difference-theories (current-theory :here)
                              (current-theory 'before-match-regex-openers)))))

(defsection regex-concat2
  (local (std::set-define-current-function regex-concat2))

  (local (defthm undup-of-single
           (equal (undup (list x)) (list x))
           :hints(("Goal" :in-theory (enable undup)))))

  (defthm match-concat-sts-rec-of-empty-pat
    (equal (match-concat-sts-rec nil x sts mode)
           (matchstatelist-fix sts))
    :hints(("Goal" :in-theory (enable match-concat-sts-rec
                                      match-concat-rec)
            :induct (len sts))))

  (defthm match-concat-sts-rec-of-single-pat
    (undup-equiv (match-concat-sts-rec (list y) x sts mode)
                 (match-regex-sts-rec y x sts mode))
    :hints(("Goal" :in-theory (enable match-concat-sts-rec
                                      match-regex-sts-rec
                                      match-concat-rec)
            :expand ((match-concat-sts-rec (list y) x sts mode)
                     (match-regex-sts-rec y x sts mode))
            :induct (len sts))))

  (local (defthm match-regex-of-empty-exact
           (implies (and (Equal (regex-kind x) :exact)
                         (Equal (regex-exact->str x) "")
                         (<= (matchstate->index st) (strlen str)))
                    (equal (match-regex-rec x str st mode)
                           (list (matchstate-fix st))))
           :hints(("Goal" :in-theory (enable match-exact take)))))

  (local (defthm match-regex-sts-rec-of-empty-exact
           (implies (and (Equal (regex-kind x) :exact)
                         (Equal (regex-exact->str x) "")
                         (matchstatelist-indices-lte (strlen str) sts))
                    (equal (match-regex-sts-rec x str sts mode)
                           (matchstatelist-fix sts)))
           :hints(("Goal" :in-theory (enable match-regex-sts-rec
                                             matchstatelist-indices-lte)
                   :induct (len sts)))))

  (local (defthm match-regex-sts-rec-of-concat
           (implies (and (Equal (regex-kind x) :concat)
                         (matchstatelist-indices-lte (strlen str) sts))
                    (equal (match-regex-sts-rec x str sts mode)
                           (match-concat-sts-rec (regex-concat->lst x) str sts mode)))
           :hints(("Goal" :in-theory (enable match-regex-sts-rec
                                             match-concat-sts-rec
                                             matchstatelist-indices-lte)
                   :induct (len sts)))))

  (defret match-regex-rec-of-regex-concat2
    (implies (<= (matchstate->index st) (strlen str))
             (undup-equiv (match-regex-rec res str st mode)
                          (match-regex-rec (regex-concat (list x y)) str st mode)))
    :hints(("Goal" :in-theory (enable regex-concat2)))))


(defsection regex-disjunct2
  (local (std::set-define-current-function regex-disjunct2))

  (defret match-regex-rec-of-regex-disjunct2
    (implies (<= (matchstate->index st) (strlen str))
             (undup-equiv (match-regex-rec res str st mode)
                          (match-regex-rec (regex-disjunct (list x y)) str st mode)))
    :hints(("Goal" :in-theory (enable regex-disjunct2)))))




(defsection matchresult->captured-substr-of-match-regex-when-regex-definitely-captures

  (defines regex-definitely-captures
    (define regex-definitely-captures ((name) (x regex-p))
      :measure (regex-count x)
      (regex-case x
        :exact nil
        :repeat (and (< 0 x.min)
                     (regex-definitely-captures name x.pat))
        :concat (regexlist-definitely-captures name x.lst)
        :disjunct (regexlist-disjunct-definitely-captures name x.lst)
        :group (or (equal x.index name)
                   (regex-definitely-captures name x.pat))
        :reverse-pref (regex-definitely-captures name x.pat)
        :no-backtrack (regex-definitely-captures name x.pat)
        :case-sens (regex-definitely-captures name x.pat)
        ;; :zerolength ;; ??
        ;; (regex-definitely-captures name x.pat)
        :otherwise nil))
    (define regexlist-definitely-captures ((name) (x regexlist-p))
      :measure (regexlist-count x)
      (if (atom x)
          nil
        (or (regex-definitely-captures name (car x))
            (regexlist-definitely-captures name (cdr x)))))
    (define regexlist-disjunct-definitely-captures ((name) (x regexlist-p))
      :measure (regexlist-count x)
      (and (consp x)
           (regex-definitely-captures name (car x))
           (or (atom (cdr x))
               (regexlist-disjunct-definitely-captures name (cdr x))))))

  (local (defthm alistp-when-backref-alist-p-rw
           (implies (backref-alist-p x)
                    (alistp x))))

  (define matchstatelist-all-have-backref ((name) (x matchstatelist-p))
    (if (atom x)
        t
      (and (assoc-equal name (matchstate->backrefs (car x)))
           (matchstatelist-all-have-backref name (cdr x))))
    ///
    (defthm matchstatelist-all-have-backref-of-remove
      (implies (assoc-equal name (matchstate->backrefs x1))
               (iff (matchstatelist-all-have-backref name (remove-equal x1 x))
                    (matchstatelist-all-have-backref name x)))
      :hints(("Goal" :in-theory (enable remove-equal))))
    (defthm matchstatelist-all-have-backref-of-undup
      (iff (matchstatelist-all-have-backref name (undup x))
           (matchstatelist-all-have-backref name x))
      :hints(("Goal" :in-theory (enable undup))))
    (defthm matchstatelist-all-have-backref-of-nil
      (matchstatelist-all-have-backref name nil))
    (defthm matchstatelist-all-have-backref-of-append
      (iff (matchstatelist-all-have-backref name (append x y))
           (and (matchstatelist-all-have-backref name x)
                (matchstatelist-all-have-backref name y))))
    (defthm matchstatelist-all-have-backref-of-set-difference
      (implies (matchstatelist-all-have-backref name x)
               (matchstatelist-all-have-backref name (set-difference-equal x y))))
    (defthm matchstatelist-all-have-backref-of-matches-remove-zero-length
      (implies (matchstatelist-all-have-backref name x)
               (matchstatelist-all-have-backref name
                                                (matches-remove-zero-length n x)))
      :hints(("Goal" :in-theory (enable matches-remove-zero-length))))
    (defthm matchstatelist-all-have-backref-of-cons
      (equal (matchstatelist-all-have-backref name (cons a b))
             (and (assoc-equal name (matchstate->backrefs a))
                  (matchstatelist-all-have-backref name b))))
    (defthm matchstatelist-all-have-backref-of-rev
      (iff (matchstatelist-all-have-backref name (rev x))
           (matchstatelist-all-have-backref name x))
      :hints(("Goal" :in-theory (enable rev))))
    (defthm matchstatelist-all-have-backref-of-matches-add-backref
      (implies (matchstatelist-all-have-backref name x)
               (matchstatelist-all-have-backref name
                                                (matches-add-backref name1 start-idx x)))
      :hints(("Goal" :in-theory (enable matches-add-backref
                                        match-add-backref))))

    (defthm matchstatelist-all-have-backref-of-matches-add-backref-same
      (matchstatelist-all-have-backref name
                                       (matches-add-backref name start-idx x))
      :hints(("Goal" :in-theory (enable matches-add-backref
                                        match-add-backref))))
    )


  (local (defthm maybe-natp-fix-when-x
           (implies x
                    (natp (maybe-natp-fix x)))
           :hints(("Goal" :in-theory (enable maybe-natp-fix)))
           :rule-classes :type-prescription))

  (defret-mutual have-backref-when-already-has-backref
    :mutual-recursion match-regex-rec
    (defret have-backref-when-already-has-backref-of-<fn>
      (implies (assoc-equal name (matchstate->backrefs st))
               (matchstatelist-all-have-backref name matches))
      :hints ('(:expand (<call>)))
      :fn match-regex-rec)
    (defret have-backref-when-already-has-backref-of-<fn>
      (implies (assoc-equal name (matchstate->backrefs st))
               (matchstatelist-all-have-backref name matches))
      :hints ('(:expand (<call>)))
      :fn match-concat-rec)
    (defret have-backref-when-already-has-backref-of-<fn>
      (implies (matchstatelist-all-have-backref name sts)
               (matchstatelist-all-have-backref name matches))
      :hints ('(:expand (<call>
                         (matchstatelist-all-have-backref name sts))))
      :fn match-concat-sts-rec)
    (defret have-backref-when-already-has-backref-of-<fn>
      (implies (assoc-equal name (matchstate->backrefs st))
               (matchstatelist-all-have-backref name matches))
      :hints ('(:expand (<call>)))
      :fn match-disjunct-rec)
    (defret have-backref-when-already-has-backref-of-<fn>
      (implies (matchstatelist-all-have-backref name sts)
               (matchstatelist-all-have-backref name matches))
      :hints ('(:expand (<call>
                         (matchstatelist-all-have-backref name sts))))
      :fn match-regex-sts-nonzero-rec)
    (defret have-backref-when-already-has-backref-of-<fn>
      (implies (matchstatelist-all-have-backref name sts)
               (matchstatelist-all-have-backref name matches))
      :hints ('(:expand (<call>
                         (matchstatelist-all-have-backref name sts))))
      :fn match-regex-sts-rec)
    (defret have-backref-when-already-has-backref-of-<fn>
      (implies (matchstatelist-all-have-backref name sts)
               (matchstatelist-all-have-backref name matches))
      :hints ('(:expand ((:free (min) <call>))))
      :fn match-repeat-sts-minimum-rec)
    (defret have-backref-when-already-has-backref-of-<fn>
      (implies (matchstatelist-all-have-backref name sts)
               (matchstatelist-all-have-backref name matches))
      :hints ('(:expand ((:free (max) <call>))))
      :fn match-repeat-sts-rec)
    (defret have-backref-when-already-has-backref-of-<fn>
      (implies (assoc-equal name (matchstate->backrefs st))
               (matchstatelist-all-have-backref name matches))
      :hints ('(:expand ((:free (max) <call>))))
      :fn match-repeat-rec)
    :skip-others t)

  (local (defthm match-disjunct-rec-of-atom
           (implies (not (consp pat))
                    (equal (match-disjunct-rec pat x st mode) nil))
           :hints (("goal" :expand ((match-disjunct-rec pat x st mode))))))


  (defret-mutual have-backref-when-regex-definitely-captures
    :mutual-recursion match-regex-rec
    (defret have-backref-when-regex-definitely-captures-of-<fn>
      (implies (regex-definitely-captures name pat)
               (matchstatelist-all-have-backref name matches))
      :hints ('(:expand (<call>
                         (regex-definitely-captures name pat))))
      :fn match-regex-rec)
    (defret have-backref-when-regex-definitely-captures-of-<fn>
      (implies (regexlist-definitely-captures name pat)
               (matchstatelist-all-have-backref name matches))
      :hints ('(:expand (<call>
                         (regexlist-definitely-captures name pat))))
      :fn match-concat-rec)
    (defret have-backref-when-regex-definitely-captures-of-<fn>
      (implies (regexlist-definitely-captures name pat)
               (matchstatelist-all-have-backref name matches))
      :hints ('(:expand (<call>
                         (regexlist-definitely-captures name pat))))
      :fn match-concat-sts-rec)
    (defret have-backref-when-regex-definitely-captures-of-<fn>
      (implies (regexlist-disjunct-definitely-captures name pat)
               (matchstatelist-all-have-backref name matches))
      :hints ('(:expand (<call>
                         (regexlist-disjunct-definitely-captures name pat))))
      :fn match-disjunct-rec)
    (defret have-backref-when-regex-definitely-captures-of-<fn>
      (implies (regex-definitely-captures name pat)
               (matchstatelist-all-have-backref name matches))
      :hints ('(:expand (<call>)))
      :fn match-regex-sts-nonzero-rec)
    (defret have-backref-when-regex-definitely-captures-of-<fn>
      (implies (regex-definitely-captures name pat)
               (matchstatelist-all-have-backref name matches))
      :hints ('(:expand (<call>
                         (matchstatelist-all-have-backref name sts))))
      :fn match-regex-sts-rec)
    (defret have-backref-when-regex-definitely-captures-of-<fn>
      (implies (and (regex-definitely-captures name pat)
                    (< 0 (nfix min)))
               (matchstatelist-all-have-backref name matches))
      :hints ('(:expand ((:free (min) <call>))))
      :fn match-repeat-sts-minimum-rec)
    ;; (defret have-backref-when-regex-definitely-captures-of-<fn>
    ;;   (implies (matchstatelist-all-have-backref name sts)
    ;;            (matchstatelist-all-have-backref name matches))
    ;;   :hints ('(:expand ((:free (max) <call>))))
    ;;   :fn match-repeat-sts-rec)
    (defret have-backref-when-regex-definitely-captures-of-<fn>
      (implies (and (regex-definitely-captures name pat)
                    (< 0 (nfix min)))
               (matchstatelist-all-have-backref name matches))
      :hints ('(:expand ((:free (max) <call>))))
      :fn match-repeat-rec)
    :skip-others t)


  (local (defthm backref-present-of-car-when-matchstatelist-all-have-backref
           (implies (and (matchstatelist-all-have-backref name x)
                         (consp x))
                    (assoc-equal name (matchstate->backrefs (car x))))))

  (defret have-backref-of-match-regex-locs-when-regex-definitely-captures
    (implies (and (regex-definitely-captures name pat)
                  (matchresult->matchedp match))
             (assoc-equal name (matchresult->backrefs match)))
    :hints(("Goal" :expand ((:free (pat x mode) <call>))
            :in-theory (e/d ((:i <fn>))
                            (matchresult->loc-under-iff))
            :induct <call>))
    :fn match-regex-locs)


  (defret have-backref-of-match-regex-when-regex-definitely-captures
    (implies (and (regex-definitely-captures name regex)
                  (matchresult->matchedp match))
             (assoc-equal name (matchresult->backrefs match)))
    :hints(("Goal" :in-theory (enable <fn>)))
    :fn match-regex)


  (local (defthm cdr-assoc-equal-under-iff-of-backref-alist
           (implies (backref-alist-p x)
                    (iff (cdr (assoc-equal name x))
                         (assoc-equal name x)))))

  (defret matchresult->captured-substr-of-match-regex-when-regex-definitely-captures
    (implies (and (regex-definitely-captures name regex)
                  (matchresult->matchedp match))
             (matchresult->captured-substr name match))
    :hints(("Goal" :in-theory (enable matchresult->captured-substr)))
    :fn match-regex)

  (defret stringp-of-matchresult->captured-substr-of-match-regex-when-regex-definitely-captures
    (implies (and (regex-definitely-captures name regex)
                  (matchresult->matchedp match))
             (stringp (matchresult->captured-substr name match)))
    :hints(("Goal" :in-theory (enable matchresult->captured-substr)))
    :fn match-regex))


