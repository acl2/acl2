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

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/alists/alist-keys" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/cat" :dir :system)
(include-book "std/util/defenum" :dir :system)
(include-book "std/strings/strprefixp" :dir :system)
(include-book "std/strings/strpos" :dir :system)
(include-book "std/util/defconsts" :dir :system)

(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable take (tau-system))))

(defmacro lstrfix (x)
  `(mbe :logic (acl2::str-fix ,x) :exec ,x))

(defmacro strlen (x)
  `(length (the string (lstrfix ,x))))

(local (Defthm explode-of-str-fix
         (equal (acl2::explode (acl2::str-fix x))
                (acl2::explode x))))

(local (defthm my-characterp-nth
         (implies (and (character-listp x)
                       (< (nfix i) (len x)))
                  (characterp (nth i x)))))

(local (defthm character-listp-cdr
         (implies (character-listp x)
                  (character-listp (cdr x)))))

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
      (rev-keys acc nil)
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
  (local (in-theory (disable acl2::revappend-removal)))
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
  




(deftypes regex
  (deftagsum regex
    (:exact ((str stringp :rule-classes :type-prescription)))
    (:repeat
     ((pat regex)
      (min natp)
      (max acl2::maybe-natp)))
    (:concat ((lst regexlist)))
    (:disjunct ((lst regexlist)))
    (:charset
     ((chars stringp :rule-classes :type-prescription)
      (negp booleanp :rule-classes :type-prescription)))
    (:start ())   ;; matches empty string at beginning
    (:end   ())   ;; matches empty string at end
    (:group
     ((pat regex)
      (index))) ;; allow named groups
    (:backref
     ((index))) ;; allow named backrefs
    (:reverse-pref ((pat regex))) ;; Reverse the preference order of matches.
    (:no-backtrack ((pat regex))) ;; Throws out all but the most-preferred match.
    (:case-sens ;; Make the subpattern match case-sensitively or insensitively.
     ((pat regex)
      (case-insens booleanp :rule-classes :type-prescription)))
    (:zerolength
     ;; Checks that the pattern matches (or does not match, if negp)
     ;; but doesn't change the point in the string where we're matching.
     ((pat regex)
      (negp booleanp :rule-classes :type-prescription)))
    :layout :list
    :measure (acl2-count x))

  (deflist regexlist :elt-type regex :true-listp t
    :measure (acl2-count x)))
    
(defprod backref
  ((loc natp :rule-classes :type-prescription)
   (len natp :rule-classes :type-prescription))
  :layout :tree)

(defmap backref-alist :val-type backref :true-listp t)

(defprod matchstate
  ((index natp :rule-classes :type-prescription)
   (backrefs backref-alist))
  :layout :tree)

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

;; (define matchstate-<= ((st1 matchstate-p) (st2 matchstate-p))
;;   (<= (matchstate->index st1) (matchstate->index st2)))

;; (define matchstate-<=-list ((st matchstate-p) (sts matchstatelist-p))
;;   (if (atom sts)
;;       t
;;     (and (matchstate-<= st (car sts))
;;          (matchstate-<=-list st (cdr sts)))))

;; (define matchstatelist-<=-state ((sts matchstatelist-p) (st matchstate-p))
;;   (if (atom sts)
;;       nil
;;     (or (matchstate-<= (car sts) st)
;;         (matchstatelist-<=-state (cdr sts) st))))

;; (define matchstatelist-<= ((sts1 matchstatelist-p) (sts2 matchstatelist-p))
;;   (if (atom sts2)
;;       t
;;     (and (matchstatelist-<=-state sts1 (car sts2))
;;          (matchstatelist-<= sts1 (cdr sts2)))))

;; (define matchstatelist-measure ((x stringp)
;;                                 (sts matchstatelist-p))
;;   :returns (meas natp :rule-classes :type-prescription)
;;   (if (consp sts)
;;       (nfix (- (strlen x) (matchstatelist-min-index sts)))
;;     0)
;;   ///
;;   (defret matchstatelist-measure-gte-car
;;     (implies (consp sts)
;;              (<= (matchstate-measure x (car sts)) meas))
;;     :hints(("Goal" :in-theory (enable matchstate-measure
;;                                       matchstatelist-min-index)))
;;     :rule-classes :linear)

;;   (defret matchstatelist-measure-gte-cdr
;;     (implies (consp sts)
;;              (<= (matchstatelist-measure x (cdr sts)) meas))
;;     :hints(("Goal" :in-theory (enable matchstatelist-min-index)))
;;     :rule-classes :linear))

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
                          (< (matchstatelist-measure x (cdr sts)) (matchstate-measure x (car sts)))))))))

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
    :hints (("goal" :use ((:instance undup-under-set-equiv
                           (x acl2::x))
                          (:instance undup-under-set-equiv
                           (x acl2::y)))
             :in-theory (disable undup-under-set-equiv))))

  (defcong undup-equiv undup-equiv (append a b) 1
    :hints (("goal" :use ((:instance append-of-undup-under-undup-equiv-1
                           (x a) (y b))
                          (:instance append-of-undup-under-undup-equiv-1
                           (x a-equiv) (y b)))
             :in-theory (disable append-of-undup-under-undup-equiv-1))))
             
  (defcong undup-equiv undup-equiv (append a b) 2)
  (defcong undup-equiv undup-equiv (append a b) 2)

  (defcong undup-equiv equal (undup x) 1)

  (defcong undup-equiv equal (matchstatelist-measure x sts) 2
    :hints (("goal" :use ((:instance matchstatelist-measure-of-undup)
                          (:instance matchstatelist-measure-of-undup
                           (sts sts-equiv)))
             :in-theory (disable matchstatelist-measure-of-undup)))))





(defines match-regex-rec
  (define match-regex-rec ((pat regex-p)
                           (x stringp)
                           (st matchstate-p)
                           (mode matchmode-p))
    :guard (<= (matchstate->index st) (strlen x))
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

        :disjunct (undup-exec (match-disjunct-rec pat.lst x st mode) nil)

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

        :zerolength (b* ((rec-matches (match-regex-rec pat.pat x st mode)))
                      (and (xor (consp rec-matches) pat.negp)
                           (list st))))))

  (define match-concat-rec ((pat regexlist-p)
                            (x stringp)
                            (st matchstate-p)
                            (mode matchmode-p))
    :returns (matches matchstatelist-p)
    :guard (<= (matchstate->index st) (strlen x))
    :measure (list (regexlist-count pat) 0 (matchstate-measure x st) 0)
    (b* ((st (matchstate-fix st))
         ((when (atom pat))
          (list st))
         (matches (match-regex-rec (car pat) x st mode)))
      (undup-exec (match-concat-sts-rec (cdr pat) x matches mode) nil)))

  (define match-concat-sts-rec ((pat regexlist-p)
                                (x stringp)
                                (sts matchstatelist-p)
                                (mode matchmode-p))
    :guard (matchstatelist-indices-lte (strlen x) sts)
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
    :guard (<= (matchstate->index st) (strlen x))
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
    :guard (matchstatelist-indices-lte (strlen x) sts)
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
    :guard (matchstatelist-indices-lte (strlen x) sts)
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
    :guard (matchstatelist-indices-lte (strlen x) sts)
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
    :guard (matchstatelist-indices-lte (strlen x) sts)
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
    :guard (matchstatelist-indices-lte (strlen x) sts)
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
    :guard (<= (matchstate->index st) (strlen x))
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

  (local (in-theory (disable match-regex-rec
                             match-concat-rec
                             match-concat-sts-rec
                             match-disjunct-rec
                             match-regex-sts-nonzero-rec
                             match-repeat-sts-minimum-rec
                             match-repeat-sts-rec
                             ;; match-repeat-sts-rec-exec
                             match-repeat-rec)))

  (local (in-theory (enable matchstatelist-min-index-of-append)))

  (defthm consp-of-match-regex-sts-nonzero-rec
    (implies (not (consp sts))
             (not (consp (match-regex-sts-nonzero-rec pat x sts mode))))
    :hints (("goal" :expand ((match-regex-sts-nonzero-rec pat x sts mode)))))

  (defthm consp-of-match-concat-sts-rec
    (implies (not (consp sts))
             (not (consp (match-concat-sts-rec pat x sts mode))))
    :hints (("goal" :expand ((match-concat-sts-rec pat x sts mode)))))

  (defret-mutual matchstatelist-indices-gte-of-match-regex-rec
    (defret matchstatelist-indices-gte-of-<fn>
      (implies (<= (nfix n) (matchstate->index st))
               (matchstatelist-indices-gte n matches))
      :hints ('(:expand (<call>
                         (:free (st) (matchstatelist-indices-gte n (list st)))))
              (and stable-under-simplificationp
                   '(:in-theory (enable matchstatelist-indices-gte
                                        matchstate-measure))))
      :fn match-regex-rec)

    (defret matchstatelist-indices-gte-of-<fn>
      (implies (<= (nfix n) (matchstate->index st))
               (matchstatelist-indices-gte n matches))
      :hints ('(:expand (<call>
                         (matchstatelist-indices-gte n (list st)))))
      :fn match-concat-rec)

    (defret matchstatelist-indices-gte-of-<fn>
      (implies (<= (nfix n) (matchstate->index st)) (matchstatelist-indices-gte n matches))
      :hints ('(:expand (<call>)))
      :fn match-disjunct-rec)

    (defret matchstatelist-indices-gte-of-<fn>
      (implies (matchstatelist-indices-gte n sts)
               (matchstatelist-indices-gte n matches))
      :hints ('(:expand (<call>
                         (matchstatelist-indices-gte n sts))))
      :fn match-concat-sts-rec)

    (defret matchstatelist-indices-gte-of-<fn>
      (implies (matchstatelist-indices-gte n sts) (matchstatelist-indices-gte n matches))
      :hints ('(:expand (<call>
                         (matchstatelist-indices-gte n sts))))
      :fn match-regex-sts-nonzero-rec)

    (defret matchstatelist-indices-gte-of-<fn>
      (implies (matchstatelist-indices-gte n sts) (matchstatelist-indices-gte n matches))
      :hints ('(:expand (<call>
                         (matchstatelist-indices-gte n sts))))
      :fn match-regex-sts-rec)

    (defret matchstatelist-indices-gte-of-<fn>
      (implies (matchstatelist-indices-gte n sts)
               (matchstatelist-indices-gte n matches))
      :hints ('(:expand ((:free (max) <call>))))
      :fn match-repeat-sts-rec)

    (defret matchstatelist-indices-gte-of-<fn>
      (implies (matchstatelist-indices-gte n sts)
               (matchstatelist-indices-gte n matches))
      :hints ('(:expand (<call>)))
      :fn match-repeat-sts-minimum-rec)

    (defret matchstatelist-indices-gte-of-<fn>
      (implies (<= (nfix n) (matchstate->index st))
               (matchstatelist-indices-gte n matches))
      :hints ('(:expand ((:free (max min) <call>)
                         (:free (x) (matchstatelist-indices-gte n (list st))))))
      :fn match-repeat-rec)
    :hints (("goal" :do-not-induct t))
    :skip-others t)

  (defret-mutual matchstatelist-indices-lte-of-match-regex-rec
    (defret matchstatelist-indices-lte-of-<fn>
      (implies (<= (matchstate->index st) (len (acl2::explode x)))
               (matchstatelist-indices-lte (len (acl2::explode x)) matches))
      :hints ('(:expand (<call>
                         (:free (x st) (matchstatelist-indices-lte x (list st)))))
              (and stable-under-simplificationp
                   '(:in-theory (enable matchstatelist-indices-lte
                                        matchstate-measure))))
      :fn match-regex-rec)

    (defret matchstatelist-indices-lte-of-<fn>
      (implies (<= (matchstate->index st) (len (acl2::explode x)))
               (matchstatelist-indices-lte (len (acl2::explode x)) matches))
      :hints ('(:expand (<call>
                         (:free (x) (matchstatelist-indices-lte x (list st))))))
      :fn match-concat-rec)

    (defret matchstatelist-indices-lte-of-<fn>
      (implies (<= (matchstate->index st) (len (acl2::explode x))) (matchstatelist-indices-lte (len (acl2::explode x)) matches))
      :hints ('(:expand (<call>)))
      :fn match-disjunct-rec)

    (defret matchstatelist-indices-lte-of-<fn>
      (implies (matchstatelist-indices-lte (len (acl2::explode x)) sts)
               (matchstatelist-indices-lte (len (acl2::explode x)) matches))
      :hints ('(:expand (<call>
                         (:free (x) (matchstatelist-indices-lte x sts)))))
      :fn match-concat-sts-rec)

    (defret matchstatelist-indices-lte-of-<fn>
      (implies (matchstatelist-indices-lte (len (acl2::explode x)) sts) (matchstatelist-indices-lte (len (acl2::explode x)) matches))
      :hints ('(:expand (<call>
                         (:free (x) (matchstatelist-indices-lte x sts)))))
      :fn match-regex-sts-nonzero-rec)

    (defret matchstatelist-indices-lte-of-<fn>
      (implies (matchstatelist-indices-lte (len (acl2::explode x)) sts)
               (matchstatelist-indices-lte (len (acl2::explode x)) matches))
      :hints ('(:expand (<call>
                         (:free (x) (matchstatelist-indices-lte x sts)))))
      :fn match-regex-sts-rec)

    (defret matchstatelist-indices-lte-of-<fn>
      (implies (matchstatelist-indices-lte (len (acl2::explode x)) sts)
               (matchstatelist-indices-lte (len (acl2::explode x)) matches))
      :hints ('(:expand ((:free (max) <call>))))
      :fn match-repeat-sts-rec)

    (defret matchstatelist-indices-lte-of-<fn>
      (implies (matchstatelist-indices-lte (len (acl2::explode x)) sts)
               (matchstatelist-indices-lte (len (acl2::explode x)) matches))
      :hints ('(:expand (<call>)))
      :fn match-repeat-sts-minimum-rec)

    (defret matchstatelist-indices-lte-of-<fn>
      (implies (<= (matchstate->index st) (len (acl2::explode x)))
               (matchstatelist-indices-lte (len (acl2::explode x)) matches))
      :hints ('(:expand ((:free (max min) <call>)
                         (:free (x) (matchstatelist-indices-lte x (list st))))))
      :fn match-repeat-rec)
    :hints (("goal" :do-not-induct t))
    :skip-others t)


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

(define charset-range ((x characterp)
                             (y characterp))
  :guard (<= (char-code x) (char-code y))
  :measure (nfix (- (char-code y) (char-code x)))
  :returns (chars character-listp)
  :prepwork ((local (defthm char-codes-not-equal
                      (implies (and (characterp x) (characterp y)
                                    (not (equal x y)))
                               (not (equal (char-code x) (char-code y))))
                      :hints (("goal" :use ((:instance code-char-char-code-is-identity (c x))
                                            (:instance code-char-char-code-is-identity (c y)))
                               :in-theory (disable code-char-char-code-is-identity))))))
  (b* ((x (mbe :logic (acl2::char-fix x) :exec x))
       ((when (mbe :logic (zp (- (char-code y) (char-code x)))
                   :exec (eql x y)))
        (list x))
       (next (code-char (+ 1 (char-code x)))))
    (cons x (charset-range next y))))

(define parse-charset-aux ((x stringp) (index natp))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (chars character-listp)
               (new-index natp :rule-classes :type-prescription))
  :guard (<= index (strlen x))
  :measure (nfix (- (strlen x) (nfix index)))
  :prepwork ()
  (b* (((when (mbe :logic (zp (- (strlen x) (nfix index)))
                   :exec (eql (strlen x) index)))
        (mv "String ended inside charset" nil (lnfix index)))
       (x (lstrfix x))
       (index (lnfix index))
       (char1 (char x index))
       (index (+ 1 index))
       ((when (eql char1 #\]))
        (mv nil nil index))
       ((unless (< index (strlen x)))
        (mv "String ended inside charset" nil index))
       (char2 (char x index))
       ((when (eql char2 #\]))
        (mv nil (list char1) (+ 1 index)))
       ((unless (eql char2 #\-))
        (b* (((mv err chars index) (parse-charset-aux x index)))
          (mv err (cons char1 chars) index)))
       (index (+ 1 index))
       ((unless (< index (strlen x)))
        (mv "String ended inside charset" nil index))
       (char3 (char x index))
       ((when (< (char-code char3) (char-code char1)))
        (mv "Invalid range" nil index))
       (range (charset-range char1 char3))
       ((mv err chars index) (parse-charset-aux x (+ 1 index))))
    (mv err (append range chars) index))
  ///
  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear))

(define parse-charset ((x stringp)
                             (index natp)) ;; after the [
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (pat (implies (not err) (regex-p pat)))
               (new-index natp :rule-classes :type-prescription))
  (b* ((x (lstrfix x))
       (index (lnfix index))
       ((when (<= (strlen x) index))
        (mv "String ended inside charset" nil index))
       ((mv negp index)
        (if (eql (char x index) #\^)
            (mv t (+ 1 index))
          (mv nil index)))
       ((when (<= (strlen x) index))
        (mv "String ended inside charset" nil index))
       ((mv has-closebracket index)
        (if (eql (char x index) #\])
            (mv t (+ 1 index))
          (mv nil index)))
       ((when (<= (strlen x) index))
        (mv "String ended inside charset" nil index))
       ((mv err chars last-index) ;; last-index is past close bracket if no error
        (parse-charset-aux x index))
       ((when err) (mv err nil last-index))
       (chars (if has-closebracket (cons #\] chars) chars)))
    (mv nil (regex-charset (coerce chars 'string) negp) last-index))
  ///
  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :hints (("goal" :expand ((parse-charset-aux x index))))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear))


(define parse-range ((x stringp)
                           (index natp)) ;; after the {
  :guard (<= index (strlen x))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (min natp :rule-classes :type-prescription)
               (max acl2::maybe-natp :rule-classes :type-prescription)
               (new-index natp :rule-classes :type-prescription))
  :prepwork ((local (defthm len-of-nthcdr
                      (implies (force (<= (nfix n) (len x)))
                               (equal (len (nthcdr n x))
                                      (- (len x) (nfix n))))
                      :hints(("Goal" :in-theory (enable nthcdr)))))
             (local (in-theory (disable len nthcdr))))
  (b* ((x (lstrfix x))
       (index (lnfix index))
       ((when (eql index (strlen x)))
        (mv "String ended inside range expression (start)" 0 0 index))
       ((mv min len1) (str::parse-nat-from-string x 0 0 index (strlen x)))
       (index (+ len1 index))
       ((when (eql index (strlen x)))
        (mv "String ended inside range expression (after min index)" 0 0 index))
       (nextchar (char x index))
       ((when (eql nextchar #\}))
        (mv nil min min (+ 1 index)))
       ((unless (eql nextchar #\,))
        (mv "Malformed range -- expecting comma" 0 0 index))
       (index (+ 1 index))
       ((when (eql index (strlen x)))
        (mv "String ended inside range expression (after comma)" 0 0 index))
       ((mv val2 len2) (str::parse-nat-from-string x 0 0 index (strlen x)))
       (max (and (not (eql len2 0)) val2))
       (index (+ len2 index))
       ((when (eql index (strlen x)))
        (mv "String ended inside range expression (after max index)" 0 0 index))
       (nextchar (char x index))
       ((unless (eql nextchar #\}))
        (mv "Malformed range -- expecting close brace" 0 0 index)))
    (mv nil min max (+ 1 index)))
  ///
  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear))


(local (include-book "std/lists/take" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(encapsulate nil
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
           :hints(("Goal" :in-theory (enable append acl2::take-redefinition nthcdr len list-fix
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
           :hints(("Goal" :in-theory (enable append acl2::take-redefinition nthcdr len list-fix
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
           (iff (equal (str::cat x y) z)
                (and (stringp z)
                     (<= (len (acl2::explode x)) (len (acl2::explode z)))
                     (equal (take (len (acl2::explode x)) (acl2::explode z))
                            (acl2::explode x))
                     (equal (nthcdr (len (acl2::explode x)) (acl2::explode z))
                            (acl2::explode y))))))

  (local (defthm character-listp-of-take
           (implies (and (character-listp x)
                         (<= (nfix n) (len x)))
                    (character-listp (take n x)))))

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
           :hints(("Goal" :in-theory (enable nthcdr)
                   :induct (nthcdr-of-take-ind n m x))
                  (and stable-under-simplificationp
                       '(:in-theory (enable nfix))))))

  (local (defthm nthcdr-of-nthcdr
           (equal (nthcdr n (nthcdr m x))
                  (nthcdr (+ (nfix n) (nfix m)) x))))
  
  (defthm match-exact-of-cat
    (Equal (match-exact (str::cat x y) str index mode)
           (let ((x-index (match-exact x str index mode)))
             (and x-index
                  (match-exact y str x-index mode))))
    :hints(("Goal" :in-theory (enable match-exact)))))

(local (in-theory (disable str::fast-string-append)))


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

(define regex-concat2 ((x regex-p) (y regex-p))
  :returns (res regex-p)
  (regex-case x
    :exact
    (regex-case y
      :exact (regex-exact (str::cat x.str y.str))
      :concat (b* (((when (atom y.lst))
                    (regex-fix x))
                   (y1 (car y.lst)))
                (regex-case y1
                  :exact (regex-concat (cons (regex-exact (str::cat x.str y1.str))
                                             (cdr y.lst)))
                  :otherwise (regex-concat (cons x y.lst))))
      :otherwise (regex-concat (list x y)))
    :otherwise
    (regex-case y
      :exact (if (equal y.str "")
                 (regex-fix x)
               (regex-concat (list x y)))
      :otherwise (regex-concat (list x y))))
  ///
  (local (include-book "clause-processors/use-by-hint" :dir :system))
  (local (defmacro hq (x) `(acl2::hq ,x)))
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
           :hints(("Goal" :in-theory (enable match-exact)))))

  (local (defthm match-regex-sts-rec-of-empty-exact
           (implies (and (Equal (regex-kind x) :exact)
                         (Equal (regex-exact->str x) "")
                         (matchstatelist-indices-lte (strlen str) sts))
                    (equal (match-regex-sts-rec x str sts mode)
                           (matchstatelist-fix sts)))
           :hints(("Goal" :in-theory (enable match-regex-sts-rec
                                             matchstatelist-indices-lte)
                   :induct (len sts)))))

  (defret match-regex-rec-of-regex-concat2
    (implies (<= (matchstate->index st) (strlen str))
             (undup-equiv (match-regex-rec res str st mode)
                          (match-regex-rec (regex-concat (list x y)) str st mode)))))


(define regex-disjunct2 ((x regex-p) (y regex-p))
  :returns (res regex-p)
  (regex-case y
    :disjunct (regex-disjunct (cons x y.lst))
    :otherwise (regex-disjunct (list x y)))
  ///
  (defret match-regex-rec-of-regex-disjunct2
    (implies (<= (matchstate->index st) (strlen str))
             (undup-equiv (match-regex-rec res str st mode)
                          (match-regex-rec (regex-disjunct (list x y)) str st mode)))))


;; regex = concat
;;         concat | regex

;; concat = repeat
;;          repeat concat

;; repeat = atom
;;          atom repeatop

;; atom = group
;;        primitive


;; group = ( regex )
;;         (?: regex )           (noncapturing)
;;         (?i: regex )          (noncapturing, case insensitive)
;;         (?^i: regex )         (noncapturing, case sensitive)
;;         (?<name> regex )
;;         (?= regex )           (zero-length lookahead)
;;         (?! regex )           (zero-length lookahead, negated)


;; primitive = character
;;             .
;;             [ characterclass ]
;;             [ ^ characterclass ]
;;             ^
;;             $
;;             backref
;;             \ metacharacter       (escape)
;;             \ charsetchar

;; backref = \ digit
;;           \g digit
;;           \g{number}
;;           \g{name}
;;           \k{name}
;;           \k<name>
;;           \k'name'

;; repeatop = repeatbase 
;;            repeatbase repeatmod

;; repeatbase = *
;;              +
;;              ?
;;              {min}
;;              {min,}
;;              {min,max}

;; repeatmod = ?      (nongreedy)
;;             +      (nonbacktracking)


(define parse-repeatbase ((x stringp)
                          (index natp))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (min natp :rule-classes :type-prescription)
               (max maybe-natp :rule-classes :type-prescription)
               (new-index natp :rule-classes :type-prescription))
  :guard (<= index (strlen x))
  ;; repeatbase = *
  ;;              +
  ;;              ?
  ;;              {min}
  ;;              {min,}
  ;;              {min,max}
  (b* ((index (lnfix index))
       ((when (<= (strlen x) index))
        (mv "End of string when parsing repeatbase" 0 0 index))
       (char (char x index)))
    (case char
      (#\* (mv nil 0 nil (+ 1 index)))
      (#\+ (mv nil 1 nil (+ 1 index)))
      (#\? (mv nil 0 1   (+ 1 index)))
      (#\{ (b* (((mv err min max new-index) (parse-range x (+ 1 index)))
                ((when err) (mv err 0 0 index)))
             (mv nil min max new-index)))
      (t (mv "Not a repeatbase" 0 0 (lnfix index)))))
  ///
  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear)

  (defret no-change-of-<fn>
    (implies err
             (equal new-index (nfix index)))))


(defenum repeatmod-p (:? :+ nil))
        
(define parse-repeatmod ((x stringp)
                         (index natp))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (repeatmod repeatmod-p)
               (new-index natp :rule-classes :type-prescription))
  :guard (<= index (strlen x))
  ;; repeatmod = ?      (nongreedy)
  ;;             +      (nonbacktracking)
  (b* ((index (lnfix index))
       ((when (<= (strlen x) index))
        (mv "End of string when parsing repeatmod" nil index))
       (char (char x index)))
    (case char
      (#\? (mv nil :? (+ 1 index)))
      (#\+ (mv nil :+ (+ 1 index)))
      (t (mv "Not a repeatmod" nil index))))
  ///
  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear)

  (defret no-change-of-<fn>
    (implies err
             (equal new-index (nfix index)))))
       

(define parse-repeatop ((x stringp)
                        (index natp))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (min natp :rule-classes :type-prescription)
               (max maybe-natp :rule-classes :type-prescription)
               (repeatmod repeatmod-p)
               (new-index natp :rule-classes :type-prescription))
  :guard (<= index (strlen x))
  (b* (((mv err min max index) (parse-repeatbase x index))
       ((when err) (mv err 0 0 nil index))
       ((mv err repeatmod index) (parse-repeatmod x index))
       ((when err) (mv nil min max nil index)))
    (mv nil min max repeatmod index))
  ///
  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear)

  (defret no-change-of-<fn>
    (implies err
             (equal new-index (nfix index)))))
  
(define match-string-at ((target stringp)
                         (x stringp)
                         (index natp))
  :returns (mv (matchedp booleanp :rule-classes :type-prescription)
               (new-index natp :rule-classes :type-prescription))
  :guard (<= index (strlen x))
  :prepwork ((local (in-theory (disable (force)))))
  (b* ((match (str::strprefixp-impl (lstrfix target)
                                     (lstrfix x)
                                     0 (lnfix index)
                                     (strlen target)
                                     (strlen x))))
    (if match
        (mv t (+ (strlen target) (lnfix index)))
      (mv nil (lnfix index))))
  ///

  (local (include-book "std/lists/nthcdr" :dir :system))

  (defret new-index-less-than-length-of-<fn>
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index
                 (len (acl2::explode x))))
    :hints (("goal" :use ((:instance acl2::len-when-prefixp
                           (x (acl2::Explode target))
                           (y (nthcdr index (acl2::explode x)))))
             :in-theory (disable acl2::len-when-prefixp)))
    :rule-classes :linear)

  (defret new-index-increasing-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (defret new-index-increasing-strong-of-<fn>
    (implies (and matchedp (not (equal 0 (strlen target))))
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret no-change-of-<fn>
    (implies (not matchedp)
             (equal new-index (lnfix index))))

  (defret measure-decr-of-match-string-at
    (<= (nfix (+ (len (acl2::explode x)) (- new-index)))
        (nfix (+ (- (nfix index)) (len (acl2::explode x)))))
    :hints(("Goal" :in-theory (e/d (nfix) (match-string-at
                                           new-index-increasing-of-match-string-at))
            :use new-index-increasing-of-match-string-at))
    :rule-classes :linear)

  (defret index-lte-len-when-match-string-at-nonempty
    (implies (and matchedp (not (equal 0 (strlen target))))
             (<= (nfix index) (len (acl2::explode x))))
    :rule-classes :forward-chaining)

  (defret new-index-less-than-length-of-<fn>-when-matched-nonempty
    (implies (and matchedp (not (equal 0 (strlen target))))
             (<= new-index
                 (len (acl2::explode x))))
    :hints (("goal" :use ((:instance new-index-less-than-length-of-match-string-at)
                          (:instance index-lte-len-when-match-string-at-nonempty))
             :in-theory (disable new-index-less-than-length-of-match-string-at
                                 index-lte-len-when-match-string-at-nonempty
                                 match-string-at)))
    :rule-classes :linear)

  (defret measure-decr-of-match-string-at-strong
    (implies (and matchedp (not (equal 0 (strlen target))))
             (< (nfix (+ (len (acl2::explode x)) (- new-index)))
                (nfix (+ (- (nfix index)) (len (acl2::explode x))))))
    :hints(("Goal" :in-theory (e/d (nfix) (match-string-at
                                           new-index-increasing-strong-of-match-string-at))
            :use (new-index-increasing-strong-of-match-string-at
                  index-lte-len-when-match-string-at-nonempty)))
    :rule-classes :linear))

(acl2::def-b*-binder when-match-string
  :body
  (b* ((target (first acl2::args))
       ((unless (stringp target))
        (er hard? 'match-string "Target must be a string"))
       (x (or (second acl2::args) 'x))
       (index (or (third acl2::args) 'index)))
    `(b* (((mv matchedp index) (match-string-at ,target ,x ,index))
          ((when matchedp) . ,acl2::forms))
       ,acl2::rest-expr)))

(acl2::def-b*-binder unless-match-string
  :body
  (b* ((target (first acl2::args))
       ((unless (stringp target))
        (er hard? 'match-string "Target must be a string"))
       (x (or (second acl2::args) 'x))
       (index (or (third acl2::args) 'index)))
    `(b* (((mv matchedp index) (match-string-at ,target ,x ,index))
          ((unless matchedp) . ,acl2::forms))
       ,acl2::rest-expr)))



(define get-charset ((str stringp))
  :returns (pat (implies pat (regex-p pat)))
  (b* (((mv err charset &) (parse-charset (str::cat (lstrfix str) "]") 0))
       ((when err) (raise "Error parsing charset: ~x0 -- ~s1" (lstrfix str) err)))
    charset))

(defmacro defcharset (letter str)
  `(table charset-table ,letter (get-charset ,str)))

(defcharset #\w "a-zA-Z0-9_")
(defcharset #\W "^a-zA-Z0-9_")
(defcharset #\d "0-9")
(defcharset #\D "^0-9")
(defcharset #\s (coerce '(#\Space #\Tab #\Newline #\Page #\Return) 'string))
(defcharset #\S (coerce '(#\^ #\Space #\Tab #\Newline #\Page #\Return) 'string))
(defcharset #\h (coerce '(#\Space #\Tab) 'string))
(defcharset #\H (coerce '(#\^ #\Space #\Tab) 'string))
(defcharset #\v (coerce '(#\Newline #\Page #\Return) 'string))
(defcharset #\V (coerce '(#\^ #\Newline #\Page #\Return) 'string))

(acl2::defconsts *charset-table* (table-alist 'charset-table (w state)))

(define charset-char-regex ((x))
  :returns (pat (implies pat (regex-p pat)))
  (cdr (assoc x *charset-table*)))
  

;; backref = \ digit
;;           \g digit
;;           \g{number}
;;           \g{name}
;;           \k{name}
;;           \k<name>
;;           \k'name'


(define find-substr ((target stringp)
                     (x stringp)
                     (index natp))
  :returns (pos maybe-natp :rule-classes :type-prescription)
  :guard (<= index (strlen x))
  :prepwork ((local (in-theory (disable (force)))))
  (str::strpos-fast (lstrfix target)
                    (lstrfix x)
                    (lnfix index)
                    (strlen target)
                    (strlen x))
  ///
  (local (defthm listpos-bound
           (implies (acl2::listpos x y)
                    (<= (acl2::listpos x y) (- (len y) (len x))))
           :hints(("Goal" :in-theory (enable acl2::listpos)))
           :rule-classes :linear))

  (local (include-book "std/lists/nthcdr" :dir :system))

  (defret new-index-of-<fn>
    (implies pos
             (<= (nfix index) pos))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (and pos
                  (<= (nfix index) (len (acl2::explode x))))
             (<= pos (- (len (acl2::explode x)) (len (acl2::explode target)))))
    :rule-classes :linear))

(define parse-k-backref ((x stringp)
                         (index natp))
  :guard (<= index (strlen x))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (pat (implies (not err) (regex-p pat)))
               (new-index natp :rule-classes :type-prescription))
;;           \k{name}
;;           \k<name>
;;           \k'name'
  (b* ((index (lnfix index))
       ((when (<= (strlen x) (lnfix index)))
        (mv "EOS parsing \\k backref" nil index))
       (char (char x index))
       (end-delim (case char
                    (#\{ "}")
                    (#\< ">")
                    (#\' "'")
                    (t nil)))
       ((unless end-delim)
        (mv "Bad delimiter in \\k backref" nil index))
       (idx (find-substr end-delim x index))
       ((unless idx)
        (mv "Unclosed name in \\k capture form" nil index))
       (name (subseq x index idx))
       (index (+ 1 idx)))
    (mv nil (regex-backref name) index))
  ///

  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear)

  (defret no-change-of-<fn>
    (implies err
             (equal new-index (nfix index)))))

(define parse-g-backref ((x stringp)
                         (index natp))
  :guard (<= index (strlen x))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (pat (implies (not err) (regex-p pat)))
               (new-index natp :rule-classes :type-prescription))
;;           \g digit
;;           \g{number}
;;           \g{name}
  (b* ((index (lnfix index))
       ((when (<= (strlen x) (lnfix index)))
        (mv "EOS parsing \\g backref" nil index))
       (char (char x index))
       ((when (str::digitp char))
        (b* (((mv val len) (str::parse-nat-from-string x 0 0 index (strlen x)))
             (index (+ index len)))
          (mv nil (regex-backref val) index)))
       (index (+ 1 index))
       ((unless (eql char #\{))
        (mv "Bad delimiter in \\g backref" nil index))
       (idx (find-substr "}" x index))
       ((unless idx)
        (mv "Unclosed name in \\g capture form" nil index))
       (name (subseq x index idx))
       ((mv val len) (str::parse-nat-from-string name 0 0 0 (strlen name)))
       ((when (eql len (strlen name)))
        (mv nil (regex-backref val) (+ 1 idx))))
    (mv nil (regex-backref name) (+ 1 idx)))
  ///

  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (local (defthm len-of-take-leading-digits-when-car-digitp
           (implies (str::digitp (car x))
                    (< 0 (len (str::take-leading-digits x))))
           :hints(("Goal" :in-theory (enable str::take-leading-digits)))
           :rule-classes :linear))

  (local (defthm len-of-take-leading-digits-upper-bound
           (<= (len (str::take-leading-digits x)) (len x))
           :hints(("Goal" :in-theory (enable str::take-leading-digits)))
           :rule-classes :linear))


  (local (include-book "std/lists/nthcdr" :dir :system))
  ;; (local (defthm car-of-nthcdr
  ;;          (equal (car (nthcdr n x)) (nth n x))))

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear))

(define parse-primitive ((x stringp)
                         (index natp))
  :guard (<= index (strlen x))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (pat (implies (not err) (regex-p pat)))
               (new-index natp :rule-classes :type-prescription))
  ;; primitive = character
  ;;             .
  ;;             [ characterclass ]
  ;;             [ ^ characterclass ]
  ;;             ^
  ;;             $
  ;;             backref
  ;;             \ metacharacter       (escape)
  ;;             \ charsetchar

  (b* ((index (lnfix index))
       ((when (<= (strlen x) (lnfix index)))
        (mv "EOS parsing primitive" nil index))
       (char (char x index))
       (index (+ 1 index)))
    (case char
      (#\. (mv nil (regex-charset "" t) index))
      (#\^ (mv nil (regex-start) index))
      (#\$ (mv nil (regex-end) index))
      (#\[ (parse-charset x index))
      (#\\
       (b* (((when (<= (strlen x) (lnfix index)))
             (mv "EOS after backslash" nil index))
            (char (char x index))
            (charset (charset-char-regex char))
            ((when charset)
             (mv nil charset (+ 1 index)))
            ((when (str::digitp char))
             (b* (((mv val len) (str::parse-nat-from-string x 0 0 index (strlen x)))
                  (index (+ index len)))
               (mv nil (regex-backref val) index)))
            (index (+ 1 index)))
         (case char
           ((#\\ #\^ #\. #\$ #\| #\( #\) #\[ #\] #\* #\+ #\? #\{ #\})
            (mv nil (regex-exact (coerce (list char) 'string)) index))
           (#\g ;; various forms of backref
            (parse-g-backref x index))
           (#\k ;; other forms of backref
            (parse-k-backref x index))
           (t (mv (str::cat "Unrecognized escape: \\" (coerce (list char) 'string)) nil index)))))
      ((#\| #\( #\) #\] #\* #\+ #\? #\{ #\})
       (mv "Found metacharacter while parsing primitive" nil index))
      (t (mv nil (regex-exact (coerce (list char) 'string)) index))))
  ///

  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (local (defthm len-of-take-leading-digits-when-car-digitp
           (implies (str::digitp (car x))
                    (< 0 (len (str::take-leading-digits x))))
           :hints(("Goal" :in-theory (enable str::take-leading-digits)))
           :rule-classes :linear))

  (local (defthm len-of-take-leading-digits-upper-bound
           (<= (len (str::take-leading-digits x)) (len x))
           :hints(("Goal" :in-theory (enable str::take-leading-digits)))
           :rule-classes :linear))


  (local (include-book "std/lists/nthcdr" :dir :system))
  ;; (local (defthm car-of-nthcdr
  ;;          (equal (car (nthcdr n x)) (nth n x))))

  (local (Defthm len-of-cdr
           (implies (consp x)
                    (equal (len (cdr x))
                           (+ -1 (len x))))))

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear))
            
             
         
       



(defines parse-regex-rec
  (define parse-regex-rec ((x stringp)
                           (index natp)
                           (br-index natp))
    :verify-guards nil
    :guard (<= index (strlen x))
    :measure (list (- (strlen x) (nfix index))  10)
    :well-founded-relation acl2::nat-list-<
    :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
                 (regex (implies (not err) (regex-p regex)))
                 (new-index natp :rule-classes :type-prescription)
                 (new-br-index natp :rule-classes :type-prescription))
    ;; regex = concat
    ;;         concat | regex
    (b* (((mv concat new-index br-index) (parse-concat-rec x index br-index))
         ((unless (mbt (<= (lnfix index) (nfix new-index))))
          (mv "Impossible" nil new-index br-index))
         (index new-index)
         ((unless-match-string "|" x index)
          (mv nil concat index br-index))
         ((mv err rest index br-index) (parse-regex-rec x index br-index))
         ((when err)
          (mv err nil index br-index)))
      (mv nil (regex-disjunct2 concat rest) index br-index)))

  (define parse-concat-rec ((x stringp)
                            (index natp)
                            (br-index natp))
    :guard (<= index (strlen x))
    :measure (list (- (strlen x) (nfix index)) 9)
    ;; No errors!
    :returns (mv (regex regex-p)
                 (new-index natp :rule-classes :type-prescription)
                 (new-br-index natp :rule-classes :type-prescription))
    ;; concat = ""           (empty)
    ;;          repeat concat
    (b* (((mv err repeat new-index new-br-index) (parse-repeat-rec x index br-index))
         ((when err) (mv (regex-exact "") (lnfix index) (lnfix br-index)))
         ((unless (mbt (and (< (lnfix index) (nfix new-index))
                            (< (lnfix index) (strlen x)))))
          ;; Impossible
          (mv (regex-exact "") (lnfix index) (lnfix br-index)))
         (index new-index)
         (br-index new-br-index)
         ((mv rest new-index new-br-index) (parse-concat-rec x index br-index)))
      (mv (regex-concat2 repeat rest) new-index new-br-index)))


  (define parse-repeat-rec ((x stringp)
                            (index natp)
                            (br-index natp))
    :guard (<= index (strlen x))
    :measure (list (- (strlen x) (nfix index)) 8)
    :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
                 (regex (implies (not err) (regex-p regex)))
                 (new-index natp :rule-classes :type-prescription)
                 (new-br-index natp :rule-classes :type-prescription))
    ;; repeat = atom
    ;;          atom repeatop
    (b* (((mv err atom index br-index) (parse-atom-rec x index br-index))
         ((when err) (mv err nil index br-index))
         ((mv err min max repeatmod index) (parse-repeatop x index))
         ((when err)
          (mv nil atom index br-index)))
      (mv nil
          (case repeatmod
            (:? (regex-reverse-pref (make-regex-repeat :pat (regex-reverse-pref atom) :min min :max max)))
            (:+ (regex-no-backtrack (make-regex-repeat :pat atom :min min :max max)))
            (t  (make-regex-repeat :pat atom :min min :max max)))
          index br-index)))

  (define parse-atom-rec ((x stringp)
                          (index natp)
                          (br-index natp))
    :guard (<= index (strlen x))
    :measure (list (- (strlen x) (nfix index)) 7)
    :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
                 (regex (implies (not err) (regex-p regex)))
                 (new-index natp :rule-classes :type-prescription)
                 (new-br-index natp :rule-classes :type-prescription))
    ;; atom = group
    ;;        primitive
    (b* ((index (lnfix index))
         ((when-match-string "(" x index)
          (parse-group-rec x index br-index))
         ((mv err result new-index) (parse-primitive x index)))
      (mv err result new-index (lnfix br-index))))

  (define parse-group-rec ((x stringp)
                           (index natp)
                           (br-index natp))
    :guard (<= index (strlen x))
    :measure (list (- (strlen x) (nfix index)) 20)
    :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
                 (regex (implies (not err) (regex-p regex)))
                 (new-index natp :rule-classes :type-prescription)
                 (new-br-index natp :rule-classes :type-prescription))
;; group = ( regex )
;;         (?: regex )           (noncapturing)
;;         (?i: regex )          (noncapturing, case insensitive)
;;         (?^i: regex )         (noncapturing, case sensitive)
;;         (?<name> regex )
;;         (?= regex )           (zero-length lookahead)
;;         (?! regex )           (zero-length lookahead, negated)
    ;; Open paren has already been read.
    (b* ((br-index (lnfix br-index))
         ((when-match-string "?:" x index)
          ;; Noncapturing group.
          (b* (((mv err pat index br-index)
                (parse-regex-rec x index br-index))
               ((when err) (mv err nil index br-index))
               ((unless-match-string ")" x index)
                (mv "Expected close paren to finish group" nil index br-index)))
            (mv nil pat index br-index)))
         ((when-match-string "?i:" x index)
          ;; Noncapturing, case-insensitive
          (b* (((mv err pat index br-index)
                (parse-regex-rec x index br-index))
               ((when err) (mv err nil index br-index))
               ((unless-match-string ")" x index)
                (mv "Expected close paren to finish group" nil index br-index)))
            (mv nil (regex-case-sens pat nil) index br-index)))
         ((when-match-string "?^i:" x index)
          ;; Noncapturing, case-sensitive
          (b* (((mv err pat index br-index)
                (parse-regex-rec x index br-index))
               ((when err) (mv err nil index br-index))
               ((unless-match-string ")" x index)
                (mv "Expected close paren to finish group" nil index br-index)))
            (mv nil (regex-case-sens pat t) index br-index)))
         ((when-match-string "?=" x index)
          ;; Zero-length lookahead
          (b* (((mv err pat index br-index)
                (parse-regex-rec x index br-index))
               ((when err) (mv err nil index br-index))
               ((unless-match-string ")" x index)
                (mv "Expected close paren to finish group" nil index br-index)))
            (mv nil (regex-zerolength pat nil) index br-index)))
         ((when-match-string "?!" x index)
          ;; Zero-length lookahead, negated
          (b* (((mv err pat index br-index)
                (parse-regex-rec x index br-index))
               ((when err) (mv err nil index br-index))
               ((unless-match-string ")" x index)
                (mv "Expected close paren to finish group" nil index br-index)))
            (mv nil (regex-zerolength pat t) index br-index)))
         ((when-match-string "?<" x index)
          (b* ((idx (find-substr ">" x index))
               ((unless idx)
                (mv "Unclosed name in ?< capture form" nil index br-index))
               (name (subseq x index idx))
               (index (+ 1 idx))
               ;; Note: Perl indexes named capture groups.
               (my-br-index br-index)
               ((mv err pat index br-index) (parse-regex-rec x index (+ 1 (lnfix br-index))))
               ((when err) (mv err nil index br-index))
               ((unless-match-string ")" x index)
                (mv "Expected close paren to finish group" nil index br-index)))
            (mv nil (regex-group (regex-group pat name) my-br-index) index br-index)))

         ;; Otherwise, default capture group.
         (my-br-index br-index)
         ((mv err pat index br-index)
          (parse-regex-rec x index (+ 1 (lnfix br-index))))
         ((when err) (mv err nil index br-index))
         ((unless-match-string ")" x index)
          (mv "Expected close paren to finish group" nil index br-index)))
      (mv nil (regex-group pat my-br-index) index br-index)))
  ///
  (local (defconsts *parse-regex-fns*
           (acl2::getpropc 'parse-regex-rec 'acl2::recursivep nil (w state))))
  
  (local (make-event `(in-theory (disable . ,*parse-regex-fns*))))

  (local (defun parse-regex-mr-fns (name body hints rule-classes fns)
           (if (atom fns)
               nil
             (cons `(defret ,name
                      ,body :hints ,hints :rule-classes ,rule-classes :fn ,(car fns))
                   (parse-regex-mr-fns name body hints rule-classes (cdr fns))))))

  (local (defun parse-regex-mutual-recursion (name body hints rule-classes omit)
           `(defret-mutual ,name
              ,@(parse-regex-mr-fns name body hints rule-classes
                                    (set-difference-eq *parse-regex-fns* omit))
              :skip-others t)))

  (defmacro def-parse-regex-thm (name body &key hints rule-classes omit)
    `(make-event (parse-regex-mutual-recursion ',name ',body ',hints ',rule-classes ',omit)))

  (def-parse-regex-thm new-index-nondecr-of-<fn>
    (<= (nfix index) new-index)
    :hints ('(:expand <call>))
    :rule-classes :linear)

  (def-parse-regex-thm new-index-incr-of-<fn>
    (implies (not err)
             (< (nfix index) new-index))
    :hints ('(:expand <call>))
    :rule-classes :linear
    :omit (parse-regex-rec parse-concat-rec))

  (def-parse-regex-thm new-index-upper-bound-of-<fn>
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :hints ('(:expand <call>))
    :rule-classes :linear)

  (local (defret index-less-than-length-when-parse-repeat-rec-no-error
           (implies (and (not err)
                         (natp index)
                         (<= index (len (acl2::explode x))))
                    (< index (len (acl2::explode x))))
           :hints (("goal" :use ((:instance new-index-incr-of-parse-repeat-rec))
                    :in-theory (disable new-index-incr-of-parse-repeat-rec)))
           :rule-classes :forward-chaining
           :fn parse-repeat-rec))

  (verify-guards parse-regex-rec))


         
