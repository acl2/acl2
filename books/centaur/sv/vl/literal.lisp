; SV - Symbolic Vector Hardware Analysis Framework
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

(in-package "VL")

;; Utility to translate a 4vec value into a VL expression given a type context.

(include-book "centaur/vl/mlib/arithclass" :dir :system)
(include-book "../svex/4vec")

(local (include-book "centaur/vl/util/default-hints" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (in-theory (disable (tau-system))))
(local (std::add-default-post-define-hook :fix))





(define vl-upperlower-to-bitlist ((upper integerp)
                                  (lower integerp)
                                  (width natp))
  :returns (res vl-bitlist-p "MSB-first")
  (b* (((when (zp width)) nil)
       (width (1- width))
       (bit (if (logbitp width upper)
                (if (logbitp width lower)
                    :vl-1val
                  :vl-xval)
              (if (logbitp width lower)
                  :vl-zval
                :vl-0val))))
    (cons bit (vl-upperlower-to-bitlist upper lower width)))
  ///
  (defret consp-of-vl-upperlower-to-bitlist
    (equal (consp res)
           (posp width))))

(define vl-4vec-to-value ((x sv::4vec-p)
                          (width posp)
                          &key
                          ((signedness vl-exprsign-p) ':vl-signed))
  :prepwork ((local (include-book "centaur/bitops/ihsext-basics" :dir :system))
             (local (in-theory (disable unsigned-byte-p acl2::loghead)))
             (local (defthm 4vec->lower-of-4vec-zero-ext
                      (implies (natp n)
                               (unsigned-byte-p n (sv::4vec->lower (sv::4vec-zero-ext (sv::2vec n) x))))
                      :hints(("Goal" :in-theory (e/d (sv::2vec-p sv::2vec sv::2vec->val sv::4vec-zero-ext))))))
             (local (defthm 4vec->lower-of-4vec-zero-ext-bounds
                      (implies (natp n)
                               (and (<= 0 (sv::4vec->lower (sv::4vec-zero-ext (sv::2vec n) x)))
                                    (< (sv::4vec->lower (sv::4vec-zero-ext (sv::2vec n) x)) (expt 2 n))))
                      :hints(("Goal" :use 4vec->lower-of-4vec-zero-ext
                              :in-theory (e/d (unsigned-byte-p)
                                              (4vec->lower-of-4vec-zero-ext)))))))
  :returns (val vl-value-p)
  (b* ((width (lposfix width))
       (trunc (sv::4vec-zero-ext (sv::2vec width) x))
       ((when (sv::2vec-p trunc))
        (b* ((val (sv::2vec->val trunc)))
          (make-vl-constint :origwidth width
                            :origsign signedness
                            :wasunsized t
                            :value val)))
       (val (vl-upperlower-to-bitlist (sv::4vec->upper trunc)
                                      (sv::4vec->lower trunc)
                                      width)))
    (make-vl-weirdint :bits val
                      :origsign signedness
                      :wasunsized t)))





(define vl-structmemberlist-sizable ((x vl-structmemberlist-p))
  :guard (vl-structmemberlist-resolved-p x)
  (b* (((mv ?err sizes) (vl-structmemberlist-sizes x)))
    ;; (and (not err)
    (not (member nil sizes))))

(define vl-datatype-sizable ((x vl-datatype-p))
  :guard (vl-datatype-resolved-p x)
  (b* (((mv ?err size) (vl-datatype-size x)))
    (natp size))
  ///

  (defthm-vl-datatype-size-flag
    (defthm vl-datatype-size-not-err-when-size
      (b* (((mv err size) (vl-datatype-size x)))
        (implies size
                 (not err)))
      :hints ('(:expand ((vl-datatype-size x))))
      :flag vl-datatype-size)
    (defthm vl-structmemberlist-sizes-not-err-when-sizes
      (b* (((mv err sizes) (vl-structmemberlist-sizes x)))
        (implies (not (member nil sizes))
                 (not err)))
      :hints ('(:expand ((vl-structmemberlist-sizes x))))
      :flag vl-structmemberlist-sizes))
  

  (defthm vl-datatype-sizable-forward
    (implies (vl-datatype-sizable x)
             (b* (((mv err size) (vl-datatype-size x)))
               (and (not err) (natp size))))
    :rule-classes :forward-chaining)

  (local (in-theory (e/d (vl-structmemberlist-sizable)
                         (member append))))

  (defthm vl-structmemberlist-sizable-implies
    (implies (and (vl-structmemberlist-sizable x)
                  (consp x))
             (and (b* (((mv err sizes) (vl-structmemberlist-sizes x)))
                    (and (not err)
                         (not (member nil sizes))))
                  (vl-datatype-sizable (vl-structmember->type (car x)))
                  (vl-structmemberlist-sizable (cdr x))))
    :hints(("Goal" :in-theory (enable vl-structmemberlist-sizes))))

  (local (in-theory (disable vl-structmemberlist-sizable-implies)))

  (defthmd vl-datatype-sizable-implies
    (implies (vl-datatype-sizable x)
             (and (b* (((mv err size) (vl-datatype-size x)))
                    (and (not err) (natp size)))
                  (vl-dimensionlist-resolved-p (vl-datatype->udims x))
                  (vl-dimensionlist-resolved-p (vl-datatype->pdims x))
                  (posp (vl-dimensionlist-total-size (vl-datatype->udims x)))
                  (posp (vl-dimensionlist-total-size (vl-datatype->pdims x)))
                  (implies (vl-datatype-case x :vl-coretype)
                           (posp (vl-coredatatype-info->size (vl-coretypename->info (vl-coretype->name x)))))
                  (implies (vl-datatype-case x :vl-struct)
                           (vl-structmemberlist-sizable (vl-struct->members x)))
                  (implies (vl-datatype-case x :vl-union)
                           (vl-structmemberlist-sizable (vl-union->members x)))
                  (implies (vl-datatype-case x :vl-enum)
                           (vl-datatype-sizable (vl-enum->basetype x)))
                  (implies (vl-datatype-case x :vl-usertype)
                           (and (vl-usertype->res x)
                                (vl-datatype-sizable (vl-usertype->res x))))))
    :hints ((and stable-under-simplificationp
                 '(:expand ((Vl-datatype-size x)))))))

(define vl-literal-expr-for-zero-size ((signedp booleanp))
  :returns (0size-expr vl-expr-p)
  (make-vl-pattern
   :pattype (make-vl-struct :members nil :packedp t :signedp signedp)
   :pat (vl-assignpat-positional nil)))


(define vl-literal-expr-from-4vec/vector-type ((type vl-datatype-p)
                                               (x sv::4vec-p))
  :guard (and (vl-datatype-resolved-p type)
              (vl-datatype-sizable type)
              (b* (((mv ?caveat class) (vl-datatype-arithclass type)))
                (vl-integer-arithclass-p class)))
  :guard-hints (("goal" :in-theory (enable vl-datatype-sizable-implies)))
  :returns (mv (expr vl-expr-p)
               (rest sv::4vec-p))
  (b* (((mv ?err size) (vl-datatype-size type))
       ((mv ?caveat class) (vl-datatype-arithclass type))
       (exprsign (vl-integer-arithclass->exprsign class))
       ((when (eql 0 size))
        ;; horrible.  But this expression will produce an svex-x without
        ;; warnings at least for an empty struct type, and maybe for other
        ;; 0-size, packed types.
        (mv (vl-literal-expr-for-zero-size (eq exprsign :vl-signed))
            (sv::4vec-fix x))))
    (mv (make-vl-literal
         :val (vl-4vec-to-value x size :signedness exprsign))
        (sv::4vec-rsh (sv::2vec size) x))))

(defthm vl-datatype-count-of-vl-datatype-update-udims
  (<= (vl-datatype-count (vl-datatype-update-udims nil x)) (vl-datatype-count x))
  :hints(("Goal" :in-theory (enable vl-datatype-count
                                    vl-datatype-update-udims
                                    vl-datatype-update-dims)
          :expand ((vl-datatype-count x))))
  :rule-classes :linear)

(defthm vl-datatype-count-of-vl-datatype-update-pdims
  (<= (vl-datatype-count (vl-datatype-update-pdims nil x)) (vl-datatype-count x))
  :hints(("Goal" :in-theory (enable vl-datatype-count
                                    vl-datatype-update-pdims
                                    vl-datatype-update-dims)
          :expand ((vl-datatype-count x))))
  :rule-classes :linear)

(local (defthm vl-dimensionlist-count-when-consp
         (implies (consp x)
                  (< 1 (vl-dimensionlist-count x)))
         :hints (("goal" :expand ((vl-dimensionlist-count x))))
         :rule-classes :linear))

(defthm vl-datatype-count-of-vl-datatype-update-udims-strong
  (implies (consp (vl-datatype->udims x))
           (< (vl-datatype-count (vl-datatype-update-udims nil x)) (vl-datatype-count x)))
  :hints(("Goal" :in-theory (enable vl-datatype-count
                                    vl-datatype-update-udims
                                    vl-datatype-update-dims)
          :expand ((vl-datatype-count x))))
  :rule-classes :linear)

(defthm vl-datatype-count-of-vl-datatype-update-pdims-strong
  (implies (consp (vl-datatype->pdims x))
           (< (vl-datatype-count (vl-datatype-update-pdims nil x)) (vl-datatype-count x)))
  :hints(("Goal" :in-theory (enable vl-datatype-count
                                    vl-datatype-update-pdims
                                    vl-datatype-update-dims)
          :expand ((vl-datatype-count x))))
  :rule-classes :linear)

(defthm vl-datatype-resolved-p-of-vl-datatype-update-udims
  (implies (vl-datatype-resolved-p x)
           (vl-datatype-resolved-p (vl-datatype-update-udims nil x)))
  :hints(("Goal" :in-theory (enable vl-datatype-resolved-p
                                    vl-datatype-update-udims
                                    vl-datatype-update-dims))))

(defthm vl-datatype-resolved-p-of-vl-datatype-update-pdims
  (implies (vl-datatype-resolved-p x)
           (vl-datatype-resolved-p (vl-datatype-update-pdims nil x)))
  :hints(("Goal" :in-theory (enable vl-datatype-resolved-p
                                    vl-datatype-update-pdims
                                    vl-datatype-update-dims))))

(defthm vl-datatype-sizable-of-vl-datatype-update-udims
  (implies (vl-datatype-sizable x)
           (vl-datatype-sizable (vl-datatype-update-udims nil x)))
  :hints(("Goal" :in-theory (e/d (vl-datatype-sizable
                                  vl-datatype-size
                                  vl-datatype-update-udims
                                  vl-datatype-update-dims)
                                 (all-equalp member append)))))

(defthm vl-datatype-sizable-of-vl-datatype-update-pdims
  (implies (vl-datatype-sizable x)
           (vl-datatype-sizable (vl-datatype-update-pdims nil x)))
  :hints(("Goal" :in-theory (e/d (vl-datatype-sizable
                                  vl-datatype-size
                                  vl-datatype-update-pdims
                                  vl-datatype-update-dims)
                                 (all-equalp member append)))))

(defthm vl-datatype->udims-of-vl-datatype-update-pdims
  (equal (vl-datatype->udims (vl-datatype-update-pdims pdims x))
         (vl-datatype->udims x)))

(defthm vl-datatype->udims-of-vl-datatype-update-udims
  (equal (vl-datatype->udims (vl-datatype-update-udims udims x))
         (vl-dimensionlist-fix udims)))

(defthm vl-datatype->pdims-of-vl-datatype-update-udims
  (equal (vl-datatype->pdims (vl-datatype-update-udims udims x))
         (vl-datatype->pdims x)))

(defthm vl-datatype->pdims-of-vl-datatype-update-pdims
  (equal (vl-datatype->pdims (vl-datatype-update-pdims pdims x))
         (vl-dimensionlist-fix pdims)))

(local (defthm vl-coretype-integer-arithclass-when-sized
         (implies (and (vl-datatype-sizable x)
                       (vl-datatype-case x :vl-coretype)
                       (not (consp (vl-datatype->udims x))))
                  (vl-integer-arithclass-p (mv-nth 1 (vl-datatype-arithclass x))))
         :hints(("Goal" :in-theory (enable vl-datatype-sizable
                                           vl-datatype-size
                                           vl-coretype-arithclass
                                           vl-coretypename->info
                                           VL-COREDATATYPE-INFOLIST-FIND-TYPE)
                 :expand ((vl-datatype-arithclass x))
                 :do-not-induct t))))

(define vl-literal-expr-warn-about-unpacked-union ((type vl-datatype-p))
  :returns (warnings vl-warninglist-p)
  (list (make-vl-warning :type :vl-unpacked-union-literal
                         :msg "Trying to make a literal expression of unpacked union type ~a0 -- please investigate."
                         :args (list (vl-datatype-fix type)))))
                         

(define vl-structmemberlist-find-max-size ((x vl-structmemberlist-p))
  :guard (and (consp x)
              (vl-structmemberlist-resolved-p x)
              (vl-structmemberlist-sizable x))
  :returns (max-size-structmem vl-structmember-p)
  :verify-guards nil
  (if (atom (cdr x))
      (vl-structmember-fix (car x))
    (b* ((rest-max (vl-structmemberlist-find-max-size (cdr x)))
         ((mv ?err rest-max-size) (vl-datatype-size (vl-structmember->type rest-max)))
         ((mv ?err curr-max-size) (vl-datatype-size (vl-structmember->type (car x)))))
      (if (< curr-max-size rest-max-size)
          rest-max
        (vl-structmember-fix (car x)))))
  ///
  (defret vl-datatype-resolved-p-of-vl-structmemberlist-find-max-size
    (implies (vl-structmemberlist-resolved-p x)
             (vl-datatype-resolved-p (vl-structmember->type max-size-structmem)))
    :hints(("Goal" :in-theory (enable vl-structmemberlist-resolved-p))))

  (defret vl-datatype-sizable-of-vl-structmemberlist-find-max-size
    (implies (and (vl-structmemberlist-sizable x)
                  (consp x))
             (vl-datatype-sizable (vl-structmember->type max-size-structmem)))
    :hints(("Goal" :in-theory (enable vl-structmemberlist-sizable-implies
                                      vl-datatype-sizable-implies))))

  (defret vl-datatype-count-of-vl-structmemberlist-find-max-size
    (implies (consp x)
             (< (vl-datatype-count (vl-structmember->type max-size-structmem))
                (vl-structmemberlist-count x)))
    :rule-classes :linear)

  (verify-guards vl-structmemberlist-find-max-size
    :hints(("Goal" :in-theory (e/d (vl-datatype-sizable-implies)
                                   (vl-datatype-sizable-of-vl-structmemberlist-find-max-size
                                    vl-structmemberlist-sizable-implies))
            :use ((:instance vl-datatype-sizable-of-vl-structmemberlist-find-max-size
                   (x (cdr x)))
                  vl-structmemberlist-sizable-implies)))))

(local (defthm vl-dimension-kind-when-total-size
         (implies (and (vl-dimensionlist-total-size x)
                       (consp x))
                  (equal (vl-dimension-kind (car x)) :range))
         :hints(("Goal" :expand ((vl-dimensionlist-total-size x)
                                 (vl-dimension-size (car x)))))))

(local (defthm vl-dimension-range-resolved-when-resolved
         (implies (and (vl-dimensionlist-resolved-p x)
                       (consp x)
                       (equal (vl-dimension-kind (car x)) :range))
                  (and (vl-expr-resolved-p (vl-range->msb (vl-dimension->range (car x))))
                       (vl-expr-resolved-p (vl-range->lsb (vl-dimension->range (car x))))))
         :hints(("Goal" :expand ((vl-dimensionlist-resolved-p x)
                                 (vl-dimension-size (car x)))))))

(local (defthm vl-dimensionlist-size-of-cdr
         (implies (and (vl-dimensionlist-total-size x)
                       (consp x))
                  (posp (vl-dimensionlist-total-size (cdr x))))
         :hints(("Goal" :expand ((vl-dimensionlist-total-size x))))
         :rule-classes :type-prescription))

(defines vl-literal-expr-from-4vec
  :prepwork ((local (in-theory (e/d (vl-datatype-sizable-implies)
                                    (vl-datatype-update-udims
                                     vl-datatype-update-pdims)))))
  (define vl-literal-expr-from-4vec ((type vl-datatype-p)
                                     (x sv::4vec-p))
    :guard (and (vl-datatype-resolved-p type)
                (vl-datatype-sizable type))
    :well-founded-relation acl2::nat-list-<
    :measure (list (vl-datatype-count type) 10 0 0)
    :returns (mv (warnings vl-warninglist-p)
                 (const-expr vl-expr-p)
                 (rest sv::4vec-p))
    :verify-guards nil
    (b* ((udims    (vl-datatype->udims type))
         (new-type (vl-datatype-update-udims nil type)))
      (vl-literal-expr-from-4vec-dims udims new-type x)))

  (define vl-literal-expr-from-4vec-dims ((dims vl-dimensionlist-p)
                                          (type vl-datatype-p)
                                          (x sv::4vec-p))
    :guard (and (vl-dimensionlist-resolved-p dims)
                (posp (vl-dimensionlist-total-size dims))
                (not (consp (vl-datatype->udims type)))
                (vl-datatype-resolved-p type)
                (vl-datatype-sizable type))
    :measure (list (vl-datatype-count type) 9 (len dims) 0)
    :returns (mv (warnings vl-warninglist-p)
                 (const-expr vl-expr-p)
                 (rest sv::4vec-p))
    (b* (((when (atom dims))
          (vl-literal-expr-from-4vec-no-dims type x))
         ((vl-range range) (vl-dimension->range (car dims)))
         ((mv warnings exprs rest)
          (vl-literal-expr-from-4vec-dim (vl-resolved->val range.msb)
                                         (vl-resolved->val range.lsb)
                                         (cdr dims) type x)))
      (mv warnings
          (make-vl-pattern :pat (vl-assignpat-positional exprs))
          rest)))

  (define vl-literal-expr-from-4vec-dim ((range-msb integerp)
                                         (range-lsb integerp)
                                         (dims vl-dimensionlist-p)
                                         (type vl-datatype-p)
                                         (x sv::4vec-p))
    :guard (and (vl-dimensionlist-resolved-p dims)
                (posp (vl-dimensionlist-total-size dims))
                (not (consp (vl-datatype->udims type)))
                (vl-datatype-resolved-p type)
                (vl-datatype-sizable type))
    :measure (list (vl-datatype-count type) 9 (len dims)
                   (+ 1 (abs (- (ifix range-msb) (ifix range-lsb)))))
    :returns (mv (warnings vl-warninglist-p)
                 (exprs vl-exprlist-p)
                 (rest sv::4vec-p))
    (b* ((range-msb (lifix range-msb))
         (range-lsb (lifix range-lsb))
         ((when (eql range-msb range-lsb))
          ;; just get the expr for the most significant chunk, which now is the
          ;; LSB of the original range
          (b* (((mv warnings expr rest) (vl-literal-expr-from-4vec-dims dims type x)))
            (mv warnings (list expr) rest)))
         (new-range-msb (+ (if (< range-lsb range-msb) -1 1) range-msb))
         ((mv warnings low-exprs rest)
          (vl-literal-expr-from-4vec-dim new-range-msb range-lsb dims type x))
         ((wmv warnings high-expr rest)
          (vl-literal-expr-from-4vec-dims dims type rest)))
      (mv warnings (cons high-expr low-exprs) rest)))

  (define vl-literal-expr-from-4vec-no-dims ((type vl-datatype-p)
                                             (x sv::4vec-p))
    :guard (and (not (consp (vl-datatype->udims type)))
                (vl-datatype-resolved-p type)
                (vl-datatype-sizable type))
    :returns (mv (warnings vl-warninglist-p)
                 (const-expr vl-expr-p)
                 (rest sv::4vec-p))
    :measure (list (vl-datatype-count type) 8 0 0)
    (b* (((mv ?caveat class) (vl-datatype-arithclass type))
         ((when (vl-integer-arithclass-p class))
          (b* (((mv expr rest) (vl-literal-expr-from-4vec/vector-type type x)))
            (mv nil expr rest)))
         (pdims (vl-datatype->pdims type))
         ((when (consp pdims))
          ;; this shouldn't happen because we shouldn't have packed dimensions
          ;; on something that isn't a vector type.  But nothing enforces this
          ;; so we'll just treat these as unpacked dims.
          (vl-literal-expr-from-4vec-dims pdims (vl-datatype-update-pdims nil type) x)))
      (vl-datatype-case type
        :vl-struct (b* (((mv warnings exprs rest)
                         (vl-literal-expr-from-4vec-structmemberlist type.members x)))
                     (mv warnings (make-vl-pattern :pat (vl-assignpat-positional exprs)) rest))
        :vl-union
        ;; Weird case.  Find the max-size structmember and use that type, I guess.
        (b* ((warnings (vl-literal-expr-warn-about-unpacked-union type))
             ((when (atom type.members))
              ;; A union of no structmembers has size 0; just pretend it's packed
              (mv warnings (vl-literal-expr-for-zero-size type.signedp) (sv::4vec-fix x)))
             (new-type (vl-structmember->type (vl-structmemberlist-find-max-size type.members))))
          (vl-literal-expr-from-4vec new-type x))

        :vl-enum
        ;; weird for an enum to not be integer but seems straightforward
        (vl-literal-expr-from-4vec type.basetype x)

        :vl-usertype
        (b* (((unless (mbt (and type.res t)))
              (mv (impossible)
                  (vl-literal-expr-for-zero-size nil)
                  (sv::4vec-fix x))))
          (vl-literal-expr-from-4vec type.res x))

        :vl-coretype
        ;;  impossible by vl-coretype-integer-arithclass-when-sized
        (mv (impossible)
            (vl-literal-expr-for-zero-size nil)
            (sv::4vec-fix x)))))

  (define vl-literal-expr-from-4vec-structmemberlist ((membs vl-structmemberlist-p)
                                                      (x sv::4vec-p))
    :guard (and (vl-structmemberlist-resolved-p membs)
                (vl-structmemberlist-sizable membs))
    :returns (mv (warnings vl-warninglist-p)
                 (exprs vl-exprlist-p)
                 (rest sv::4vec-p))
    :measure (list (vl-structmemberlist-count membs) 8 0 0)
    (b* (((when (atom membs))
          (mv nil nil (sv::4vec-fix x)))
         ((mv warnings rest-exprs rest-x) (vl-literal-expr-from-4vec-structmemberlist (cdr membs) x))
         ((wmv warnings first-expr rest) (vl-literal-expr-from-4vec (vl-structmember->type (car membs)) rest-x)))
      (mv warnings (cons first-expr rest-exprs) rest)))
  ///
  (verify-guards vl-literal-expr-from-4vec))
