; Copyright (C) 2022 Intel Corporation
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
; Original author: Mertcan Temel <mert.temel@intel.com>

(in-package "RP")

(include-book "pp-flatten-meta-fncs")

(include-book "pp-flatten-with-binds-meta")

(include-book "sum-merge-fncs")

(include-book "centaur/sv/svex/4vec" :dir :system)

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

(local
 (fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arith-5
  :disabled t))

(local
 (include-book "pp-flatten-meta-correct"))

(local
 (include-book "sum-merge-fncs-correct"))

(local
 (include-book "lemmas"))
(local
 (include-book "lemmas-2"))

(local
   (defthm is-equals-of-others
     (implies (not (equal (car term) 'equals))
              (not (is-equals term )))
     :hints (("Goal"
              :in-theory (e/d (is-equals) ())))))

(define 4vec-branch-drop-r-case-pattern-check ((term rp-termp))
  :Returns (pass booleanp)
  :measure (cons-count term)
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  (b* ((term (ex-from-rp term)))
    (case-match term
      (('sv::4vec-?* ('-- x) & else)
       (and (b* ((x (ex-from-rp x)))
              (or (binary-fnc-p x)
                  (equal x ''0)
                  (equal x ''1)
                  (logbit-p x)))
            (4vec-branch-drop-r-case-pattern-check else)))
      (('quote x)
       (and (sv::4vec-p x)
            (not (integerp x)))))))

(define 4vec-branch-drop-r-case-aux ((term rp-termp)
                                     (met-cases (and (pp-term-p met-cases)
                                                     (rp-termp met-cases))))
  :verify-guards nil
  :measure (cons-count term)
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  :returns (mv (new-term rp-termp :hyp (rp-termp term))
               (dont-rw)
               (valid booleanp))
  (b* ((term (ex-from-rp term)))
    (case-match term
      (('sv::4vec-?* ('-- x) then else)
       (b* (((unless (and (pp-term-p x)))
             (mv ''nil nil nil))
            (met-cases `(binary-or ,x ,met-cases))
            ((mv rest-new-term rest-dont-rw valid)
             (4vec-branch-drop-r-case-aux else met-cases))
            ((Unless valid) (mv ''nil nil nil)))
         (mv `(sv::4vec-?* (-- ,x) ,then ,rest-new-term)
             `(nil (nil t) t ,rest-dont-rw)
             t)))
      (('quote x)
       (b* (((unless (and (sv::4vec-p x)
                          (not (integerp x))))
             (mv ''nil nil nil))
            (met-cases (pp-flatten-with-binds
                        met-cases )))
         (if (equal met-cases (list ''1))
             (mv ''0 t t)
           (mv ''nil nil nil))))
           
      (&
       (mv ''nil nil nil))))
  ///
  (verify-guards 4vec-branch-drop-r-case-aux
    :hints (("Goal"
             :expand ((:free (x y) (pp-term-p `(binary-or ,x ,y))))
             :in-theory (e/d (is-rp
                              binary-or-p)
                             ())))))

(define 4vec-branch-drop-r-case ((term rp-termp))
  :returns (mv (res-term rp-termp :hyp (rp-termp term))
               (dont-rw))
  (case-match term
    (('sv::4vec-?* & & &)
     (b* (((unless (4vec-branch-drop-r-case-pattern-check term))
           (mv term nil))
          ((mv new-term dont-rw valid)
           (4vec-branch-drop-r-case-aux term ''0)))
       (if valid
           (mv new-term dont-rw)
         (mv term nil))))
    (& (mv term nil))))


(local
 (in-theory (disable pp-term-p)))


(encapsulate
  nil

  (local
   (in-theory (disable
               +-IS-SUM
               REWRITING-POSITIVE-LTE-GTE-GT-LT
              ;; +-is-SUM
               mod2-is-m2
               floor2-if-f2
               C-SPEC-IS-F2
               c-is-f2
               s-is-m2
               s-spec-is-m2
               ;;SVL::4VEC-ZERO-EXT-IS-4VEC-CONCAT
               c-spec-is-f2
               s-c-spec-is-list-m2-f2
               c-s-spec-is-list-m2-f2
               s-of-c-trig-def
               )))

  (with-output
    :off :all
    :gag-mode nil

    (def-formula-checks
      4vec-branch-formula-checks
      (binary-append
       ifix
       
       acl2::logcar$inline
       acl2::logcdr$inline
       acl2::logbit$inline
       unpack-booth
       --
       times
       sum-list
       binary-and
       and-list
       sort-sum
       rp::c-s-spec
       rp::s-c-spec
       rp::c-spec
       rp::s-spec
       
       ;; svl::bits
       ;; svl::4vec-bitand
       ;; svl::4vec-bitor
        svl::4vec-?
        svl::4vec-?*
       ;; sv::4vec-bitxor
       ;; svl::4vec-bitnot
       ;; svl::4vec-bitnot$
       adder-b+
       s-of-c-trig
       binary-?
       binary-xor
       binary-or
       binary-not
       bit-fix
       s-c-res
       c
       m2
       f2
       times2
       s
       pp
       binary-sum
       ;;sv::3vec-fix
       bit-concat
       ;;sv::4vec-fix
       svl::Bits
       and-times-list

       int-vector-adder-lst-w/carry
       ))))


(local
 (create-regular-eval-lemma sv::4vec-?* 3 4vec-branch-formula-checks))

(local
 (create-regular-eval-lemma -- 1 4vec-branch-formula-checks))

(local
 (create-regular-eval-lemma sv::4vec-fix$inline 1 4vec-branch-formula-checks))


(local
 (defthm 4vec-branch-formula-checks-implies-mult-formula-checks
   (implies (4vec-branch-formula-checks state)
            (mult-formula-checks state))
   :hints (("Goal"
            :in-theory (e/d (4vec-branch-formula-checks
                             mult-formula-checks
                             ) ())))))

(local
 (defret pp-flatten-correct-with-sum-list-eval
  (implies (and (mult-formula-checks state)
                (pp-term-p term)
                (booleanp sign)
                (rp-termp term)
                (valid-sc term a)
                (or (= coef 1)
                    (= coef -1))
                (rp-evl-meta-extract-global-facts))
           (equal (sum-list-eval pp-lst a)
                  (times coef (rp-evlt term a))))
  :fn pp-flatten
  :hints (("Goal"
           :use ((:instance pp-flatten-correct))
           :in-theory (e/d () (pp-flatten-correct))))))

(local
 (defret pp-flatten-with-binds-correct-with-sum-list-eval
  (implies (and (mult-formula-checks state)
                (pp-term-p term)
                (rp-termp term)
                (booleanp signed)
                (valid-sc term a)
                (or (= coef 1)
                    (= coef -1))
                (rp-evl-meta-extract-global-facts))
           (equal (sum-list-eval pp-lst a)
                  (times coef (rp-evlt term a))))
  :fn pp-flatten-with-binds
  :hints (("Goal"
           :use ((:instance pp-flatten-with-binds-correct))
           :in-theory (e/d () (pp-flatten-with-binds-correct))))))

(local
 (defthm 4VEC-?*-cond-lemma1
   (implies (equal (ifix test) 1)
            (equal (sv::4vec-?* (-- test) then else)
                   (sv::4vec-fix then)))
   :hints (("Goal"
            :in-theory (e/d (sv::4vec-?*
                             SV::3VEC-?*
                             --)
                            ())))))

(local
 (defthm 4VEC-?*-cond-lemma2
   (implies t
            (equal (sv::4vec-?* -1 then else)
                   (sv::4vec-fix then)))
   :hints (("Goal"
            :in-theory (e/d (sv::4vec-?*
                             SV::3VEC-?*
                             --)
                            ())))))

(local
 (defthm or$-of-0
   (equal (or$ x 0)
          (bit-fix x))
   :hints (("Goal"
            :in-theory (e/d (or$ bit-fix) ())))))

(local
 (defthm when-not-0-and-pp-termp
   (implies (and (valid-sc term a)
                 (pp-term-p term)
                 (rp-evl-meta-extract-global-facts :state state)
                 (4vec-branch-formula-checks state)
                 (not (equal (rp-evlt term a) 0)))
            (equal (rp-evlt term a) 1))
   :hints (("Goal"
            :use ((:instance pp-term-p-is-bitp
                             (strict nil)))
            :in-theory (e/d () ())))))

(local
 (defthmd when-pp-flatten-is-1
   (implies (and (valid-sc term a)
                 (pp-term-p term)
                 (rp-termp term)
                 (rp-evl-meta-extract-global-facts :state state)
                 (4vec-branch-formula-checks state)
                 (EQUAL (pp-flatten term :DISABLED nil)
                        (list ''1)))
            (equal (rp-evlt term a)
                   1))
   :hints (("Goal"
            :use ((:instance pp-flatten-correct
                             (coef 1)
                             (disabled nil)
                             (term-size-limit nil)))
            :in-theory (e/d (ifix)
                            (pp-flatten-correct))))))

(local
 (defthmd when-pp-flatten-with-binds-is-1
   (implies (and (valid-sc term a)
                 (pp-term-p term)
                 (rp-termp term)
                 (rp-evl-meta-extract-global-facts :state state)
                 (4vec-branch-formula-checks state)
                 (EQUAL (PP-FLATTEN-WITH-BINDS term :DISABLED nil)
                        (list ''1)))
            (equal (rp-evlt term a)
                   1))
   :hints (("Goal"
            :use ((:instance pp-flatten-with-binds-correct
                             (coef 1)
                             (disabled nil)))
            :in-theory (e/d (ifix)
                            (pp-flatten-with-binds-correct))))))


(local
 (defthm rp-evlt-of-quoted-with-ex-from-rp
   (implies (and (quotep (ex-from-rp x))
                 (consp (cdr (ex-from-rp x))))
            (equal (rp-evlt x a)
                   (unquote (ex-from-rp x))))
   :hints (("Goal"
            :expand ((rp-trans (ex-from-rp x)))
            :in-theory (e/d (rp-evlt-of-ex-from-rp-reverse
                             )
                            (include-fnc
                             EVL-OF-EXTRACT-FROM-RP
                             ex-from-rp
                             rp-evlt-of-ex-from-rp))))))

(defret 4vec-branch-drop-r-case-aux-correct
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (4vec-branch-formula-checks state)
                (mult-formula-checks state)
                valid
                (valid-sc term a)
                (rp-termp term)
                (valid-sc met-cases a)
                (bitp (rp-evlt met-cases a))
                (equal (rp-evlt met-cases a) 0)
                (rp-termp met-cases)
                (pp-term-p met-cases))
           (equal (rp-evlt new-term a)
                  (rp-evlt term a)))
  :fn 4vec-branch-drop-r-case-aux
  :hints (("goal"
           :expand ((:free (x y) (pp-term-p `(binary-or ,x ,y)))
                    (:free (x y) (valid-sc `(binary-or ,x ,y) a)))
           :in-theory (e/d
                       (4vec-branch-drop-r-case-aux
                        regular-rp-evl-of_4vec-?*_when_4vec-branch-formula-checks_with-ex-from-rp
                        regular-rp-evl-of_4vec-?*_when_4vec-branch-formula-checks
                        regular-rp-evl-of_--_when_4vec-branch-formula-checks
                        regular-rp-evl-of_--_when_4vec-branch-formula-checks_with-ex-from-rp
                        is-rp
                        binary-or-p)
                       (4vec-branch-formula-checks-implies-mult-formula-checks
                        pp-term-p
                        valid-sc)))
          (and stable-under-simplificationp
               '(:use ((:instance when-pp-flatten-is-1
                                  (term met-cases))
                       (:instance when-pp-flatten-with-binds-is-1
                                  (term met-cases)))))))


(defret 4vec-branch-drop-r-case-aux-valid-sc
  (implies (and (rp-evl-meta-extract-global-facts :state state)
                (4vec-branch-formula-checks state)
                (mult-formula-checks state)
                valid
                (valid-sc term a))
           (valid-sc new-term a))
  :fn 4vec-branch-drop-r-case-aux
  :hints (("goal"
           :in-theory (e/d
                       (4vec-branch-drop-r-case-aux
                        is-rp)
                       (4vec-branch-formula-checks-implies-mult-formula-checks)))))


(rp::add-meta-rule
 :meta-fnc 4vec-branch-drop-r-case
 :trig-fnc sv::4vec-?*
 :valid-syntaxp t
 :formula-checks 4vec-branch-formula-checks
 :returns (mv term dont-rw)
 :hints (("Goal"
          :in-theory (e/d (4vec-branch-drop-r-case) ()))))
