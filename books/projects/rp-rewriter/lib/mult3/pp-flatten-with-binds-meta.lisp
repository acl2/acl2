; SV - Symbolic Vector Hardware Analysis Framework
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

(local
 (Include-Book "std/basic/intern-in-package-of-symbol" :dir :system))

(local
 (include-book "pp-flatten-meta-correct"))

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/apply-bindings-lemmas" :dir :system))

(local
 (include-book "lemmas"))

(local
 (include-book "sum-merge-fncs-correct"))

(local
 (in-theory (disable TO-LIST*-SUM-EVAL
                     +-IS-SUM)))

(local
 (fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arith-5
  :disabled t))

(local
 (set-induction-depth-limit 2))

(progn

  (define make-pp-entry (tmp-var orig-term)
    :inline t
    (cons tmp-var orig-term))

  (define pp-entry->tmp-var (entry)
    :guard (consp entry)
    :inline t
    (car entry)
    ///
    (defthm pp-entry->tmp-var-of-make-pp-entry
      (equal (pp-entry->tmp-var (make-pp-entry tmp-var orig-term))
             tmp-var)
      :hints (("Goal"
               :in-theory (e/d (MAKE-PP-ENTRY) ())))))

  (define pp-entry->orig-term (entry)
    :guard (consp entry)
    :inline t
    (cdr entry)
    ///
    (defthm pp-entry->orig-term-of-make-pp-entry
      (equal (pp-entry->orig-term (make-pp-entry tmp-var orig-term))
             orig-term)
      :hints (("Goal"
               :in-theory (e/d (MAKE-PP-ENTRY) ())))))

  (define pp-binds-p (x)
    :enabled t
    :guard-hints (("Goal"
                   :do-not-induct t
                   :in-theory (e/d () ())))
    (if (atom x)
        (equal x nil)
      (b* (((Unless (consp (car x))) nil)
           (orig-term (pp-entry->orig-term (car x)))
           (tmp-var (pp-entry->tmp-var (car x))))
        (and
         (pp-term-p orig-term)
         (rp-termp orig-term)
         (symbolp tmp-var)
         (b* ((replacement (symbol-name tmp-var)))
           (and (> (length replacement) 4)
                (equal (subseq replacement 0 4) "VAR-")
                (equal (subseq replacement 4 nil)
                       (str::nat-to-dec-string (len (cdr x))))))
         (pp-binds-p (cdr x))))))

  (define rp-assoc-w/-tmp-var (tmp-var (alist pp-binds-p))
    :inline t
    :returns entry
    (assoc-equal tmp-var alist)
    ///
    (defret nonnil-<fn>-implies-consp
      (implies (and entry (alistp alist)) (consp entry))
      :rule-classes :forward-chaining)
    (defret nonnil-<fn>-implies-consp-2
      (implies (and entry (pp-binds-p alist)) (consp entry))
      :rule-classes :forward-chaining)
    (defret consp-<fn>-implies-nonil
      (implies (consp entry) entry)
      :rule-classes :forward-chaining))

  (define rp-assoc-w/-orig-term (orig-term
                                 (alist pp-binds-p))
    (if (or (atom alist)
            (atom (car alist)))
        nil
      (if (rp-equal-cnt orig-term
                        (pp-entry->orig-term (car alist))
                        2)
          (car alist)
        (rp-assoc-w/-orig-term orig-term (cdr alist)))))

  (local
   (defthm rp/pp-term-p-of-rp-assoc-w/-orig-term
     (implies (and (pp-binds-p alist)
                   (rp-assoc-w/-orig-term x alist))
              (and (pp-term-p (pp-entry->orig-term (rp-assoc-w/-orig-term x alist)))
                   (rp-termp (pp-entry->orig-term (rp-assoc-w/-orig-term x alist)))
                   (rp-termp (pp-entry->tmp-var (rp-assoc-w/-orig-term x alist)))
                   (symbolp (pp-entry->tmp-var (rp-assoc-w/-orig-term x
                                                                      alist)))
                   (symbolp (car (rp-assoc-w/-orig-term x
                                                        alist)))
                   (pp-entry->tmp-var (rp-assoc-w/-orig-term x alist))))
     :hints (("goal"
              :in-theory (e/d (pp-entry->tmp-var
                               rp-assoc-w/-orig-term
                               pp-binds-p)
                              ())))))

  (local
   (defthm cdr-of-RP-ASSOC-W/-ORIG-TERM
     (implies (RP-ASSOC-W/-ORIG-TERM term alist)
              (and (rp-EQUAL (cdr (RP-ASSOC-W/-ORIG-TERM term alist))
                             term)))
     :hints (("Goal"
              :in-theory (e/d (RP-ASSOC-W/-ORIG-TERM
                               PP-ENTRY->ORIG-TERM)
                              ())))))

  (local
   (defthm rp-termp/symbolp-of-rp-assoc-w/-tmp-var
     (implies (and (pp-binds-p alist)
                   (rp-assoc-w/-tmp-var x alist))
              (and (pp-term-p (pp-entry->orig-term (rp-assoc-w/-tmp-var x alist)))
                   (rp-termp (pp-entry->orig-term (rp-assoc-w/-tmp-var x alist)))
                   (rp-termp (pp-entry->tmp-var (rp-assoc-w/-tmp-var x alist)))
                   (symbolp (pp-entry->tmp-var (rp-assoc-w/-tmp-var x alist)))
                   (pp-entry->tmp-var (rp-assoc-w/-tmp-var x alist))))
     :hints (("goal"
              :in-theory (e/d (rp-assoc-w/-tmp-var
                               pp-binds-p)
                              ()))))))

(progn ;; pp-bind

  (local
   (in-theory (disable DEFAULT-CDR
                       include-fnc
                       DEFAULT-CaR)))

  (define pp-term-bind ((term (and (rp-termp term)
                                   (pp-term-p term)))
                        (pp-binds pp-binds-p)
                        (index natp))
    :guard (equal (len pp-binds) index)
    :measure (cons-count term)
    :returns (mv (res)
                 (res-pp-binds)
                 (res-index)
                 (valid))
    :hints (("Goal"
             :in-theory (e/d (or*
                              measure-lemmas)
                             ())))
    :verify-guards nil
    (b* ((orig term)
         (term (ex-from-rp$ term)))
      (cond
       ((binary-?-p term)
        (b* (((mv test pp-binds index valid-test)
              (pp-term-bind (cadr term) pp-binds index))
             ((mv then pp-binds index valid-then)
              (pp-term-bind (caddr term) pp-binds index))
             ((mv else pp-binds index valid-else)
              (pp-term-bind (cadddr term) pp-binds index)))
          (mv (hons-list (car term) test then else)
              pp-binds index
              (and* valid-test valid-then valid-else))))

       ((or (binary-xor-p term)
            (binary-or-p term)
            (binary-and-p term))
        (b* (((mv a pp-binds index valid-a)
              (pp-term-bind (cadr term) pp-binds index))
             ((mv b pp-binds index valid-b)
              (pp-term-bind (caddr term) pp-binds index)))
          (mv (hons-list (car term) a b)
              pp-binds index
              (and* valid-a valid-b))))

       ((binary-not-p term)
        (b* (((mv a pp-binds index valid-a)
              (pp-term-bind (cadr term) pp-binds index)))
          (mv (hons-list (car term) a)
              pp-binds index
              valid-a)))

       ((or (equal term ''1)
            (equal term ''0))
        (mv (hons-copy term) pp-binds index t))

       ((or (bit-of-p term)
            (has-bitp-rp orig))
        (b* ((entry (rp-assoc-w/-orig-term term pp-binds))
             ((when entry)
              (mv (hons-list 'bit-fix (pp-entry->tmp-var entry))
                  pp-binds index t))
             (var (intern$ (str::cat "VAR-"
                                     (str::nat-to-dec-string index))
                           "RP"))
             (var-with-rp (hons-list 'bit-fix var)))
          (mv var-with-rp (cons (make-pp-entry var orig) pp-binds) (1+ index) t)))
       (t (mv term pp-binds index nil)))))

  (local
   (defthm pp-term-p-of-ex-from-rp
     (implies (and (pp-term-p term)
                   (not (has-bitp-rp term)))
              (pp-term-p (ex-from-rp term)))))

  (local
   (defthm pp-term-p-of-ex-from-rp-2
     (implies (and (pp-term-p term)
                   (binary-fnc-p (ex-from-rp term)))
              (pp-term-p (ex-from-rp term)))
     :hints (("goal"
              :in-theory (e/d (binary-fnc-p) ())))))

  (local
   (in-theory (e/d (pp-term-list-p)
                   (pp-term-p))))

  (local
   (defthm pp-term-p-and-binary-fnc-p-lemma
     (implies (and (or (binary-not-p x)
                       (or* (binary-xor-p x)
                            (binary-or-p x)
                            (binary-and-p x))
                       (binary-?-p x))
                   (pp-term-list-p lst)
                   (equal (len lst) (len (cdr x))))
              (pp-term-p `(,(car x) . ,lst)))
     :hints (("goal"
              :expand ((pp-term-list-p (cddr lst) :strict nil)
                       (pp-term-list-p (cdr lst) :strict nil)
                       (pp-term-list-p lst :strict nil)
                       (pp-term-list-p (cdddr lst) :strict nil)
                       (:free (x y)
                              (pp-term-p (cons x y)
                                         :strict nil)))
              :do-not-induct t
              :in-theory (e/d (len
                               or*
                               has-bitp-rp
                               is-rp
                               ex-from-rp
                               bit-of-p
                               pp-p
                               binary-or-p
                               binary-and-p
                               binary-xor-p
                               binary-?-p
                               binary-not-p
                               binary-fnc-p
                               pp-term-p
                               pp-term-list-p)
                              ())))))

  (local
   (defthm dummy-len-equiv-implies-integerp-lemma
     (implies (equal (len x) num)
              (integerp num))
     :rule-classes :forward-chaining))

  (local
   (defthm pp-term-p-of-bit-of-lemma
     (pp-term-p (list 'bit-of x y)
                :strict nil)
     :hints (("goal"
              :expand (pp-term-p (list 'bit-of x y)
                                 :strict nil)
              :in-theory (e/d (binary-xor-p
                               binary-or-p
                               binary-and-p
                               pp-term-p pp-p
                               is-rp
                               has-bitp-rp
                               bit-of-p
                               ex-from-rp
                               binary-?-p)
                              ())))))

  (local
   (defthm ex-from-rp-of-binary-fnc
     (implies (binary-fnc-p term)
              (equal (ex-from-rp term)
                     term))
     :hints (("goal"
              :in-theory (e/d (binary-fnc-p
                               ex-from-rp is-rp)
                              ())))))

  (local
   (defthm ex-from-rp-of-binary-fnc-explicit
     (and  (equal (ex-from-rp `(binary-not . ,lst))
                  `(binary-not . ,lst))
           (equal (ex-from-rp `(bit-fix . ,lst))
                  `(bit-fix . ,lst))
           (equal (ex-from-rp `(binary-? . ,lst))
                  `(binary-? . ,lst))
           (equal (ex-from-rp `(binary-and . ,lst))
                  `(binary-and . ,lst))
           (equal (ex-from-rp `(binary-xor . ,lst))
                  `(binary-xor . ,lst))
           (equal (ex-from-rp `(binary-or . ,lst))
                  `(binary-or . ,lst)))
     :hints (("goal"
              :in-theory (e/d (ex-from-rp is-rp)
                              ())))))

  (local
   (defthm pp-term-p-of-binary-fncs-p
     (and (equal (pp-term-p `(binary-not ,x))
                 (pp-term-p x))
          (equal (pp-term-p `(bit-fix ,x))
                 t)
          (implies (and (pp-term-p x)
                        (pp-term-p y))
                   (pp-term-p `(binary-or ,x ,y)))
          (implies (and (pp-term-p x)
                        (pp-term-p y))
                   (pp-term-p `(binary-and ,x ,y)))
          (implies (and (pp-term-p x)
                        (pp-term-p y))
                   (pp-term-p `(binary-xor ,x ,y)))
          (implies (and (pp-term-p x)
                        (pp-term-p y)
                        (pp-term-p z))
                   (pp-term-p `(binary-? ,x ,y ,z)))
          (implies (and (pp-term-p x)
                        (or (binary-not-p (ex-from-rp x))
                            (or* (binary-xor-p (ex-from-rp x))
                                 (binary-or-p (ex-from-rp x))
                                 (binary-and-p (ex-from-rp x)))
                            (binary-?-p (ex-from-rp x))))
                   (pp-term-p (cadr (ex-from-rp x))
                              :strict nil))
          (implies (and (pp-term-p x)
                        (or (or* (binary-xor-p (ex-from-rp x))
                                 (binary-or-p (ex-from-rp x))
                                 (binary-and-p (ex-from-rp x)))
                            (binary-?-p (ex-from-rp x))))
                   (pp-term-p (caddr (ex-from-rp x))
                              :strict nil))
          (implies (and (pp-term-p x)
                        (binary-?-p (ex-from-rp x)))
                   (pp-term-p (cadddr (ex-from-rp x))
                              :strict nil)))
     :hints (("goal"
              :do-not-induct t
              :expand ((binary-fnc-p (ex-from-rp x))
                       (:free (x y)
                              (pp-term-p (cons x y)))
                       (pp-term-p x :strict nil))
              :in-theory (e/d (;;binary-fnc-p
                               pp-term-p
                               binary-and-p
                               binary-not-p
                               binary-or-p
                               binary-xor-p
                               binary-?-p
                               is-rp ex-from-rp
                               has-bitp-rp)
                              (ex-from-rp-of-binary-fnc
                               ex-from-rp))))))

  (local
   (defthm rp-termp-of-binary-fncs
     (and (implies (and (rp-termp x)
                        (binary-fnc-p (ex-from-rp x)))
                   (rp-termp (cadr (ex-from-rp x))
                             ))
          (implies (and (rp-termp x)
                        (or (binary-xor-p (ex-from-rp x))
                            (binary-or-p (ex-from-rp x))
                            (binary-and-p (ex-from-rp x))
                            #|(or* (binary-xor-p (ex-from-rp x))
                            (binary-or-p (ex-from-rp x))
                            (binary-and-p (ex-from-rp x)))|#
                            (binary-?-p (ex-from-rp x))))
                   (rp-termp (caddr (ex-from-rp x))
                             ))
          (implies (and (rp-termp x)
                        (binary-?-p (ex-from-rp x)))
                   (rp-termp (cadddr (ex-from-rp x))
                             )))
     :hints (("goal"
              :in-theory (e/d (or*
                               binary-fnc-p) ())))))

  (defthm non-nil-intern-in-package-of-symbol
    (implies (and (stringp x)
                  (not (equal x "NIL")))
             (intern-in-package-of-symbol x 'acl2-pkg-witness))
    :hints (("goal"
             :use ((:instance acl2::equal-of-intern-in-package-of-symbols
                              (acl2::a x)
                              (acl2::b "NIL")
                              (acl2::in-pkg (pkg-witness "RP"))))
             :in-theory (e/d ()
                             (acl2::equal-of-intern-in-package-of-symbols)))))

  (defthmd implode-equivalance-with-string
    (and (implies (and (stringp string)
                       (equal chars
                              (acl2::explode string)))
                  (equal (equal (acl2::implode chars)
                                string)
                         t))
         (implies (and (stringp string)
                       (character-listp chars)
                       (not (equal chars
                                   (acl2::explode string))))
                  (equal (equal (acl2::implode chars)
                                string)
                         nil))))

  (defthm ex-from-rp-of-intern-in-package-of-symbol
    (equal (ex-from-rp (intern-in-package-of-symbol string in-pkg))
           (intern-in-package-of-symbol string in-pkg))
    :hints (("goal"
             :use ((:instance
                    symbolp-intern-in-package-of-symbol
                    (acl2::x string)
                    (acl2::y in-pkg)))
             :in-theory (e/d (ex-from-rp is-rp)
                             (symbolp-intern-in-package-of-symbol)))))

  (defthm binary-fnc-p-of-intern-in-package-of-symbol
    (and (not (binary-and-p (intern-in-package-of-symbol string in-pkg)))
         (not (binary-or-p (intern-in-package-of-symbol string in-pkg)))
         (not (binary-xor-p (intern-in-package-of-symbol string in-pkg)))
         (not (binary-?-p (intern-in-package-of-symbol string in-pkg)))
         (not (binary-not-p (intern-in-package-of-symbol string in-pkg)))
         (not (bit-of-p (intern-in-package-of-symbol string in-pkg)))
         (not (pp-p (intern-in-package-of-symbol string in-pkg)))
         (not (bit-fix-p (intern-in-package-of-symbol string in-pkg))))
    :hints (("goal"
             :use ((:instance
                    symbolp-intern-in-package-of-symbol
                    (acl2::x string)
                    (acl2::y in-pkg)))
             :in-theory (e/d (binary-and-p
                              binary-or-p
                              binary-?-p
                              binary-not-p
                              bit-of-p
                              pp-p
                              binary-xor-p)
                             ()))))

  (defthm has-bitp-rp-of-rp-bitp
    (has-bitp-rp (list 'rp ''bitp x))
    :hints (("goal"
             :in-theory (e/d (is-rp has-bitp-rp)
                             ()))))

  (defthm pp-term-p-of-rp-bitp
    (implies (or (and (not (binary-xor-p (ex-from-rp x)))
                      (not (binary-or-p (ex-from-rp x)))
                      (not (binary-and-p (ex-from-rp x)))
                      (not (binary-?-p (ex-from-rp x)))
                      (not (binary-not-p (ex-from-rp x)))
                      (not (pp-p (ex-from-rp x))))
                 (symbolp x))
             (pp-term-p (list 'rp ''bitp x)))
    :hints (("goal"
             :do-not-induct t
             :expand (pp-term-p (list 'rp ''bitp x)
                                :strict nil)
             :in-theory (e/d (pp-term-p) ()))))

  (defthm rp-term-p-of-rp-bitp
    (equal (rp-termp `(rp 'bitp ,x))
           (rp-termp x)))

  (local
   (defthm rp-termp-intern-in-package-of-symbol
     (implies (intern-in-package-of-symbol x y)
              (rp-termp (intern-in-package-of-symbol x y)))))

  (local
   (defthm rp-termp-intern-in-package-of-symbol-2
     (and (implies (character-listp rest)
                   (rp-termp
                    (intern-in-package-of-symbol
                     (acl2::implode (list* #\V rest)) 'acl2-pkg-witness))))
     :hints (("goal"
              :use ((:instance
                     implode-equivalance-with-string
                     (chars (list* #\V rest))
                     (string "NIL")))
              :in-theory (e/d () ())))))

  (local
   (defthm dummy-lemma-strings
     (implies (stringp string)
              (equal (str::fast-string-append "VAR-" string)
                     (acl2::implode (list* #\V #\A #\R #\-
                                           (explode string)))))))

  (local
   (defthm rp-termp-fo-binary-fncs-explicit
     (and (implies (and
                    (rp-termp x))
                   (rp-termp `(binary-not ,x)))
          (implies (and (or (equal fn 'binary-or)
                            (equal fn 'binary-and)
                            (equal fn 'binary-xor))
                        (rp-termp x)
                        (rp-termp y))
                   (rp-termp `(,fn ,x ,y)))
          (implies (and (rp-termp x)
                        (rp-termp y)
                        (rp-termp z))
                   (rp-termp `(binary-? ,x ,y ,z))))))

  (defret return-vals-of-<fn>
    (and (implies (and (pp-binds-p pp-binds)
                       (pp-term-p term)
                       (rp-termp term)
                       (equal (len pp-binds) index))
                  (and (pp-term-p res)
                       (rp-termp res)
                       (pp-binds-p res-pp-binds)))
         (implies (equal (len pp-binds) index)
                  (equal (len res-pp-binds) res-index))
         (implies (natp index)
                  (natp res-index))
         (booleanp valid))
    :hints (("goal"
             :in-theory (e/d (pp-term-bind
                              len)
                             ((:rewrite default-+-2)
                              (:rewrite acl2::and*-rem-first)
                              (:rewrite
                               acl2::default-intern-in-package-of-symbol)
                              (:rewrite default-+-1)
                              (:rewrite rationalp-implies-acl2-numberp)
                              (:meta binary-or**/and**-guard-meta-correct)
                              (:rewrite append-of-nil)
                              (:rewrite str::explode-when-not-stringp)
                              (:definition str::fast-string-append)
                              (:definition string-append)
                              (:definition ex-from-rp)
                              (:rewrite
                               acl2::intern-in-package-of-symbol-is-identity)
                              is-if-rp-termp
                              is-rp-pseudo-termp
                              (:type-prescription rp-termp)
                              (:rewrite rp-termp-caddr)
                              (:rewrite rp-termp-cadr)
                              (:rewrite ex-from-rp-of-binary-fnc)
                              (:rewrite rp-termp-cadddr)
                              (:rewrite pseudo-termlistp-extract-from-rp)
                              ;;(:rewrite binary-fnc-p-relieve)
                              natp
                              rp-termp
                              falist-consistent))))
    :fn pp-term-bind)

  (verify-guards pp-term-bind
    :hints (("goal"
             :do-not-induct t
             :in-theory (e/d (or*)
                             (rp-termp))))))

(defsection pp-apply-bindings

  (define can-be-removed-from-bit-fix ((term rp-termp))
    (b* ((orig term)
         (term (ex-from-rp$ term)))
      (or (binary-fnc-p term)
          (single-s-p term)
          (bit-of-p term)
          (has-bitp-rp orig))))

  (define pp-apply-bindings-and-arg-lst ((and-arg-lst rp-term-listp)
                                         (pp-binds pp-binds-p))
    :returns (mv (res true-listp) valid)
    :guard-hints (("Goal"
                   :in-theory (e/d () (pp-binds-p))))
    (if (atom and-arg-lst)
        (mv nil (equal and-arg-lst nil))
      (b* (((mv rest valid)
            (pp-apply-bindings-and-arg-lst (cdr and-arg-lst) pp-binds))
           (cur (car and-arg-lst))
           ((mv cur has-bit-fix) (if (bit-fix-p cur)
                                     (mv (cadr cur) t)
                                   (mv cur nil)))
           (entry (rp-assoc-w/-tmp-var cur pp-binds))
           ((unless entry) (mv nil nil))
           (res (pp-remove-extraneous-sc (pp-entry->orig-term entry)))
           (res (cond ((and has-bit-fix
                            (can-be-removed-from-bit-fix res))
                       res)
                      (has-bit-fix
                       (progn$ (cwe "Could not removed bit-fix in  pp-apply-bindings-and-arg-lst for: ~p0  ~%"
                                    res)
                               `(bit-fix ,res)))
                      (t res))))
        (mv (cons res rest) valid)))
    ///
    (defret return-vals-of-<fn>
      (implies (and (rp-term-listp and-arg-lst)
                    (pp-binds-p pp-binds))
               (rp-term-listp res))))

  (define pp-apply-bindings ((pp-lst rp-term-listp)
                             (pp-binds pp-binds-p))
    :returns (mv res valid)

    (if (atom pp-lst)
        (mv nil t)
      (b* (((mv rest valid1) (pp-apply-bindings (cdr pp-lst) pp-binds))
           (cur (car pp-lst))
           ((mv cur negated)
            (case-match cur (('-- x) (mv x t)) (& (mv cur nil)))))
        (case-match cur
          (('and-list & ('list . and-arg-lst))
           (b* (((mv and-arg-lst valid2)
                 (pp-apply-bindings-and-arg-lst and-arg-lst pp-binds))
                (and-arg-lst (if (and$-list-ordered-p and-arg-lst)
                                 and-arg-lst
                               (sort-and$-list and-arg-lst (len and-arg-lst))))
                (cur (create-and-list-instance and-arg-lst)))
             (mv (cons (if negated `(-- ,cur) cur) rest)
                 (and* valid1 valid2))))
          (''1
           (mv (cons (if negated `(-- ,cur) cur) rest) valid1))
          (& (b* ((entry (rp-assoc-w/-tmp-var cur pp-binds))
                  ((unless entry) (mv nil nil))
                  (cur (pp-remove-extraneous-sc (pp-entry->orig-term entry))))
               (mv (cons (if negated `(-- ,cur) cur)  rest)
                   valid1))))))
    ///
    (defret return-vals-of-<fn>
      (implies (and (rp-term-listp pp-lst)
                    (pp-binds-p pp-binds))
               (rp-term-listp res)))))

(define pp-flatten-with-binds ((term (and (pp-term-p term)
                                          (rp-termp term)))
                               (signed booleanp)
                               &key
                               (disabled 'nil))
  :returns (pp-lst)
  (b* (((when (or disabled
                  (not (cons-count-compare term 20))
                  (not (mbt (and (pp-term-p term)
                                 (rp-termp term)
                                 t)))))
        (pp-flatten term signed :disabled disabled))
       ((mv honsed-pp-term pp-binds & valid)
        (pp-term-bind term nil 0))
       ((unless valid)
        (cwe "In pp-flatten-with-binds, pp-term-bind returned invalid bindings.
                                          for incoming term: ~p0 ~%" term)
        (pp-flatten term signed))
       (pp-lst (pp-flatten-memoized honsed-pp-term signed))
       ((mv res-pp-lst valid) (pp-apply-bindings pp-lst pp-binds))
       ((unless valid)
        (cwe "In pp-flatten-with-binds, pp-apply-bindings returned invalid.
                                          for incoming term: ~p0. bindings: ~p1
                                          and flattened term: ~p2 ~%" term
                                          pp-binds pp-lst)
        (pp-flatten term signed))
       (res-pp-lst (if (pp-lst-orderedp res-pp-lst)
                       res-pp-lst
                     (pp-sum-sort-lst res-pp-lst))))
    res-pp-lst)
  ///
  (profile 'pp-flatten-with-binds)
  (profile 'pp-apply-bindings)
  (profile 'pp-term-bind)

  (defret rp-term-listp-of-<fn>
    (implies (rp-termp term)
             (rp-term-listp pp-lst))))

(local
 (defthmd assoc-equal-is-RP-ASSOC-W/-TMP-VAR
   (implies t
            (equal (assoc-equal var binds)
                   (RP-ASSOC-W/-TMP-VAR var binds)))
   :hints (("Goal"
            :in-theory (e/d (RP-ASSOC-W/-TMP-VAR) ())))))

(local
 (defthmd existing-rp-assoc-w/-tmp-var-pp-binds-implies
   (and (implies (and (assoc-equal var pp-binds)
                      (pp-binds-p pp-binds))
                 (and (equal (car (assoc-equal var pp-binds)) var)
                      (symbolp var))))
   :rule-classes (:forward-chaining :rewrite)
   :hints (("Goal"
            :in-theory (e/d (rp-assoc-w/-tmp-var
                             PP-ENTRY->TMP-VAR)
                            ())))))

(local
 (defthm nonnil-assoc-equal-implies-consp-2
   (implies (and (ASSOC-EQUAL key alist) (pp-binds-p alist))
            (consp (ASSOC-EQUAL key alist)))
   :rule-classes :forward-chaining))

(local
 (defthm consp-ASSOC-EQUAL-implies-nonil
   (implies (consp (ASSOC-EQUAL key alist)) (ASSOC-EQUAL key alist))
   :rule-classes :forward-chaining))

(local
 (defthm ex-from-rp-when-car-is-quote
   (implies (equal 'quote (car x))
            (equal (ex-from-rp x) x))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (ex-from-rp is-rp) ())))))

(local
 (defthm ex-from-rp-when-car-is-list
   (implies (equal 'list (car x))
            (equal (ex-from-rp x) x))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (ex-from-rp is-rp) ())))))

(local
 (defthmd eval-of-RP-APPLY-BINDINGS-ex-from-rp
   (implies (and (rp-termp term)
                 (bindings-alistp bindings))
            (equal (rp-evlt (rp-apply-bindings (ex-from-rp term) bindings) a)
                   (rp-evlt (rp-apply-bindings term bindings) a)))))

(local
 (defthmd eval-of-RP-APPLY-BINDINGS-ex-from-rp-reverse
   (implies (and (syntaxp (or (atom term)
                              (not (equal (car term) 'ex-from-rp))))
                 (rp-termp term)
                 (bindings-alistp bindings))
            (equal (rp-evlt (rp-apply-bindings term bindings) a)
                   (rp-evlt (rp-apply-bindings (ex-from-rp term) bindings) a)))))

(local
 (defthm pp-binds-p-implies-bindings-alistp
   (implies (pp-binds-p pp-binds)
            (bindings-alistp pp-binds))
   :hints (("Goal"
            :in-theory (e/d (pp-binds-p
                             PP-ENTRY->ORIG-TERM)
                            ())))))

(local
 (create-regular-eval-lemma bit-fix 1 mult-formula-checks))
(local
 (create-regular-eval-lemma binary-not 1 mult-formula-checks))
(local
 (create-regular-eval-lemma binary-or 2 mult-formula-checks))
(local
 (create-regular-eval-lemma binary-xor 2 mult-formula-checks))
(local
 (create-regular-eval-lemma binary-and 2 mult-formula-checks))
(local
 (create-regular-eval-lemma binary-? 3 mult-formula-checks))
(local
 (create-regular-eval-lemma s 3 mult-formula-checks))

(local
 (defthmd CAN-BE-REMOVED-FROM-BIT-FIX-implies
   (implies (and (CAN-BE-REMOVED-FROM-BIT-FIX term)
                 (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (valid-sc term a))
            (and (bitp (rp-evlt term a))))
   :hints (("Goal"
            :in-theory (e/d* (BINARY-FNC-P
                              regular-eval-lemmas
                              CAN-BE-REMOVED-FROM-BIT-FIX)
                             (bitp))))))

(local
 (defthmd CAN-BE-REMOVED-FROM-BIT-FIX-implies-2
   (implies (and (CAN-BE-REMOVED-FROM-BIT-FIX (PP-REMOVE-EXTRANEOUS-SC term))
                 (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (valid-sc term a))
            (and (bitp (rp-evlt term a))))
   :hints (("Goal"
            :use ((:instance CAN-BE-REMOVED-FROM-BIT-FIX-implies
                             (term (PP-REMOVE-EXTRANEOUS-SC term))))
            :in-theory (e/d* ()
                             (bitp))))))

(local
 (defthm valid-sc-bindings-lemma-with-pp-binds
   (implies (and (valid-sc-bindings pp-binds a)
                 (assoc-equal var pp-binds))
            (VALID-SC (CDR (ASSOC-EQUAL var PP-BINDS))
                      A))))

(local
 (defret pp-apply-bindings-and-arg-lst-is-rp-apply-bindings-subterms-when-valid
   (implies (and valid
                 (pp-binds-p pp-binds)
                 (rp-term-listp and-arg-lst)

                 (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (valid-sc-bindings pp-binds a)
                 )
            (equal (rp-evlt-lst res a)
                   (rp-evlt-lst (rp-apply-bindings-subterms and-arg-lst pp-binds)
                                a)))
   :fn pp-apply-bindings-and-arg-lst
   :hints (("Goal"
            :expand ((RP-APPLY-BINDINGS (CADR (CAR AND-ARG-LST))
                                        PP-BINDS)
                     (RP-APPLY-BINDINGS (CAR AND-ARG-LST)
                                        PP-BINDS)
                     (rp-apply-bindings (ex-from-rp (car and-arg-lst))
                                        pp-binds)
                     (rp-apply-bindings-subterms and-arg-lst pp-binds))
            :in-theory (e/d (;;eval-of-RP-APPLY-BINDINGS-ex-from-rp-reverse
                             CAN-BE-REMOVED-FROM-BIT-FIX-implies
                             CAN-BE-REMOVED-FROM-BIT-FIX-implies-2
                             eval-of-RP-APPLY-BINDINGS-ex-from-rp

                             existing-rp-assoc-w/-tmp-var-pp-binds-implies
                             rp-apply-bindings-subterms
                             RP-ASSOC-W/-TMP-VAR
                             pp-entry->orig-term
                             pp-apply-bindings-and-arg-lst)
                            (;;RP-TRANS-OPENER

                             RP-EVLT-LST-OF-APPLY-BINDINGS-TO-EVL-LST
                             RP-EVLT-OF-APPLY-BINDINGS-TO-EVL
                             RP-APPLY-BINDINGS-SUBTERMS-TO-EVLT-LST
                             RP-APPLY-BINDINGS-TO-EVLT
                             RP-APPLY-BINDINGS))))))

(local
 (defthm VALID-SC-assoc-equal-lemma
   (implies (and (VALID-SC-BINDINGS PP-BINDS A)
                 (ASSOC-EQUAL key
                              PP-BINDS))
            (VALID-SC (CDR (ASSOC-EQUAL key
                                        PP-BINDS))
                      A))))

(local
 (defret valid-sc-subterms-of-PP-APPLY-BINDINGS-AND-ARG-LST
   (implies (and valid
                 (valid-sc-bindings PP-BINDS a))
            (valid-sc-subterms res a))
   :fn pp-apply-bindings-and-arg-lst
   :hints (("Goal"
            :in-theory (e/d (pp-apply-bindings-and-arg-lst
                             RP-ASSOC-W/-TMP-VAR
                             PP-ENTRY->ORIG-TERM)
                            ())))))

(local
 (create-regular-eval-lemma and-list 2 mult-formula-checks))
(local
 (create-regular-eval-lemma -- 1 mult-formula-checks))

(local
 (defthm car-of-assoc-equal
   (implies (ASSOC-EQUAL VAR PP-BINDS)
            (equal (car (ASSOC-EQUAL VAR PP-BINDS)) var))))

(local
 (defthm RP-APPLY-BINDINGS-lemma-when-var-is-present-in-pp-binds
   (implies (and (ASSOC-EQUAL var PP-BINDS)
                 (PP-BINDS-P PP-BINDS))
            (equal (rp-apply-bindings var pp-binds)
                   (CDR (ASSOC-EQUAL var PP-BINDS))))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance rp-termp/symbolp-of-rp-assoc-w/-tmp-var
                             (x var)
                             (alist pp-binds)))
            :expand (RP-APPLY-BINDINGS var pp-BINDS)
            :in-theory (e/d (;;PP-BINDS-P
                             assoc-equal
                             RP-ASSOC-W/-ORIG-TERM
                             RP-ASSOC-W/-TMP-VAR
                             PP-ENTRY->TMP-VAR
                             PP-ENTRY->ORIG-TERM)
                            ())))))

(local
 (defret pp-apply-bindings-is-rp-apply-bindings-subterms-when-valid
   (implies (and valid
                 (rp-term-listp pp-lst)
                 (pp-binds-p pp-binds)
                 (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (valid-sc-bindings pp-binds a)
                 )
            (equal (rp-evlt-lst res a)
                   (rp-evlt-lst (rp-apply-bindings-subterms pp-lst pp-binds) a)))
   :fn pp-apply-bindings
   :hints (("goal"
            :expand ((rp-apply-bindings (car pp-lst) pp-binds)
                     (rp-apply-bindings-subterms pp-lst pp-binds)
                     (rp-apply-bindings (caddr (car pp-lst))
                                        pp-binds)
                     (rp-apply-bindings (cadr (car pp-lst))
                                        pp-binds)
                     (rp-apply-bindings (caddr (cadr (car pp-lst)))
                                        pp-binds))
            :in-theory (e/d* (;;create-and-list-instance
                              and-list
                              existing-rp-assoc-w/-tmp-var-pp-binds-implies
                              rp-apply-bindings
                              pp-apply-bindings
                              rp-assoc-w/-tmp-var
                              ;;create-and-list-instance
                              pp-entry->orig-term
                              regular-eval-lemmas)
                             (RP-TRANS-OPENER
                              rp-evlt-lst-of-apply-bindings-to-evl-lst
                              rp-evlt-of-apply-bindings-to-evl
                              rp-apply-bindings-subterms-to-evlt-lst
                              rp-apply-bindings-to-evlt
                              rp-apply-bindings
                              rp-trans))))))

(local
 (defret valid-sc-bindings-of-pp-term-bind
   (implies (and (valid-sc-bindings pp-binds a)
                 (equal (len pp-binds) index)
                 (pp-binds-p pp-binds)
                 valid
                 (valid-sc term a)
                 (rp-termp term)
                 (pp-term-p term))
            (valid-sc-bindings res-pp-binds a))
   :fn pp-term-bind
   :hints (("goal"
            :in-theory (e/d (pp-term-bind
                             make-pp-entry)
                            ((:linear acl2::apply$-badgep-properties . 1)
                             (:definition acl2::apply$-badgep)
                             (:definition subsetp-equal)
                             (:definition member-equal)
                             (:rewrite
                              acl2::member-equal-newvar-components-1)

                             (:rewrite ex-from-rp-of-binary-fnc)
                             (:rewrite binary-fnc-p-relieve)
                             (:definition ex-from-rp)
                             ;;(:rewrite valid-sc-caddr)

                             eval-and-all
                             include-fnc))))))

(local
 (defthm rp-evlt-of-symbol
   (implies (and (symbolp x)
                 x)
            (equal (rp-evlt x a)
                   (cdr (assoc-equal x a))))
   :hints (("Goal"
            :in-theory (e/d (rp-trans) ())))))

;; (local
;;  (defthmd eval-of-ex-from-rp-reverse
;;    (implies (or (atom x)
;;                 (not (equal (car x) 'ex-from-rp)))
;;             (equal (rp-evlt x a)
;;                    (rp-evlt (

(local
 (defthm ASSOC-EQUAL-of-BIND-BINDINGS-AUX
   (implies (alistp a1)
            (equal (assoc-equal var (BIND-BINDINGS-AUX a1 a2))
                   (if (assoc-equal var a1)
                       (cons var (rp-evl (cdr (assoc-equal var a1)) a2))
                     nil)))))

(local
 (defthm strip-cars-of-rp-trans-bindings
   (equal (STRIP-CARS (RP-TRANS-BINDINGS PP-BINDS))
          (STRIP-CARS PP-BINDS))))

#|(local
 (defthm assoc-equal-of-rp-assoc-w/-orig-term-lemma
   (implies (equal (strip-cars pp-binds)
                   (strip-cars pp-binds-2))
            (equal (ASSOC-EQUAL (CAR (RP-ASSOC-W/-ORIG-TERM term PP-BINDS))
                                PP-BINDS-2)
                   (RP-ASSOC-W/-ORIG-TERM term PP-BINDS-2)))
   :hints (("Goal"
            :in-theory (e/d (RP-ASSOC-W/-ORIG-TERM) ())))))|#

#|(local
 (defthm valid-sc-of-pp-term-bind-lemma
   (implies (and (pp-binds-p pp-binds)
                 (RP-ASSOC-W/-ORIG-TERM (EX-FROM-RP TERM)
                                        PP-BINDS))
            (equal
             (CDR
              (ASSOC-EQUAL (PP-ENTRY->TMP-VAR (RP-ASSOC-W/-ORIG-TERM (EX-FROM-RP TERM) PP-BINDS))
                           (BIND-BINDINGS-AUX (RP-TRANS-BINDINGS PP-BINDS)
                                              A)))
             (rp-evlt term a)))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d (PP-ENTRY->TMP-VAR
                             RP-ASSOC-W/-ORIG-TERM
                             PP-ENTRY->ORIG-TERM)
                            ())))))|#

(local
 (defthm HAS-BITP-RP-implies
   (implies (and (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (HAS-BITP-RP TERM)
                 (valid-sc term a))
            (and (bitp (rp-evlt term a))
                 ))
   :hints (("Goal"

            :in-theory (e/d (;;rp-evl-when-is-rp
                             valid-sc-single-step
                             HAS-BITP-RP)
                            (EX-FROM-RP-LEMMA1
                             bitp))))))

(local
 (defthm rp-assoc-w/-orig-term-of-ex-from-rp
   (equal (rp-assoc-w/-orig-term (ex-from-rp term) pp-binds)
          (rp-assoc-w/-orig-term term pp-binds))
   :hints (("goal"
            :in-theory (e/d (rp-assoc-w/-orig-term) ())))))

;; (local
;;  (define bind-bindings-aux-with-trans (b1 b2)
;;    :verify-guards nil
;;    (if (atom b1)
;;        nil
;;        (cons (cons (caar b1) (rp-evlt (cdar b1) b2))
;;              (bind-bindings-aux-with-trans (cdr b1) b2)))))

;; (local
;;  (defthmd BIND-BINDINGS-AUX-to-bind-bindings-aux-with-trans
;;    (equal (BIND-BINDINGS-AUX (RP-TRANS-BINDINGS b1)
;;                              b2)
;;           (bind-bindings-aux-with-trans b1 b2))
;;    :hints (("Goal"
;;             :in-theory (e/d (bind-bindings-aux-with-trans) ())))))

(local
 (defthmd include-fnc-of-symbol
   (implies (symbolp x)
            (equal (include-fnc x fn)
                   nil))
   :hints (("Goal"
            :in-theory (e/d (include-fnc) ())))))

(local
 (defret not-include-fnc-of-pp-term-bind
   (implies (and valid
                 (pp-binds-p pp-binds)
                 (rp-termp term)
                 (pp-term-p term)
                 (EQUAL (LEN PP-BINDS) INDEX))
            (not (include-fnc res 'rp)))
   :fn pp-term-bind
   :hints (("Goal"
            :in-theory (e/d (include-fnc-of-symbol
                             INCLUDE-FNC
                             pp-term-bind)
                            ())))))

(local
 (defret valid-sc-of-pp-term-bind
   (implies (and valid
                 (pp-binds-p pp-binds)
                 (rp-termp term)
                 (pp-term-p term)
                 (EQUAL (LEN PP-BINDS) INDEX))
            (valid-sc res a))
   :fn pp-term-bind
   :hints (("Goal"
            :in-theory (e/d (NOT-INCLUDE-RP-MEANS-VALID-SC
                             pp-term-bind)
                            ())))))

(local
 (defthm rp-evlt-of-known-a-and-symbol
   (implies (and (symbolp x)
                 x)
            (equal (rp-evlt x (cons (cons x y) a))
                   y))
   :hints (("Goal"
            :in-theory (e/d (rp-trans) ())))))

(local
 (defthm when-ex-from-rp-is-1-or-zero
   (and (implies (EQUAL (EX-FROM-RP TERM) ''1)
                 (equal (EQUAL 1 (RP-EVLT TERM A)) t))
        (implies (EQUAL (EX-FROM-RP TERM) ''0)
                 (equal (EQUAL 0 (RP-EVLT TERM A)) t)))
   :hints (("Goal"
            :in-theory (e/d (ex-from-rp rp-trans is-rp) ())))))

(local
 (defun ends-with-p (x y)
   (if (atom y)
       (equal x y)
     (if (equal x y)
         t
       (ends-with-p x (cdr y))))))

(local
 (defthm ends-with-p-chain
   (implies (and (ends-with-p x y)
                 (ends-with-p y z))
            (ends-with-p x z))))

(local
 (defret ends-with-p-of-pp-term-bind
   (ends-with-p pp-binds res-pp-binds)
   :fn pp-term-bind
   :hints (("Goal"
            :in-theory (e/d (pp-term-bind) ())))))

(local
 (encapsulate
   nil

   (defun unique-lstp (lst)
     (if (atom lst)
         (equal lst nil)
       (and (not (member (car lst) (cdr lst)))
            (unique-lstp (cdr lst)))))

   (local
    (defun rp-assoc-w/-orig-term2 (orig-term alist)
      (if (or (atom alist)
              (atom (car alist)))
          nil
        (if (rp-equal-cnt orig-term
                          (pp-entry->orig-term (car alist))
                          2)
            alist
          (rp-assoc-w/-orig-term2 orig-term (cdr alist))))))

   (defthmd implode-equivalance-with-string-2
     (implies (and (stringp string)
                   (characterp x)
                   (character-listp rest))
              (and (equal (equal (acl2::implode (cons x rest))
                                 string)
                          (and (equal x (car (explode string)))
                               (equal rest (cdr (explode string)))))
                   (equal (equal string (acl2::implode (cons x rest)))
                          (and (equal x (car (explode string)))
                               (equal rest (cdr (explode string)))))))
     :hints (("goal"
              :use ((:instance
                     implode-equivalance-with-string
                     (chars (cons x rest))))
              :in-theory (e/d ()
                              ()))))

   (defthm dummy-len-consp-lemma
     (implies (< 4 (+ 3 (len x)))
              (consp x))
     :rule-classes :forward-chaining
     :hints (("goal"
              :in-theory (e/d () ()))))

   (local
    (defthm character-listp-of-cdr
      (implies (character-listp lst)
               (and (implies (consp lst) (characterp (car lst)))
                    (implies (and (consp lst) (consp (cdr lst)))
                             (characterp (cadr lst)))
                    (implies (and (consp lst)
                                  (consp (cdr lst))
                                  (consp (cddr lst)))
                             (characterp (caddr lst)))
                    (implies (and (consp lst)
                                  (consp (cdr lst))
                                  (consp (cddr lst))
                                  (consp (cdddr lst)))
                             (characterp (cadddr lst)))
                    (character-listp (cdr lst))))))

   (local
    (defthm cons-equiv
      (equal (equal (cons x y) other)
             (and (consp other)
                  (equal (car other) x)
                  (equal (cdr other) y)))))

   (local
    (defthm rp-evlt-of-pp-term-bind-lemma0
      (implies (and (pp-binds-p alist)
                    (rp-assoc-w/-orig-term term alist))
               (equal (symbol-name (car (rp-assoc-w/-orig-term term alist)))
                      (str::cat
                       "VAR-"
                       (str::nat-to-dec-string
                        (len (cdr (rp-assoc-w/-orig-term2 term alist)))))))
      :hints (("goal"
               :induct (rp-assoc-w/-orig-term2 term alist)
               :do-not-induct t
               :expand ((pp-binds-p alist)
                        (:free (x) (nthcdr 4 x))
                        (:free (x) (nthcdr 3 x))
                        (:free (x) (nthcdr 2 x))
                        (:free (x) (nthcdr 1 x)))
               :in-theory (e/d (nthcdr
                                pp-binds-p
                                implode-equivalance-with-string-2
                                implode-equivalance-with-string
                                rp-assoc-w/-orig-term
                                pp-entry->orig-term
                                pp-entry->tmp-var)
                               ())))))

   (defthm rp-evlt-of-pp-term-bind-lemma2
     (implies (case-split (not (rp-assoc-w/-orig-term term alist)))
              (equal (symbol-name (car (rp-assoc-w/-orig-term term alist)))
                     "NIL"))
     :hints (("goal"

              :do-not-induct t

              :in-theory (e/d ()
                              ()))))

   (local
    (defthm symbol-name-equiv-lemma
      (implies (and (symbolp x)
                    (symbolp y)
                    (not (equal (symbol-name x) (symbol-name y))))
               (equal (equal x y) nil))))

   (local
    (defthm implode-equiv-implies
      (implies (and (character-listp x)
                    (stringp other)
                    (equal (acl2::implode x) other))
               (equal x (explode other)))
      :rule-classes nil))

   (local
    (defthm equiv-with-explode
      (implies (and (character-listp other)
                    (stringp x))
               (equal (equal other (explode x))
                      (equal (acl2::implode other) x)))))

   (defthm symbol-p-of-car-of-rp-assoc-w/-orig-term-lemma
     (implies (pp-binds-p lst)
              (symbolp (car (rp-assoc-w/-orig-term term lst))))
     :hints (("goal"
              :cases ((rp-assoc-w/-orig-term term lst))
              :do-not-induct t
              :in-theory (e/d () ()))))

   (local
    (defthm len-of-RP-ASSOC-W/-ORIG-TERM2
      (implies (rp-assoc-w/-orig-term2 term lst)
               (<= (len (rp-assoc-w/-orig-term2 term lst))
                   (len lst)))
      :hints (("Goal"
               :in-theory (e/d () ())))))

   (local
    (defthm RP-ASSOC-W/-ORIG-TERM-consp-lemma
      (implies (or (RP-ASSOC-W/-ORIG-TERM2 TERM lst)
                   (RP-ASSOC-W/-ORIG-TERM TERM lst))
               (and (consp (RP-ASSOC-W/-ORIG-TERM TERM lst))
                    (consp (RP-ASSOC-W/-ORIG-TERM2 TERM lst))))
      :hints (("Goal"
               :in-theory (e/d (RP-ASSOC-W/-ORIG-TERM) ())))))

   (local
    (defthm RP-ASSOC-W/-ORIG-TERM2-lemma
      (implies (RP-ASSOC-W/-ORIG-TERM term alist)
               (RP-ASSOC-W/-ORIG-TERM2 term alist))
      :hints (("Goal"
               :in-theory (e/d (RP-ASSOC-W/-ORIG-TERM) ())))))

   #|(local
   (defthm len-of-cdr ; ; ; ; ; ;
   (implies (consp x) ; ; ; ; ; ;
   (equal (len (cdr x)) ; ; ; ; ; ;
   (1- (len x))))))|#

   (local
    (defthm dummy-len-lemma
      (implies (and (consp other)
                    (and (<= (len other) (len lst))))
               (equal (equal (1+ (len lst)) (len (cdr other)))
                      nil))))

   (defthm rp-evlt-of-pp-term-bind-lemma1
     (implies (pp-binds-p (cons first rest))
              (not (equal (car (rp-assoc-w/-orig-term term rest))
                          (car first))))
     :hints (("goal"
              :expand ((:free (x) (nthcdr 4 x))
                       (:free (x) (nthcdr 3 x))
                       (:free (x) (nthcdr 2 x))
                       (:free (x) (nthcdr 1 x)))
              :in-theory (e/d (take
                               rp-assoc-w/-orig-term
                               pp-entry->orig-term
                               pp-entry->tmp-var
                               IMPLODE-EQUIVALANCE-WITH-STRING
                               IMPLODE-EQUIVALANCE-WITH-STRING-2)
                              ()))))

   (defthm rp-evlt-of-pp-term-bind-lemma
     (implies (and (pp-binds-p pp-binds)
                   (RP-ASSOC-W/-ORIG-TERM TERM PP-BINDS))
              (equal (CDR
                      (ASSOC-EQUAL (PP-ENTRY->TMP-VAR (RP-ASSOC-W/-ORIG-TERM TERM PP-BINDS))
                                   (APPEND (BIND-BINDINGS-AUX (RP-TRANS-BINDINGS PP-BINDS)
                                                              A)
                                           A)))
                     (rp-evlt term a)))
     :hints (("Goal"
              :in-theory (e/d (RP-ASSOC-W/-ORIG-TERM
                               PP-ENTRY->TMP-VAR
                               PP-ENTRY->ORIG-TERM
                               pp-binds-p)
                              ()))))

   (local
    (defthm pp-binds-have-unique-keys-lemma1
      (implies (and (pp-binds-p rest)
                    (pp-binds-p (cons first rest2))
                    (>= (len rest2) (len rest)))
               (not (member-equal (car first)
                                  (strip-cars rest))))
      :hints (("goal"

               :expand ((:free (x) (nthcdr 4 x))
                        (:free (x) (nthcdr 3 x))
                        (:free (x) (nthcdr 2 x))
                        (:free (x) (nthcdr 1 x)))
               :in-theory (e/d (take
                                rp-assoc-w/-orig-term
                                pp-entry->orig-term
                                pp-entry->tmp-var
                                IMPLODE-EQUIVALANCE-WITH-STRING
                                IMPLODE-EQUIVALANCE-WITH-STRING-2)
                               ())))))

   (local
    (defthm pp-binds-have-unique-keys-lemma ;;;;;;;;;;;;;;;;;;;;;;;;;;;
      (implies (pp-binds-p (cons first rest))
               (not (member-equal (car first)
                                  (strip-cars rest))))
      :hints (("goal"
               :do-not-induct t
               :use ((:instance pp-binds-have-unique-keys-lemma1
                                (rest2 rest)))
               :expand ((:free (x) (nthcdr 4 x))
                        (:free (x) (nthcdr 3 x))
                        (:free (x) (nthcdr 2 x))
                        (:free (x) (nthcdr 1 x)))
               :in-theory (e/d (take
                                rp-assoc-w/-orig-term
                                pp-entry->orig-term
                                pp-entry->tmp-var
                                IMPLODE-EQUIVALANCE-WITH-STRING
                                IMPLODE-EQUIVALANCE-WITH-STRING-2)
                               ())))))

   (defthm pp-binds-have-unique-keys
     (implies (pp-binds-p pp-binds)
              (and (unique-lstp (strip-cars pp-binds))))
     :hints (("Goal"
              :expand ((:free (x) (nthcdr 4 x))
                       (:free (x) (nthcdr 3 x))
                       (:free (x) (nthcdr 2 x))
                       (:free (x) (nthcdr 1 x)))
              :in-theory (e/d (take
                               rp-assoc-w/-orig-term
                               pp-entry->orig-term
                               pp-entry->tmp-var
                               IMPLODE-EQUIVALANCE-WITH-STRING
                               IMPLODE-EQUIVALANCE-WITH-STRING-2
                               pp-binds-p
                               PP-ENTRY->ORIG-TERM
                               PP-ENTRY->TMP-VAR)
                              ()))))

   (local
    (defthm dummy-ends-with-p-lemma
      (implies (< (len lst2) (len lst1))
               (not (ends-with-p lst1 lst2)))
      :otf-flg t
      :hints (("goal"
               ;;:use ((:instance dummy-cons-lemma))
               :expand ((ends-with-p lst (cdr lst))
                        (ENDS-WITH-P LST (CDDR LST)))
               :in-theory (e/d () (acl2::cons-car-cdr))))))

   (local
    (defthm dummy-len-lemma2
      (implies (consp lst)
               (< (len (cdr lst)) (len lst)))
      :hints (("Goal"
               :in-theory (e/d () ())))))

   (local
    (defthm dummy-cars-equiv-lemma
      (implies (not (equal (car x) (car y)))
               (equal (equal x y)
                      nil))))

   (local
    (defthmd member-equal-of-pp-binds-and-ends-with-p-lemma1
      (implies (and (ends-with-p lst-small (cons var rest))
                    (unique-lstp lst-small)
                    (unique-lstp (cons var rest))
                    (member-equal var lst-small))
               (equal (cons var rest)
                      lst-small))
      :hints (("Goal"
               :induct (member-equal var rest)
               :in-theory (e/d () ())))))

   (local
    (defthm member-equal-of-pp-binds-and-ends-with-p-lemma
      (implies (and (ends-with-p lst-small lst-big)
                    (unique-lstp lst-small)
                    (unique-lstp lst-big)
                    (member-equal var lst-small))
               (equal (member-equal var lst-big)
                      (member-equal var lst-small)))
      :hints (("subgoal *1/2"
               :use ((:instance member-equal-of-pp-binds-and-ends-with-p-lemma1
                                (var (car lst-big))
                                (rest (cdr lst-big)))))
              ("Goal"
               :induct (member-equal var lst-big)
               :in-theory (e/d () ())))))

   (local
    (defthm dummy-ends-with-p-lemma2
      (implies (and (consp lst-small)
                    (ENDS-WITH-P LST-SMALL REST))
               (ENDS-WITH-P (CDR LST-SMALL) REST))))

   (local
    (defthm ASSOC-EQUAL-OF-PP-BINDS-AND-ENDS-WITH-P-LEMMA1-1
      (implies (and (CONSP LST-SMALL)
                    (UNIQUE-LSTP (STRIP-CARS LST-SMALL))
                    (NOT (MEMBER-EQUAL (CAR VAR)
                                       (STRIP-CARS LST-SMALL))))
               (equal (EQUAL (CAR VAR) (CAR (CAR LST-SMALL)))
                      nil))))

   (defthm ends-with-p-and-member-equal-lemma
     (implies (and (ends-with-p lst-small rest)
                   (not (member-equal var rest)))
              (not (member-equal var lst-small))))

   (defthm ends-with-strip-cars-lemma
     (implies (ends-with-p lst-small rest)
              (ends-with-p (strip-cars lst-small) (strip-cars rest))))

   (local
    (defthm assoc-equal-of-pp-binds-and-ends-with-p-lemma1-2
      (IMPLIES (AND (CONSP LST-SMALL)
                    (ENDS-WITH-P LST-SMALL REST)
                    (UNIQUE-LSTP (STRIP-CARS LST-SMALL))
                    (NOT (MEMBER-EQUAL (CAR VAR)
                                       (STRIP-CARS REST)))
                    (CAR LST-SMALL))
               (not (EQUAL (CAR VAR) (CAR (CAR LST-SMALL)))))
      :hints (("Goal"
               :in-theory (e/d () ())))))

   (local
    (defthmd assoc-equal-of-pp-binds-and-ends-with-p-lemma1
      (implies (and (ends-with-p lst-small (cons var rest))
                    (unique-lstp (strip-cars lst-small))
                    (unique-lstp (strip-cars (cons var rest)))
                    (assoc-equal (car var) lst-small))
               (equal (cons var rest)
                      lst-small))
      :hints (("Goal"
               :induct (assoc-equal (car var) lst-small)
               :in-theory (e/d (ENDS-WITH-P) ())))))

   ;;;;;;;;;;;;
   (defthm assoc-equal-of-pp-binds-and-ends-with-p
     (implies (and (ends-with-p bindings-small bindings-big)
                   (pp-binds-p bindings-small)
                   (pp-binds-p bindings-big)
                   (assoc-equal var bindings-small))
              (equal (assoc-equal var bindings-big)
                     (assoc-equal var bindings-small)))
     :hints (("subgoal *1/2"
              :use ((:instance assoc-equal-of-pp-binds-and-ends-with-p-lemma1
                               (var (car BINDINGS-BIG))
                               (rest (cdr BINDINGS-BIG))
                               (lst-small BINDINGS-SMALL))))
             ("Goal"
              :in-theory (e/d (PP-ENTRY->ORIG-TERM) ()))))))

(local
 (defines all-vars-bound-p
   :flag-local nil
   :verify-guards nil
   (define all-vars-bound-p (term bindings)
     :returns result
     (cond ((atom term)
            (consp (ASSOC-EQUAL TERM bindings)))
           ((acl2::fquotep term) t)
           (T (all-vars-bound-lst-p (cdr term) bindings))))
   (define all-vars-bound-lst-p (lst bindings)
     :returns result
     (if (atom lst)
         (equal lst nil)
       (and (all-vars-bound-p (car lst) bindings)
            (all-vars-bound-lst-p (cdr lst) bindings))))))

(local
 (defthm PP-ENTRY->TMP-VAR-is-not-quote
   (implies (and (CONSP (PP-ENTRY->TMP-VAR (RP-ASSOC-W/-ORIG-TERM TERM
                                                                  PP-BINDS)))
                 (pp-binds-p pp-binds))
            (NOT
             (EQUAL (CAR (PP-ENTRY->TMP-VAR (RP-ASSOC-W/-ORIG-TERM TERM PP-BINDS)))
                    'QUOTE)))
   :hints (("Goal"
            :in-theory (e/d (RP-ASSOC-W/-ORIG-TERM) ())))
   ))

(local
 (defthm cdr-of-pp-entry->tmp-var
   (implies (pp-binds-p pp-binds)
            (equal (cdr (pp-entry->tmp-var
                         (rp-assoc-w/-orig-term term pp-binds)))
                   nil))
   :hints (("Goal"
            :in-theory (e/d (pp-entry->tmp-var
                             RP-ASSOC-W/-ORIG-TERM)
                            ())))))

(local
 (defthm consp-of-assoc-equal
   (implies (alistp y)
            (iff (consp (assoc-equal x y))
                 (assoc-equal x y)))))

(local
 (defthm dummy-assoc-equal-pp-entry->tmp-var-lemma
   (implies
    (and
     (rp-assoc-w/-orig-term term pp-binds))
    (assoc-equal (pp-entry->tmp-var (rp-assoc-w/-orig-term term pp-binds))
                 pp-binds))
   :hints (("goal"
            :in-theory (e/d (pp-entry->tmp-var
                             rp-assoc-w/-orig-term)
                            ())))))

(local
 (defthm ends-with-p-and-assoc-equal-lemma
   (implies (and (alistp bindings)
                 (alistp bindings-small)
                 (ENDS-WITH-P BINDINGS-SMALL BINDINGS)
                 (CONSP (ASSOC-EQUAL TERM BINDINGS-SMALL)))
            (CONSP (ASSOC-EQUAL TERM BINDINGS)))))

(local
 (defret-mutual all-vars-bound-p-ends-with-p-lemma
   (defret all-vars-bound-p-ends-with-p-lemma
     (implies (and (alistp bindings)
                   (alistp bindings-small)
                   (ends-with-p bindings-small bindings)
                   (all-vars-bound-p term bindings-small))
              (all-vars-bound-p term bindings))
     :fn all-vars-bound-p)
   (defret all-vars-bound-lst-p-ends-with-p-lemma
     (implies (and (alistp bindings)
                   (alistp bindings-small)
                   (ends-with-p bindings-small bindings)
                   (all-vars-bound-lst-p lst bindings-small))
              (all-vars-bound-lst-p lst bindings))
     :fn all-vars-bound-lst-p)
   :mutual-recursion all-vars-bound-p
   :hints (("goal"
            :in-theory (e/d (all-vars-bound-lst-p
                             all-vars-bound-p)
                            ())))))

(local
 (defret alistp-of-PP-TERM-BIND
   (implies (alistp pp-binds)
            (alistp res-pp-binds))
   :fn pp-term-bind
   :hints (("Goal"
            :in-theory (e/d (pp-term-bind) ())))))

(local
 (defret all-vars-bound-p-of-pp-term-bind
   (implies (and valid
                 (pp-binds-p pp-binds)
                 (rp-termp term)
                 (pp-term-p term)
                 (equal (len pp-binds) index))
            (all-vars-bound-p res res-pp-binds))
   :fn pp-term-bind
   :otf-flg t
   :hints (("subgoal *1/2"
            :use ((:instance
                   all-vars-bound-p-ends-with-p-lemma
                   (term (mv-nth 0
                                 (pp-term-bind (cadr (ex-from-rp term))
                                               pp-binds (len pp-binds))))
                   (bindings
                    (mv-nth 1
                            (pp-term-bind (caddr (ex-from-rp term))
                                          (mv-nth 1
                                                  (pp-term-bind (cadr (ex-from-rp term))
                                                                pp-binds (len pp-binds)))
                                          (mv-nth 2
                                                  (pp-term-bind (cadr (ex-from-rp term))
                                                                pp-binds (len pp-binds))))))
                   (bindings-small
                    (mv-nth 1
                            (pp-term-bind (cadr (ex-from-rp term))
                                          pp-binds (len pp-binds)))))))
           ("subgoal *1/1"
            :use ((:instance
                   all-vars-bound-p-ends-with-p-lemma
                   (term (mv-nth 0
                                 (pp-term-bind (cadr (ex-from-rp term))
                                               pp-binds (len pp-binds))))
                   (bindings
                    (mv-nth 1
                            (pp-term-bind (caddr (ex-from-rp term))
                                          (mv-nth 1
                                                  (pp-term-bind (cadr (ex-from-rp term))
                                                                pp-binds (len pp-binds)))
                                          (mv-nth 2
                                                  (pp-term-bind (cadr (ex-from-rp term))
                                                                pp-binds (len pp-binds))))))
                   (bindings-small
                    (mv-nth 1
                            (pp-term-bind (cadr (ex-from-rp term))
                                          pp-binds (len pp-binds)))))

                  (:instance
                   all-vars-bound-p-ends-with-p-lemma
                   (term
                    (mv-nth 0
                            (pp-term-bind (cadr (ex-from-rp term))
                                          pp-binds (len pp-binds))))
                   (bindings
                    (mv-nth
                     1
                     (pp-term-bind
                      (cadddr (ex-from-rp term))
                      (mv-nth 1
                              (pp-term-bind (caddr (ex-from-rp term))
                                            (mv-nth 1
                                                    (pp-term-bind (cadr (ex-from-rp term))
                                                                  pp-binds (len pp-binds)))
                                            (mv-nth 2
                                                    (pp-term-bind (cadr (ex-from-rp term))
                                                                  pp-binds (len pp-binds)))))
                      (mv-nth
                       2
                       (pp-term-bind (caddr (ex-from-rp term))
                                     (mv-nth 1
                                             (pp-term-bind (cadr (ex-from-rp term))
                                                           pp-binds (len pp-binds)))
                                     (mv-nth 2
                                             (pp-term-bind (cadr (ex-from-rp term))
                                                           pp-binds (len pp-binds))))))))
                   (bindings-small
                    (mv-nth 1
                            (pp-term-bind (caddr (ex-from-rp term))
                                          (mv-nth 1
                                                  (pp-term-bind (cadr (ex-from-rp term))
                                                                pp-binds (len pp-binds)))
                                          (mv-nth 2
                                                  (pp-term-bind (cadr (ex-from-rp term))
                                                                pp-binds (len
                                                                          pp-binds)))))))

                  (:instance
                   all-vars-bound-p-ends-with-p-lemma
                   (term
                    (mv-nth 0
                            (pp-term-bind (caddr (ex-from-rp term))
                                          (mv-nth 1
                                                  (pp-term-bind (cadr (ex-from-rp term))
                                                                pp-binds (len pp-binds)))
                                          (mv-nth 2
                                                  (pp-term-bind (cadr (ex-from-rp term))
                                                                pp-binds (len pp-binds))))))
                   (bindings
                    (mv-nth
                     1
                     (pp-term-bind
                      (cadddr (ex-from-rp term))
                      (mv-nth 1
                              (pp-term-bind (caddr (ex-from-rp term))
                                            (mv-nth 1
                                                    (pp-term-bind (cadr (ex-from-rp term))
                                                                  pp-binds (len pp-binds)))
                                            (mv-nth 2
                                                    (pp-term-bind (cadr (ex-from-rp term))
                                                                  pp-binds (len pp-binds)))))
                      (mv-nth
                       2
                       (pp-term-bind (caddr (ex-from-rp term))
                                     (mv-nth 1
                                             (pp-term-bind (cadr (ex-from-rp term))
                                                           pp-binds (len pp-binds)))
                                     (mv-nth 2
                                             (pp-term-bind (cadr (ex-from-rp term))
                                                           pp-binds (len pp-binds))))))))
                   (bindings-small
                    (mv-nth 1
                            (pp-term-bind (caddr (ex-from-rp term))
                                          (mv-nth 1
                                                  (pp-term-bind (cadr (ex-from-rp term))
                                                                pp-binds (len pp-binds)))
                                          (mv-nth 2
                                                  (pp-term-bind (cadr (ex-from-rp term))
                                                                pp-binds (len pp-binds)))))))))
           ("goal"
            :expand ((all-vars-bound-p
                      (pp-entry->tmp-var (rp-assoc-w/-orig-term term pp-binds))
                      pp-binds)
                     (:free (x y bindings)
                            (all-vars-bound-p (cons x y) bindings))
                     (:free (x y bindings)
                            (all-vars-bound-lst-p (cons x y) bindings)))
            :in-theory (e/d* (all-vars-bound-p
                              all-vars-bound-lst-p
                              make-pp-entry
                              pp-term-bind)
                             ())))))

(local
 (defthm
   rp-evlt-of-variable
   (implies (symbolp acl2::x)
            (equal (rp-evlt acl2::x acl2::a)
                   (and acl2::x
                        (cdr (assoc-equal acl2::x acl2::a)))))
   :hints (("Goal"
            :in-theory (e/d (rp-trans) ()))) ))

(local
 (defthm assoc-equal-of-bind-bindings
   (implies (assoc-equal term bindings)
            (equal (cdr (ASSOC-EQUAL TERM
                                     (APPEND (BIND-BINDINGS-AUX BINDINGS A)
                                             A)))
                   (rp-evl (cdr (assoc-equal term bindings)) a)))))

(local
 (defthm ASSOC-EQUAL-of-RP-TRANS-BINDINGS
   (implies (alistp bindings)
            (EQUAL (CONSP (ASSOC-EQUAL TERM (RP-TRANS-BINDINGS BINDINGS)))
                   (CONSP (ASSOC-EQUAL TERM BINDINGS))))))

(local
 (defret-mutual all-var-bound-p-with-rp-trans-bindings
   (defret all-var-bound-p-with-rp-trans-bindings
     (implies (alistp bindings)
              (equal (all-vars-bound-p term (rp-trans-bindings bindings))
                     (all-vars-bound-p term bindings)))
     :fn all-vars-bound-p)
   (defret all-var-bound-lst-p-with-rp-trans-bindings
     (implies (alistp bindings)
              (equal (all-vars-bound-lst-p lst (rp-trans-bindings bindings))
                     (all-vars-bound-lst-p lst bindings)))
     :fn all-vars-bound-lst-p)
   :mutual-recursion all-vars-bound-p
   :hints (("Goal"
            :in-theory (e/d (all-vars-bound-p
                             RP-TRANS-BINDINGS
                             all-vars-bound-lst-p)
                            ())))))

(local
 (defthm-rp-trans
   (defthm rp-evlt-of-big-pp-binds-to-small-binds
     (implies (and (all-vars-bound-p term bindings-small)
                   (rp-termp term)
                   (alistp bindings)
                   (alistp bindings-small)
                   (ends-with-p bindings-small bindings)
                   (pp-binds-p bindings-small)
                   (pp-binds-p bindings)
                   )
              (equal (rp-evlt term (bind-bindings bindings a))
                     (rp-evlt term (bind-bindings bindings-small a))))

     :flag rp-trans)
   (defthm rp-evlt-lst-of-big-pp-binds-to-small-binds
     (implies (and (all-vars-bound-lst-p lst bindings-small)
                   (rp-term-listp lst)
                   (alistp bindings)
                   (alistp bindings-small)
                   (ends-with-p bindings-small bindings)
                   (pp-binds-p bindings-small)
                   (pp-binds-p bindings)
                   )
              (equal (rp-evlt-lst lst (bind-bindings bindings a))
                     (rp-evlt-lst lst (bind-bindings bindings-small a))))
     :flag rp-trans-lst)
   :hints (("Goal"
            :expand (ALL-VARS-BOUND-P NIL BINDINGS-SMALL)
            :in-theory (e/d (rp-evl-of-fncall-args
                             rp-trans
                             ALL-VARS-BOUND-P
                             ALL-VARS-BOUND-LST-P)
                            (pp-binds-p))))))

(local
 (encapsulate
   nil
   (local
    (defthm measure-lemma-1
      (IMPLIES (AND (CONSP (EX-FROM-RP TERM))
                    (CONSP (CDR TERM))
                    (CONSP (CDDR TERM)))
               (< (CONS-COUNT (CADDR (EX-FROM-RP TERM)))
                  (CONS-COUNT TERM)))
      :hints (("Goal"
               :in-theory (e/d (cons-count is-rp ex-from-rp) ())))))

   (local
    (defthm has-bitp-rp-of-ex-from-rp
      (NOT (HAS-BITP-RP (EX-FROM-RP TERM)))
      :hints (("Goal"
               :in-theory (e/d (is-rp has-bitp-rp) ())))))

   (local
    (defthm pp-term-p-of-ex-from-rp-3
      (implies (pp-term-p (ex-from-rp term))
               (pp-term-p term))
      :hints (("Goal"
               :in-theory (e/d (pp-term-p
                                )
                               ())))))

   (local
    (defun pp-termp-of-rp-trans-induct (term)
      (declare (xargs :measure (cons-count term)
                      :hints (("Goal"
                               :in-theory (e/d (measure-lemmas) ())))))
      (b* ((ORIG TERM) (TERM (EX-FROM-RP TERM)))
        (cond ((atom term)
               t)
              ((quotep term)
               t)
              ((AND (EQUAL (CAR orig) 'FALIST)
                    (CONSP (CDR orig))
                    (CONSP (CDDR orig)))
               (pp-termp-of-rp-trans-induct (caddr orig)))
              ((AND (EQUAL (CAR term) 'FALIST)
                    (CONSP (CDR term))
                    (CONSP (CDDR term)))
               (pp-termp-of-rp-trans-induct (caddr term)))
              ((AND (EQUAL (CAR orig) 'list))
               t)
              ((AND (EQUAL (CAR term) 'list))
               t)
              ((OR (BINARY-AND-P TERM)
                   (BINARY-OR-P TERM)
                   (BINARY-XOR-P TERM))
               (list (pp-termp-of-rp-trans-induct (cadr term))
                     (pp-termp-of-rp-trans-induct (caddr term))))
              ((BINARY-?-P TERM)
               (list (pp-termp-of-rp-trans-induct (cadr term))
                     (pp-termp-of-rp-trans-induct (caddr term))
                     (pp-termp-of-rp-trans-induct (cadddr term))))
              ((BINARY-not-P TERM)
               (pp-termp-of-rp-trans-induct (cadr term)))
              ((pp-p TERM)
               (pp-termp-of-rp-trans-induct (cadr term)))
              ((OR (BIT-OF-P TERM)
                   (HAS-BITP-RP ORIG)
                   (BIT-FIX-P TERM)
                   (EQUAL TERM ''1)
                   (EQUAL TERM ''0))
               T)

              (t nil)))))

   (local
    (defthm pp-termp-of-rp-trans-lemma
      (implies (PP-P (EX-FROM-RP TERM))
               (pp-p (EX-FROM-RP (RP-TRANS TERM))))
      :rule-classes (:rewrite :forward-chaining)
      :hints (("Goal"
               :in-theory (e/d (is-rp ex-from-rp pp-p rp-trans) ())))))

   (local
    (defthm pp-termp-of-rp-trans-lemma2
      (and (implies (bit-of-p (EX-FROM-RP TERM))
                    (bit-of-p (EX-FROM-RP (RP-TRANS TERM))))
           (implies (bit-fix-p (EX-FROM-RP TERM))
                    (bit-fix-p (EX-FROM-RP (RP-TRANS TERM)))))
      :rule-classes :rewrite
      :hints (("Goal"
               :in-theory (e/d (bit-fix-p bit-of-p is-rp ex-from-rp pp-p rp-trans)
                               ())))))
   (local
    (defthm pp-p-implies-not-others
      (implies (pp-p term)
               (and (not (binary-and-p term))
                    (not (binary-xor-p term))
                    (not (binary-or-p term))
                    (not (binary-?-p term))
                    (not (binary-not-p term))))
      :rule-classes (:rewrite :forward-chaining)))

   (local
    (defthm bit-of-p-implies-not-others
      (implies (bit-of-p term)
               (and (not (binary-and-p term))
                    (not (binary-xor-p term))
                    (not (binary-or-p term))
                    (not (binary-?-p term))
                    (not (binary-not-p term))
                    (not (pp-p term))))
      :rule-classes (:rewrite :forward-chaining)))

   (local
    (defthm bit-fix-p-implies-not-others
      (implies (bit-fix-p term)
               (and (not (binary-and-p term))
                    (not (binary-xor-p term))
                    (not (binary-or-p term))
                    (not (binary-?-p term))
                    (not (binary-not-p term))
                    (not (pp-p term))))
      :rule-classes (:rewrite :forward-chaining)))

   (local
    (defthm dummy-has-bit-rp-lemma
      (implies (HAS-BITP-RP TERM)
               (HAS-BITP-RP (rp-trans term)))
      :rule-classes (:rewrite :forward-chaining)
      :hints (("Goal"
               :in-theory (e/d (has-bitp-rp rp-trans is-rp) ())))))

   (local
    (defthm dummy-quote-ex-from-rp-lemma
      (implies (NOT (EQUAL (CAR (EX-FROM-RP TERM)) 'QUOTE))
               (not (EQUAL (CAR TERM) 'QUOTE)))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :in-theory (e/d (EX-FROM-RP is-rp) ())))))

   (local
    (defun is-falist-loose (term)
      (and (EQUAL (CAR term) 'faLIST)
           (CONSP (CDR term))
           (CONSP (CDDR term)))))

   (local
    (defthmd ex-from-rp-of-rp-trans
      (implies (syntaxp (or (atom term)
                            (not (equal (car term) 'ex-from-rp))))
               (equal (ex-from-rp (rp-trans term))
                      (ex-from-rp (rp-trans (ex-from-rp term)))))
      :hints (("Goal"
               :in-theory (e/d (rp-trans ex-from-rp is-rp) ())))))

   (local
    (defthmd ex-from-rp-of-rp-trans-when-car-is-list
      (implies (equal (car (ex-from-rp term)) 'list)
               (equal (ex-from-rp (rp-trans term))
                      (ex-from-rp (trans-list (RP-TRANS-LST (cdr (ex-from-rp term)))))))
      :hints (("Goal"
               :use ((:instance ex-from-rp-of-rp-trans))
               :in-theory (e/d (rp-trans)
                               ())))))

   (local
    (defthmd ex-from-rp-of-rp-trans-when-car-is-falist
      (implies (is-falist-loose (ex-from-rp term))
               (equal (ex-from-rp (rp-trans term))
                      (ex-from-rp (rp-trans (caddr (ex-from-rp term))))))
      :hints (("Goal"
               :use ((:instance ex-from-rp-of-rp-trans))
               :in-theory (e/d (rp-trans)
                               ())))))

   (local
    (defthmd ex-from-rp-of-rp-trans-when-car-is-falist-2
      (implies (and (equal (car term) 'falist)
                    (rp-termp term))
               (or (equal (car (caddr term)) 'cons)
                   (equal (car (caddr term)) 'quote)
                   (equal (caddr term) ''nil)))
      :hints (("Goal"
               :expand ((FALIST-CONSISTENT-AUX (CADR (CADR TERM))
                                               (CADDR TERM)))
               :in-theory (e/d (FALIST-CONSISTENT
                                FALIST-CONSISTENT-AUX)
                               ())))))

   (local
    (defthmd ex-from-rp-of-rp-trans-when-car-is-falist-3
      (implies (and (equal (car term) 'falist)
                    (rp-termp term)
                    (case-split (equal (car (caddr term)) 'cons)))
               (equal (EX-FROM-RP (RP-TRANS (caddr term)))
                      (cons 'cons
                            (rp-trans-lst (cdr (caddr term))))))

      :hints (("Goal"
               :use ((:instance ex-from-rp-of-rp-trans-when-car-is-falist-2))
               :in-theory (e/d ()
                               (rp-termp))))))

   (local
    (defthmd ex-from-rp-of-rp-trans-when-car-is-falist-4
      (implies (and (equal (car term) 'falist)
                    (rp-termp term)
                    (not (equal (car (caddr term)) 'cons))
                    (case-split (equal (caddr term) ''nil)))
               (equal (EX-FROM-RP (RP-TRANS (caddr term)))
                      ''nil))

      :hints (("Goal"
               :use ((:instance ex-from-rp-of-rp-trans-when-car-is-falist-2))
               :in-theory (e/d (rp-trans)
                               ())))))

   (local
    (defthmd ex-from-rp-of-rp-trans-when-car-is-falist-5
      (implies (and (equal (car term) 'falist)
                    (rp-termp term)
                    (not (equal (car (caddr term)) 'cons))
                    (not (equal (caddr term) ''nil)))
               (equal (EX-FROM-RP (RP-TRANS (caddr term)))
                      (cons 'quote (cdr (caddr term)))))

      :hints (("Goal"
               :use ((:instance ex-from-rp-of-rp-trans-when-car-is-falist-2))
               :in-theory (e/d (rp-trans)
                               ())))))

   (local
    (defthmd ex-from-rp-of-rp-trans-2-lemma
      (implies (and (Not (equal (car term) 'list))
                    (Not (equal (car term) 'quote))
                    (Not (equal (car term) 'falist))
                    (rp-termp term))
               (equal (is-rp (rp-trans term))
                      (is-rp term)))
      :hints (("Goal"
               :do-not-induct t
               :expand ((rp-trans term)
                        (RP-TRANS (CADR TERM))
                        (RP-TRANS-LST (CDR TERM)))
               :in-theory (e/d (is-rp rp-termp) ())))))

   (local
    (defthmd ex-from-rp-of-rp-trans-2
      (implies (and
                (not (EQUAL (CAR (EX-FROM-RP TERM)) 'LIST))
                (not (EQUAL (CAR (EX-FROM-RP TERM)) 'quote))
                (not (is-falist-loose (EX-FROM-RP TERM)))
                (rp-termp term))
               (equal (ex-from-rp (rp-trans (ex-from-rp term)))
                      (rp-trans (ex-from-rp term))
                      ))
      :hints (("Goal"

               :do-not-induct t
               :expand ((RP-TRANS TERM)
                        (RP-TRANS-LST (CDR (EX-FROM-RP TERM)))
                        (RP-TRANS (EX-FROM-RP TERM))
                        (IS-RP (LIST (CAR TERM)))
                        (RP-TRANS-LST (CDR TERM))
                        (IS-RP (LIST* (CAR (EX-FROM-RP TERM))
                                      (RP-TRANS (CADR (EX-FROM-RP TERM)))
                                      (RP-TRANS-LST (CDDR (EX-FROM-RP TERM))))))
               :in-theory (e/d (is-rp rp-trans ex-from-rp-of-rp-trans-2-lemma)
                               ())))))

   (local
    (defthmd ex-from-rp-of-rp-trans-3
      (implies (and
                (not (EQUAL (CAR (EX-FROM-RP TERM)) 'LIST))
                (not (EQUAL (CAR (EX-FROM-RP TERM)) 'quote))
                (not (is-falist-loose (EX-FROM-RP TERM)))
                (rp-termp term))
               (equal (ex-from-rp (rp-trans term))
                      (rp-trans (ex-from-rp term))))
      :hints (("Goal"
               :in-theory (e/d (ex-from-rp-of-rp-trans
                                ex-from-rp-of-rp-trans-2)
                               ())))))

   (local
    (defthm binary-and-p-lemma
      (implies (and (true-listp lst)
                    (true-listp term)
                    (equal (len (cdr term)) (len lst)))
               (and (equal (binary-and-p (cons (car term) lst))
                           (binary-and-p term))))

      :hints (("Goal"
               :do-not-induct t
               :expand ((LEN (CDDDR TERM))
                        (LEN (CDDR TERM))
                        (LEN (CDDR LST))
                        (LEN (CDR LST))
                        (LEN LST)
                        (LEN (CDR TERM)))
               :in-theory (e/d (BINARY-AND-P) ())))))

   (local
    (defthm len-of-rp-trans-lst
      (equal (len (rp-trans-lst lst))
             (len lst))
      :hints (("Goal"
               :induct (len lst)
               :in-theory (e/d () ())))))

   (local
    (defthm ex-from-rp-of-quoted
      (implies (not (equal fn 'rp))
               (equal (ex-from-rp (cons fn rest))
                      (cons fn rest)))
      :hints (("Goal"
               :in-theory (e/d (ex-from-rp is-rp) ())))))

   (local
    (defthm cdr-of-rp-trans-lst
      (equal (cdr (rp-trans-lst lst))
             (rp-trans-lst (cdr lst)))
      ))

   (progn
     (local
      (defthm BIT-FIX-P-of-rp-trans
        (implies (and (not (EQUAL (CAR TERM) 'LIST))
                      (not (is-falist-loose term))
                      (not (EQUAL (CAR TERM) 'quote))
                      (rp-termp term))
                 (equal (bit-fix-p (rp-trans term))
                        (bit-fix-p term)))
        :hints (("Goal"
                 :expand ((rp-trans term)
                          (RP-TERM-LISTP (CDR TERM))
                          (RP-TERMP TERM)
                          (RP-TRANS-LST (CDDR TERM)))
                 :in-theory (e/d (bit-fix-p) ())))))

     (local
      (defthm PP-P-P-of-rp-trans
        (implies (and (not (EQUAL (CAR TERM) 'LIST))
                      (not (is-falist-loose term))
                      (not (EQUAL (CAR TERM) 'quote))
                      (rp-termp term))
                 (equal (pp-p (rp-trans term))
                        (pp-p term)))
        :hints (("Goal"
                 :expand ((rp-trans term)
                          (RP-TERM-LISTP (CDR TERM))
                          (RP-TERMP TERM)
                          (RP-TRANS-LST (CDDR TERM)))
                 :in-theory (e/d (pp-p) ())))))

     (local
      (defthm BINARY-?-P-P-of-rp-trans
        (implies (and (not (EQUAL (CAR TERM) 'LIST))
                      (not (is-falist-loose term))
                      (not (EQUAL (CAR TERM) 'quote))
                      (rp-termp term))
                 (equal (binary-?-p (rp-trans term))
                        (binary-?-p term)))
        :hints (("Goal"
                 :expand ((rp-trans term)
                          (RP-TERM-LISTP (CDR TERM))
                          (RP-TERMP TERM)
                          (RP-TRANS-LST (CDDR TERM))
                          (RP-TRANS-LST (CDDDDR TERM)))
                 :in-theory (e/d (binary-?-p) ())))))

     (local
      (defthm BINARY-and-P-of-rp-trans
        (implies (and (not (EQUAL (CAR TERM) 'LIST))
                      (not (is-falist-loose term))
                      (not (EQUAL (CAR TERM) 'quote))
                      (rp-termp term))
                 (equal (binary-and-p (rp-trans term))
                        (binary-and-p term)))
        :hints (("Goal"
                 :expand ((rp-trans term)
                          (RP-TERM-LISTP (CDR TERM))
                          (RP-TERMP TERM)
                          (RP-TRANS-LST (CDDDR TERM))
                          (RP-TRANS-LST (CDDR TERM))
                          (RP-TRANS-LST (CDDDDR TERM)))
                 :in-theory (e/d (binary-and-p) ())))))

     (local
      (defthm BINARY-or-P-of-rp-trans
        (implies (and (not (EQUAL (CAR TERM) 'LIST))
                      (not (is-falist-loose term))
                      (not (EQUAL (CAR TERM) 'quote))
                      (rp-termp term))
                 (equal (binary-or-p (rp-trans term))
                        (binary-or-p term)))
        :hints (("Goal"
                 :expand ((rp-trans term)
                          (RP-TERM-LISTP (CDR TERM))
                          (RP-TERMP TERM)
                          (RP-TRANS-LST (CDDDR TERM))
                          (RP-TRANS-LST (CDDR TERM))
                          (RP-TRANS-LST (CDDDDR TERM)))
                 :in-theory (e/d (binary-or-p) ())))))

     (local
      (defthm BINARY-xor-P-of-rp-trans
        (implies (and (not (EQUAL (CAR TERM) 'LIST))
                      (not (is-falist-loose term))
                      (not (EQUAL (CAR TERM) 'quote))
                      (rp-termp term))
                 (equal (binary-xor-p (rp-trans term))
                        (binary-xor-p term)))
        :hints (("Goal"
                 :expand ((rp-trans term)
                          (RP-TERM-LISTP (CDR TERM))
                          (RP-TERMP TERM)
                          (RP-TRANS-LST (CDDDR TERM))
                          (RP-TRANS-LST (CDDR TERM))
                          (RP-TRANS-LST (CDDDDR TERM)))
                 :in-theory (e/d (binary-xor-p) ())))))

     (local
      (defthm BINARY-NOT-P-of-rp-trans
        (implies (and (not (EQUAL (CAR TERM) 'LIST))
                      (not (is-falist-loose term))
                      (not (EQUAL (CAR TERM) 'quote))
                      (rp-termp term))
                 (equal (binary-not-p (rp-trans term))
                        (binary-not-p term)))
        :hints (("Goal"
                 :expand ((rp-trans term)
                          (RP-TERM-LISTP (CDR TERM))
                          (RP-TERMP TERM)
                          (RP-TRANS-LST (CDDR TERM)))
                 :in-theory (e/d (binary-not-p) ()))))))

   (local
    (defthm rp-trans-when-known-fncs
      (and (implies (or (BIT-OF-P term)
                        (binary-fnc-p term)
                        (pp-p term))
                    (equal (RP-TRANS term)
                           (cons (car term)
                                 (rp-trans-lst (cdr term))))))
      :hints (("Goal"
               :in-theory (e/d (binary-fnc-p
                                rp-trans) ())))))

   (local
    (defthm ex-from-rp-of-TRANS-LIST
      (equal (ex-from-rp (trans-list lst))
             (trans-list lst))))

   (local
    (defthm known-function-of-trans-list
      (and (not (binary-?-p (trans-list lst)))
           (not (binary-or-p (trans-list lst)))
           (not (binary-not-p (trans-list lst)))
           (not (bit-of-p (trans-list lst)))
           (not (binary-xor-p (trans-list lst)))
           (not (binary-and-p (trans-list lst)))
           (not (pp-p (trans-list lst))))
      :hints (("Goal"
               :in-theory (e/d (binary-fnc-p
                                binary-or-p
                                BINARY-XOR-P
                                BINARY-AND-P
                                trans-list)
                               ())))))

   (local
    (defthm rp-trans-when-falist
      (implies (is-falist-loose term)
               (equal (rp-trans term)
                      (rp-trans (caddr term))))
      :hints (("Goal"
               :in-theory (e/d (rp-trans) ())))))

   (local
    (defthm has-bitp-rp-when-falist
      (implies (HAS-BITP-RP TERM)
               (and (not (EQUAL (CAR TERM) 'FALIST))
                    (not (EQUAL (CAR TERM) 'list))
                    (not (EQUAL (CAR TERM) 'quote))))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :in-theory (e/d (has-bitp-rp is-rp)
                               ())))))

   (local
    (defthm ex-from-rp-of-rp-trans-when-quoted-1
      (implies (equal (ex-from-rp term) ''1)
               (equal (ex-from-rp (rp-trans term))
                      ''1))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :use ((:instance
                      ex-from-rp-of-rp-trans))
               :in-theory (e/d (rp-trans ex-from-rp is-rp) ())))))

   (local
    (defthm ex-from-rp-of-rp-trans-when-quoted-0
      (implies (equal (ex-from-rp term) ''0)
               (equal (ex-from-rp (rp-trans term))
                      ''0))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :use ((:instance
                      ex-from-rp-of-rp-trans))
               :in-theory (e/d (rp-trans ex-from-rp is-rp) ())))))

   (local
    (defthm ex-from-rp-of-rp-trans-when-quoted-general
      (implies (equal (car (ex-from-rp term)) 'quote)
               (equal (ex-from-rp (rp-trans term))
                      (ex-from-rp term)))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :expand (RP-TRANS (EX-FROM-RP TERM))
               :in-theory (e/d (ex-from-rp-of-rp-trans)
                               (ex-from-rp))))))

   (defthm pp-termp-of-rp-trans
     (implies (and (pp-term-p term)
                   (rp-termp term))
              (pp-term-p (rp-trans term)))
     :hints ( #|("subgoal *1/4"
             :use ((:instance ex-from-rp-of-rp-trans-when-car-is-falist-2 ;
             (term (EX-FROM-RP TERM)))))|#
             ("Goal"
              :induct (pp-termp-of-rp-trans-induct term)
              ;;:induct (pp-term-p term)
              :expand ((PP-TERM-P TERM :STRICT NIL)
                       (RP-TRANS-LST (CDR (EX-FROM-RP TERM)))
                       (RP-TRANS-LST (CDDR (EX-FROM-RP TERM)))
                       (RP-TRANS-LST (CDDDR (EX-FROM-RP TERM)))
                       (:free (x y) (BINARY-?-P (CONS x y)))
                       (:free (x y) (BINARY-not-P (CONS x y)))
                       (:free (x y) (BINARY-and-P (CONS x y)))
                       (:free (x y) (BINARY-or-P (CONS x y)))
                       (:free (x y) (BINARY-xor-P (CONS x y)))
                       (PP-TERM-P (RP-TRANS TERM) :STRICT NIL))
              :in-theory (e/d (ex-from-rp-of-rp-trans-when-car-is-list
                               binary-fnc-p
                               pp-term-p
                               ex-from-rp-of-rp-trans-3
                               ;; ex-from-rp-of-rp-trans-when-quoted
                               ex-from-rp-of-rp-trans-when-car-is-falist
                               ex-from-rp-of-rp-trans-when-car-is-falist-3
                               ex-from-rp-of-rp-trans-when-car-is-falist-4
                               ex-from-rp-of-rp-trans-when-car-is-falist-5
                               )
                              ((:REWRITE EX-FROM-RP-OF-BINARY-FNC)
                               (:DEFINITION BINARY-FNC-P$INLINE)
                               (:REWRITE PP-TERM-P-OF-EX-FROM-RP)
                               PP-TERMP-OF-RP-TRANS-LEMMA2
                               rp-trans-lst
                               ex-from-rp)))))))

(local
 (defthm len-of-RP-TRANS-BINDINGS
   (equal (len (rp-trans-bindings bindings))
          (len bindings))))

(local
 (defthm pp-binds-p-of-rp-trans-bindings
   (implies (pp-binds-p bindings)
            (pp-binds-p (rp-trans-bindings bindings)))
   :hints (("goal"
            :induct (pp-binds-p bindings)
            :do-not-induct t
            :in-theory (e/d (pp-binds-p

                             binary-and-p
                             PP-ENTRY->TMP-VAR
                             rp-trans-bindings
                             PP-ENTRY->ORIG-TERM)
                            ())))))

(local
 (defthm ENDS-WITH-P-of-RP-TRANS-BINDINGS
   (implies (and (ends-with-p lst1 lst2))
            (ends-with-p (rp-trans-bindings lst1) (rp-trans-bindings lst2)))
   :hints (("Goal"
            :in-theory (e/d (RP-TRANS-BINDINGS) ())))))



(local 
 (defthm rp-evlt-of-pp-term-bind-dummy-lemma
   (implies (and (MV-NTH 3
                         (PP-TERM-BIND (CADR (EX-FROM-RP TERM))
                                       PP-BINDS (LEN PP-BINDS)))
                 (MV-NTH 3
                         (PP-TERM-BIND (CADDR (EX-FROM-RP TERM))
                                       (MV-NTH 1
                                               (PP-TERM-BIND (CADR (EX-FROM-RP TERM))
                                                             PP-BINDS (LEN PP-BINDS)))
                                       (MV-NTH 2
                                               (PP-TERM-BIND (CADR (EX-FROM-RP TERM))
                                                             PP-BINDS (LEN
                                                                       PP-BINDS)))))
                 (pp-binds-p pp-binds)

                 ;;(rp-termp term)
                 ;;(pp-term-p term)

                 (rp-termp (CADR (EX-FROM-RP TERM)))
                 (rp-termp (CAdDR (EX-FROM-RP TERM)))
                 (rp-termp (CAddDR (EX-FROM-RP TERM)))

                 (pp-term-p (CADR (EX-FROM-RP TERM)))
                 (pp-term-p (CAdDR (EX-FROM-RP TERM)))
                 (pp-term-p (CAddDR (EX-FROM-RP TERM)))
                 
                 )
            (ALL-VARS-BOUND-P
             (MV-NTH 0
                     (PP-TERM-BIND (CADR (EX-FROM-RP TERM))
                                   PP-BINDS (LEN PP-BINDS)))
             (MV-NTH 1
                     (PP-TERM-BIND (CADDR (EX-FROM-RP TERM))
                                   (MV-NTH 1
                                           (PP-TERM-BIND (CADR (EX-FROM-RP TERM))
                                                         PP-BINDS (LEN PP-BINDS)))
                                   (MV-NTH 2
                                           (PP-TERM-BIND (CADR (EX-FROM-RP TERM))
                                                         PP-BINDS (LEN PP-BINDS)))))))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance all-vars-bound-p-ends-with-p-lemma
                             (term (mv-nth 0
                                           (pp-term-bind (cadr (ex-from-rp term))
                                                         pp-binds (len
                                                                   pp-binds))))
                             (bindings-small (mv-nth 1
                                                     (pp-term-bind (cadr (ex-from-rp term))
                                                                   pp-binds
                                                                   (len pp-binds))))
                             (bindings (mv-nth 1
                                               (pp-term-bind (caddr (ex-from-rp term))
                                                             (mv-nth 1
                                                                     (pp-term-bind (cadr (ex-from-rp term))
                                                                                   pp-binds (len pp-binds)))
                                                             (mv-nth 2
                                                                     (pp-term-bind (cadr (ex-from-rp term))
                                                                                   pp-binds (len pp-binds))))))))
            :in-theory (e/d ()
                            (ex-from-rp))))))

(local
 (defret rp-evlt-of-pp-term-bind
   (implies (and valid
                 (pp-binds-p pp-binds)
                 (rp-termp term)
                 (pp-term-p term)
                 (equal (len pp-binds) index)
                 (valid-sc term a)
                 (valid-sc-bindings pp-binds a)

                 (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts))
            (equal (rp-evlt res
                            (bind-bindings (rp-trans-bindings res-pp-binds) a))
                   (rp-evlt term a)))

   :fn pp-term-bind
   :otf-flg t
   :hints (("subgoal *1/2"
            :use ((:instance rp-evlt-of-big-pp-binds-to-small-binds
                             (term (mv-nth 0
                                           (pp-term-bind (cadr (ex-from-rp term))
                                                         pp-binds (len pp-binds))))
                             (bindings (rp-trans-bindings
                                        (mv-nth
                                         1
                                         (pp-term-bind (caddr (ex-from-rp term))
                                                       (mv-nth 1
                                                               (pp-term-bind (cadr (ex-from-rp term))
                                                                             pp-binds (len pp-binds)))
                                                       (mv-nth 2
                                                               (pp-term-bind (cadr (ex-from-rp term))
                                                                             pp-binds
                                                                             (len pp-binds)))))))
                             (bindings-small (rp-trans-bindings (mv-nth 1
                                                                        (pp-term-bind (cadr (ex-from-rp term))
                                                                                      pp-binds
                                                                                      (len pp-binds))))))))

           ("subgoal *1/1"
            :use ((:instance rp-evlt-of-big-pp-binds-to-small-binds
                             (term (mv-nth 0
                                           (pp-term-bind (cadr (ex-from-rp term))
                                                         pp-binds (len pp-binds))))
                             (bindings (rp-trans-bindings
                                        (mv-nth
                                         1
                                         (pp-term-bind (caddr (ex-from-rp term))
                                                       (mv-nth 1
                                                               (pp-term-bind (cadr (ex-from-rp term))
                                                                             pp-binds (len pp-binds)))
                                                       (mv-nth 2
                                                               (pp-term-bind (cadr (ex-from-rp term))
                                                                             pp-binds
                                                                             (len pp-binds)))))))
                             (bindings-small (rp-trans-bindings (mv-nth 1
                                                                        (pp-term-bind (cadr (ex-from-rp term))
                                                                                      pp-binds
                                                                                      (len
                                                                                       pp-binds))))))
                  (:instance rp-evlt-of-big-pp-binds-to-small-binds
                             (term (MV-NTH 0
                                           (PP-TERM-BIND (CADR (EX-FROM-RP TERM))
                                                         PP-BINDS (LEN PP-BINDS))))
                             (bindings (RP-TRANS-BINDINGS
                                        (MV-NTH
                                         1
                                         (PP-TERM-BIND
                                          (CADDDR (EX-FROM-RP TERM))
                                          (MV-NTH
                                           1
                                           (PP-TERM-BIND (CADDR (EX-FROM-RP TERM))
                                                         (MV-NTH 1
                                                                 (PP-TERM-BIND (CADR (EX-FROM-RP TERM))
                                                                               PP-BINDS (LEN PP-BINDS)))
                                                         (MV-NTH 2
                                                                 (PP-TERM-BIND (CADR (EX-FROM-RP TERM))
                                                                               PP-BINDS (LEN PP-BINDS)))))
                                          (MV-NTH
                                           2
                                           (PP-TERM-BIND (CADDR (EX-FROM-RP TERM))
                                                         (MV-NTH 1
                                                                 (PP-TERM-BIND (CADR (EX-FROM-RP TERM))
                                                                               PP-BINDS (LEN PP-BINDS)))
                                                         (MV-NTH 2
                                                                 (PP-TERM-BIND (CADR (EX-FROM-RP TERM))
                                                                               PP-BINDS (LEN PP-BINDS)))))))))
                             (bindings-small (rp-trans-bindings (mv-nth 1
                                                                        (pp-term-bind (caddr (ex-from-rp term))
                                                                                      (mv-nth 1
                                                                                              (pp-term-bind (cadr (ex-from-rp term))
                                                                                                            pp-binds (len pp-binds)))
                                                                                      (mv-nth 2
                                                                                              (pp-term-bind (cadr (ex-from-rp term))
                                                                                                            pp-binds (len
                                                                                                                      pp-binds))))))))
                  (:instance rp-evlt-of-big-pp-binds-to-small-binds
                             (term (MV-NTH 0
                                           (PP-TERM-BIND (CADDR (EX-FROM-RP TERM))
                                                         (MV-NTH 1
                                                                 (PP-TERM-BIND (CADR (EX-FROM-RP TERM))
                                                                               PP-BINDS (LEN PP-BINDS)))
                                                         (MV-NTH 2
                                                                 (PP-TERM-BIND (CADR (EX-FROM-RP TERM))
                                                                               PP-BINDS (LEN PP-BINDS))))))
                             (bindings (RP-TRANS-BINDINGS
                                        (mv-nth
                                         1
                                         (pp-term-bind
                                          (cadddr (ex-from-rp term))
                                          (mv-nth 1
                                                  (pp-term-bind (caddr (ex-from-rp term))
                                                                (mv-nth 1
                                                                        (pp-term-bind (cadr (ex-from-rp term))
                                                                                      pp-binds (len pp-binds)))
                                                                (mv-nth 2
                                                                        (pp-term-bind (cadr (ex-from-rp term))
                                                                                      pp-binds (len pp-binds)))))
                                          (mv-nth
                                           2
                                           (pp-term-bind (caddr (ex-from-rp term))
                                                         (mv-nth 1
                                                                 (pp-term-bind (cadr (ex-from-rp term))
                                                                               pp-binds (len pp-binds)))
                                                         (mv-nth 2
                                                                 (pp-term-bind (cadr (ex-from-rp term))
                                                                               pp-binds (len pp-binds)))))))))
                             (bindings-small (rp-trans-bindings
                                              (mv-nth 1
                                                      (pp-term-bind (caddr (ex-from-rp term))
                                                                    (mv-nth 1
                                                                            (pp-term-bind (cadr (ex-from-rp term))
                                                                                          pp-binds (len pp-binds)))
                                                                    (mv-nth 2
                                                                            (pp-term-bind (cadr (ex-from-rp term))
                                                                                          pp-binds (len pp-binds))))))))))

           ("goal"
            :in-theory (e/d* (regular-eval-lemmas
                              implode-equivalance-with-string
                              make-pp-entry
                              pp-term-bind)
                             ((:DEFINITION EQ)
                              (:REWRITE
                               ACL2::INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY)
                              ;;;;(:REWRITE DUMMY-LEMMA-STRINGS)
                              (:REWRITE DEFAULT-+-2)
                              (:REWRITE ACL2::AND*-REM-FIRST)
                              (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP)
                              ;;(:REWRITE IMPLODE-EQUIVALANCE-WITH-STRING)
                              ;;(:REWRITE IMPLODE-EQUIVALANCE-WITH-STRING)
                              (:META BINARY-OR**/AND**-GUARD-META-CORRECT)

                              EX-FROM-RP
                              VALID-SC
                              EX-FROM-RP-OF-BINARY-FNC
                              (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)))))))

;;; MAIN LEMMA

(defret pp-flatten-with-binds-correct
  (implies (and (mult-formula-checks state)
                (pp-term-p term)
                (booleanp signed)
                (valid-sc term a)
                (rp-evl-meta-extract-global-facts))
           (equal (sum-list (rp-evlt-lst pp-lst a))
                  (if signed
                      (-- (rp-evlt term a))
                    (rp-evlt term a))))
  :fn pp-flatten-with-binds
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (pp-flatten-with-binds
                             regular-eval-lemmas)
                            ()))))

(local
 (defret valid-sc-PP-APPLY-BINDINGS-AND-ARG-LST
   (implies (and ;;(not (include-fnc-subterms and-arg-lst 'rp))
             (valid-sc-bindings pp-binds a))
            (valid-sc-subterms res a))
   :fn pp-apply-bindings-and-arg-lst
   :hints (("Goal"
            :in-theory (e/d (PP-ENTRY->ORIG-TERM
                             RP-ASSOC-W/-TMP-VAR
                             PP-APPLY-BINDINGS-AND-ARG-LST)
                            ())))))

(local
 (defthm VALID-SC-of-CREATE-AND-LIST-INSTANCE
   (implies (valid-sc-subterms lst a)
            (valid-sc (CREATE-AND-LIST-INSTANCE lst) a))
   :hints (("Goal"
            :in-theory (e/d (valid-sc is-rp is-if CREATE-AND-LIST-INSTANCE) ())))))

(local
 (defret valid-sc-PP-APPLY-BINDINGS
   (implies (and ;;(not (include-fnc-subterms pp-lst 'rp))
             (valid-sc-bindings pp-binds a)
             valid)
            (valid-sc-subterms res a))
   :fn pp-apply-bindings
   :hints (("Goal"
            :in-theory (e/d (PP-ENTRY->ORIG-TERM
                             RP-ASSOC-W/-TMP-VAR
                             PP-APPLY-BINDINGS)
                            ())))))

(defret pp-flatten-with-binds-valid-sc
  (implies (and (mult-formula-checks state)
                (pp-term-p term)
                (booleanp signed)
                (valid-sc term a)
                (rp-evl-meta-extract-global-facts))
           (valid-sc-subterms pp-lst a))
  :fn pp-flatten-with-binds
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (pp-flatten-with-binds
                             regular-eval-lemmas)
                            ()))))
