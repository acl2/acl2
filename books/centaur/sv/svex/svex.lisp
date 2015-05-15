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

(in-package "SV")
(include-book "std/util/defines" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
(include-book "tools/flag" :dir :system)
(include-book "centaur/misc/universal-equiv" :dir :system)
(include-book "centaur/misc/arith-equiv-defs" :dir :system)
(include-book "tools/easy-simplify" :dir :system)
(include-book "std/lists/repeat" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(local (include-book "std/lists/acl2-count" :dir :system))
(local (include-book "centaur/misc/arith-equivs" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/append" :dir :system))

(defxdoc svex.lisp :parents (svex))
(local (xdoc::set-default-parents svex.lisp))

(defsection 4vec
  :parents (sv)
  :short "A 4-valued bit vector representation, used by the SVEX package."
  :long "<p>A 4vec represents a vector of 4-valued bits.  Each bit can be 1, 0,
X, or Z.  The concrete representation is either an integer (for special cases
where every bit is 1 or 0) or a pair of integers, upper and lower.  Each
4-valued bit is determined by the corresponding positions in the two integers.
If two corresponding bits are equal, then the resulting bit is that value (1 or
0).  If the upper bit is 1 and the lower 0, then the resulting value is X, and
if the upper bit is 0 and the lower 1, then the resulting value is Z.</p>

<p>Examples:</p>
<table>
<tr><th>Representation</th><th>Meaning (LSB first)</th></tr>
<tr><td>6</td>        <td>0,1,1,0,0,0,...</td></tr>
<tr><td>-13</td>      <td>1,1,0,0,1,1,...</td></tr>
<tr><td>(6 . -13)</td><td>Z,1,X,0,Z,Z,...</td></tr>
</table>"
  (define 4vec-p (x)
    (or (integerp x)
        (and (consp x)
             (integerp (car x))
             (integerp (cdr x))
             (not (equal (car x) (cdr x))))))

  (local (in-theory (enable 4vec-p)))

  (define 4vec ((upper integerp)
                (lower integerp))
    :parents nil
    :returns (x 4vec-p)
    (b* ((upper (lifix upper))
         (lower (lifix lower)))
      (if (eql upper lower)
          upper
        (cons upper lower))))

  (local (in-theory (enable 4vec)))

  (defconst *4vec-x* (4vec -1 0))
  (defconst *4vec-z* (4vec 0 -1))
  (defmacro 4vec-x () `',*4vec-x*)
  (defmacro 4vec-z () `',*4vec-z*)

  (defconst *4vec-1x* (4vec 1 0))
  (defconst *4vec-1z* (4vec 0 1))
  (defmacro 4vec-1x () `',*4vec-1x*)
  (defmacro 4vec-1z () `',*4vec-1z*)

  (define 4vec-fix ((x 4vec-p))
    :parents (4vec)
    :short "Fix an arbitrary object to a 4vec-p.  Guard assumes already 4vec-p."
    :inline t
    :prepwork ((local (in-theory (disable (force)))))
    :returns (newx 4vec-p)
    (mbe :logic (if (consp x)
                    (4vec (ifix (car x))
                          (ifix (cdr x)))
                  (if (integerp x)
                      x
                    (4vec-x)))
         ;; (4vec (ifix (4vec->upper x))
         ;;       (ifix (4vec->lower x)))
         :exec x)
    ///
    (defthm 4vec-fix-of-4vec
      (implies (4vec-p x)
               (equal (4vec-fix x) x)))

    (fty::deffixtype 4vec :pred 4vec-p :fix 4vec-fix :equiv 4vec-equiv :define t :forward t))

  (local (in-theory (enable 4vec-fix)))

  (define 4vec->upper ((x 4vec-p))
    :returns (upper integerp
                    :rule-classes (:rewrite :type-prescription))
    (mbe :logic (if (consp x)
                    (ifix (car x))
                  (if (integerp x)
                      x
                    -1))
         :exec (if (integerp x)
                   x
                 (car x)))
    ///
    (defthm 4vec->upper-of-4vec
      (equal (4vec->upper (4vec upper lower))
             (ifix upper)))

    (defthm 4vec->upper-of-4vec-fix
      (equal (4vec->upper (4vec-fix x))
             (4vec->upper x))))

  (define 4vec->lower ((x 4vec-p))
    :returns (lower integerp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (if (consp x)
                    (ifix (cdr x))
                  (if (integerp x)
                      x
                    0))
         :exec (if (integerp x)
                   x
                 (cdr x)))
    ///
    (defthm 4vec->lower-of-4vec
      (equal (4vec->lower (4vec upper lower))
             (ifix lower)))

    (defthm 4vec->lower-of-4vec-fix
      (equal (4vec->lower (4vec-fix x))
             (4vec->lower x))))

  (local (in-theory (enable 4vec->upper 4vec->lower)))

  (defthm 4vec-of-fields
    (4vec-equiv (4vec (4vec->upper x) (4vec->lower x))
                x)
    :hints(("Goal" :in-theory (enable 4vec-fix 4vec-equiv))))

  (defthmd 4vec-fix-is-4vec-of-fields
    (equal (4vec-fix x)
           (4vec (4vec->upper x) (4vec->lower x)))
    :hints(("Goal" :in-theory (enable 4vec-fix))))

  (defthm 4vec-elim
    (implies (4vec-p x)
             (equal (4vec (4vec->upper x) (4vec->lower x))
                    x))
    :rule-classes :elim)

  (def-b*-binder 4vec
    :body
    (std::da-patbind-fn '4vec '((upper . 4vec->upper)
                                (lower . 4vec->lower))
                        args acl2::forms acl2::rest-expr))

  (defthm 4vec-equal
    (equal (equal (4vec upper lower) x)
           (and (4vec-p x)
                (equal (4vec->upper x) (ifix upper))
                (equal (4vec->lower x) (ifix lower))))
    :hints(("Goal" :in-theory (e/d (4vec-fix)))))


  (local (in-theory (enable 4vec-equiv)))

  (defcong 4vec-equiv equal (4vec->upper x) 1)
  (defcong 4vec-equiv equal (4vec->lower x) 1))


(define 2vec-p ((x 4vec-p))
  :parents (2vec)
  :inline t
  :enabled t
  :guard-hints (("goal" :in-theory (e/d (4vec-p 4vec->upper 4vec->lower 4vec-fix))))
  (mbe :logic (equal (4vec->upper x)
                     (4vec->lower x))
       :exec (integerp x))
  ///
  (defthm 4vec->lower-when-2vec-p
    (implies (2vec-p x)
             (equal (4vec->lower x)
                    (4vec->upper x))))

  (fty::deffixequiv 2vec-p))

(define 2vec ((x integerp))
  :parents (4vec)
  :short "A 2vec is a 4vec that has no X or Z bits."
  :long "<p>@('2vec') constructs a 2vec from an integer; @('2vec-p') recognizes
a 2vec; @('2vec->val') gets the integer value out of a 2vec.</p>"
  :inline t
  :guard-hints (("goal" :in-theory (enable 4vec)))
  (mbe :logic (4vec x x)
       :exec x)
  ///
  (defthm 4vec-p-of-2vec
    (4vec-p (2vec x)))

  (defthm 4vec->upper-of-2vec
    (equal (4vec->upper (2vec x))
           (ifix x)))

  (defthm 4vec->lower-of-2vec
    (equal (4vec->lower (2vec x))
           (ifix x)))

  (defthm equal-of-2vec
    (equal (equal (2vec x) y)
           (and (4vec-p y)
                (equal (4vec->upper y) (ifix x))
                (equal (4vec->lower y) (ifix x)))))

  (fty::deffixequiv 2vec))

(define 2vec->val ((x (and (4vec-p x) (2vec-p x))))
  :parents (2vec)
  :short "Extract the upper/lower value (both the same) from a 2vec."
  :inline t
  :enabled t
  :guard-hints (("goal" :in-theory (enable 4vec->upper 4vec->lower 4vec-p)))
  (mbe :logic (4vec->upper x)
       :exec x))


(defflexsum svar
  :parents (svex)
  :kind nil
  (:svar :type-name svar
   :cond t
   :shape (if (atom x)
              (or (stringp x)
                  (and (symbolp x)
                       (not (booleanp x))))
            (and (eq (car x) :var)
                 (consp (cdr x))
                 (not (and (or (stringp (cadr x))
                               (and (symbolp (cadr x))
                                    (not (booleanp (cadr x)))))
                           (eql (cddr x) 0)))))
   :fields
   ((name :acc-body (if (atom x) x (cadr x)))
    (delay :type natp :acc-body (if (atom x) 0 (cddr x))
           :default 0))
   :ctor-body (if (and (or (stringp name)
                           (and (symbolp name)
                                (not (booleanp name))))
                       (eql delay 0))
                  name
                (hons :var (hons name delay)))))



(define fnsym-p (x)
  (and (symbolp x)
       (not (eq x 'quote))
       (not (keywordp x)))
  ///
  (defthm fnsym-p-compound-recognizer
    (implies (fnsym-p x)
             (symbolp x))
    :rule-classes :compound-recognizer))

(define fnsym-fix (x)
  :returns (x fnsym-p)
  (if (fnsym-p x) x 'id)
  ///
  (defthm fnsym-fix-when-fnsym-p
    (implies (fnsym-p x)
             (equal (fnsym-fix x) x)))

  (fty::deffixtype fnsym :pred fnsym-p :fix fnsym-fix :equiv fnsym-equiv :define t :forward t))


(fty::deftypes svex
  :parents (sv)
  :prepwork ((local (defthm 4vec-not-svar-p
                      (implies (svar-p x)
                               (not (4vec-p x)))
                      :hints(("Goal" :in-theory (enable 4vec-p svar-p)))))
             (local (defthm cons-fnsym-not-svar-p
                      (implies (not (eq x :var))
                               (not (svar-p (cons x y))))
                      :hints(("Goal" :in-theory (enable fnsym-p svar-p))))))
  (fty::defflexsum svex
    (:var
     :cond (svar-p x)
     :fields ((name :acc-body x :type svar-p))
     :ctor-body name)
    (:quote
     :cond (or (atom x)
               (eq (car x) 'quote))
     :shape (or (atom x) (and (consp (cdr x))
                              (consp (cadr x))
                              (not (cddr x))))
     :fields ((val :acc-body (if (atom x) x (cadr x))
                   :type 4vec))
     :ctor-body (if (atom val) val (hons 'quote (hons val nil))))
    (:call
     :cond t
     :fields ((fn :acc-body (car x) :type fnsym)
              (args :acc-body (cdr x) :type svexlist))
     :ctor-body (hons fn args)))
  (fty::deflist svexlist :elt-type svex :true-listp t))

(memoize 'svex-p :condition '(consp x))

(defconst *svex-z* (svex-quote (4vec-z)))
(defconst *svex-x* (svex-quote (4vec-x)))
(defconst *svex-1z* (svex-quote (4vec-1z)))
(defconst *svex-1x* (svex-quote (4vec-1x)))

(defmacro svex-z () `',*svex-z*)
(defmacro svex-x () `',*svex-x*)
(defmacro svex-1z () `',*svex-1z*)
(defmacro svex-1x () `',*svex-1x*)

(defthm len-of-svexlist-fix
  (equal (len (svexlist-fix x))
         (len x)))

(defthm svex-count-of-car-weak
  (<= (svex-count (car args))
      (svexlist-count args))
  :hints (("goal" :cases ((consp args))))
  :rule-classes :linear)

(defthm svexlist-count-of-cdr-weak
  (<= (svexlist-count (cdr args))
      (svexlist-count args))
  :hints (("goal" :cases ((consp args))))
  :rule-classes :linear)



(define svex-nth ((n natp) (x svexlist-p))
  :enabled t
  :guard-debug t
  (mbe :logic (svex-fix (nth n x))
       :exec (if (< n (len x))
                 (nth n x)
               (svex-quote (4vec-x)))))

(define svex-update-nth ((n natp) (v svex-p) (x svexlist-p))
  :enabled t
  :prepwork ((local (in-theory (e/d (update-nth replicate svexlist-fix)
                                    (acl2::equal-of-append-repeat))))
             (local (include-book "arithmetic/top-with-meta" :dir :system)))
  (mbe :logic (svexlist-fix (update-nth n v x))
       :exec (if (<= n (len x))
                 (update-nth n v x)
               (append x
                       (replicate (- n (len x)) (svex-quote (4vec-x)))
                       (list v)))))


(fty::defalist svex-alist :key-type svar :val-type svex :true-listp t)



(define svex-acons ((var svar-p) (v svex-p) (a svex-alist-p))
  :prepwork ((local (in-theory (enable svex-alist-fix svex-alist-p))))
  :returns (aa svex-alist-p)
  (mbe :logic (cons (cons (svar-fix var)
                          (svex-fix v))
                    (svex-alist-fix a))
       :exec (cons (cons var v) a))
  ///
  (fty::deffixequiv svex-acons))

(define svex-lookup ((var svar-p) (a svex-alist-p))
  :prepwork ((local (in-theory (enable svex-alist-fix svex-alist-p))))
  :returns (v (iff (svex-p v) v))
  (mbe :logic (cdr (hons-assoc-equal (svar-fix var) (svex-alist-fix a)))
       :exec (cdr (assoc-equal var a)))
  ///
  (fty::deffixequiv svex-lookup)

  (defthm svex-lookup-of-nil
    (equal (svex-lookup v nil) nil))

  (defthm svex-lookup-of-svex-acons
    (equal (svex-lookup var1 (svex-acons var2 x a))
           (if (equal (svar-fix var1) (svar-fix var2))
               (svex-fix x)
             (svex-lookup var1 a)))
    :hints(("Goal" :in-theory (enable svex-acons)))))

(define svex-fastlookup ((var svar-p) (a svex-alist-p))
  :prepwork ((local (in-theory (enable svex-alist-fix svex-alist-p
                                       svex-lookup))))
  :enabled t
  (mbe :logic (svex-lookup var a)
       :exec (cdr (hons-get var a))))

(define svex-fastacons ((var svar-p) (v svex-p) (a svex-alist-p))
  :prepwork ((local (in-theory (enable svex-acons))))
  :enabled t
  (mbe :logic (svex-acons var v a)
       :exec (hons-acons var v a)))

(fty::deflist svarlist :elt-type svar :true-listp t :elementp-of-nil nil)

(define svex-alist-keys ((x svex-alist-p))
  :prepwork ((local (in-theory (enable svex-alist-p))))
  :returns (keys svarlist-p)
  (if (atom x)
      nil
    (if (consp (car x))
        (cons (mbe :logic (svar-fix (caar x)) :exec (caar x))
              (svex-alist-keys (cdr x)))
      (svex-alist-keys (cdr x))))
  ///
  (fty::deffixequiv svex-alist-keys
    :hints (("goal" :expand ((svex-alist-fix x)))))

  (defthm member-svex-alist-keys
    (iff (member k (svex-alist-keys x))
         (and (svar-p k)
              (svex-lookup k x)))
    :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix))))

  (defthm svex-alist-keys-of-svex-acons
    (equal (svex-alist-keys (svex-acons k v x))
           (cons (svar-fix k) (svex-alist-keys x)))
    :hints(("Goal" :in-theory (enable svex-acons)))))

(define svex-alist-vals ((x svex-alist-p))
  :prepwork ((local (in-theory (enable svex-alist-p))))
  :returns (vals svexlist-p)
  (if (atom x)
      nil
    (if (consp (car x))
        (cons (mbe :logic (svex-fix (cdar x)) :exec (cdar x))
              (svex-alist-vals (cdr x)))
      (svex-alist-vals (cdr x))))
  ///
  (fty::deffixequiv svex-alist-vals
    :hints (("goal" :expand ((svex-alist-fix x)))))

  (defthm member-svex-alist-vals-when-svex-lookup
    (implies (svex-lookup k x)
             (member (svex-lookup k x)
                     (svex-alist-vals x)))
    :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix))))

  (defthm svex-alist-vals-of-svex-acons
    (equal (svex-alist-vals (svex-acons k v x))
           (cons (svex-fix v) (svex-alist-vals x)))
    :hints(("Goal" :in-theory (enable svex-acons))))

  (defthm len-of-svex-alist-vals
    (equal (len (svex-alist-vals x))
           (len (svex-alist-keys x)))
    :hints(("Goal" :in-theory (enable svex-alist-keys)))))



(defalist svar-alist :key-type svar)

(defalist svar-map :key-type svar :val-type svar)

