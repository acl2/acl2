; TRUTH - integer truth table representation
; Copyright (C) 2017 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "TRUTH")

(include-book "truth")
(include-book "centaur/fty/bitstruct" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/bitops/ash-bounds" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (in-theory (disable unsigned-byte-p signed-byte-p)))
(local (std::add-default-post-define-hook :fix))


(define var-alist ((n natp) (numvars natp))
  :guard (<= n numvars)
  (if (zp n)
      nil
    (let ((n (1- n)))
      (cons (cons n (var n numvars))
            (var-alist n numvars)))))

(defun var-cases-fn (n numvars)
  (if (zp n)
      nil
    (if (eql n 1)
        `((otherwise ,(var 0 numvars)))
      (cons `(,(1- n) ,(var (1- n) numvars))
            (var-cases-fn (1- n) numvars)))))

(defmacro var-cases (n numvars)
  `(case ,n
     . ,(var-cases-fn numvars numvars)))

(defun swap-adjacent-case (m numvars)
  `(logior (the (unsigned-byte ,(ash 1 numvars))
                (logand ,(loghead (ash 1 numvars)
                                  (logeqv (var m numvars)
                                          (var (+ 1 m) numvars)))
                        (the (unsigned-byte ,(ash 1 numvars)) truth)))
           (the (unsigned-byte ,(ash 1 numvars))
                (ash (the (unsigned-byte ,(ash 1 numvars))
                          (logand ,(logand (var (+ 1 m) numvars)
                                           (lognot (var m numvars)))
                                  (the (unsigned-byte ,(ash 1 numvars)) truth)))
                     ,(- (ash 1 m))))
           (the (unsigned-byte ,(ash 1 numvars))
                (ash (the (unsigned-byte ,(ash 1 numvars))
                          (logand ,(logand (var m numvars)
                                           (lognot (var (+ 1 m) numvars)))
                                  (the (unsigned-byte ,(ash 1 numvars)) truth)))
                     ,(ash 1 m)))))

(defun swap-adjacent-cases-fn (m numvars)
  (if (zp m)
      nil
    (cons (list (if (eql m 1) 'otherwise (1- m))
                (swap-adjacent-case (1- m) numvars))
          (swap-adjacent-cases-fn (1- m) numvars))))

(defmacro swap-adjacent-cases (numvars)
  `(case m
     . ,(swap-adjacent-cases-fn (1- numvars) numvars)))


(defun swap-vars-case (n m numvars)
  `(logior (the (unsigned-byte ,(ash 1 numvars))
                (logand ,(loghead (ash 1 numvars)
                                  (logeqv (var m numvars)
                                          (var n numvars)))
                        (the (unsigned-byte ,(ash 1 numvars)) truth)))
           (the (unsigned-byte ,(ash 1 numvars))
                (ash (the (unsigned-byte ,(ash 1 numvars))
                          (logand ,(logand (var n numvars)
                                           (lognot (var m numvars)))
                                  (the (unsigned-byte ,(ash 1 numvars)) truth)))
                     ,(- (ash 1 m) (ash 1 n))))
           (the (unsigned-byte ,(ash 1 numvars))
                (ash (the (unsigned-byte ,(ash 1 numvars))
                          (logand ,(logand (var m numvars)
                                           (lognot (var n numvars)))
                                  (the (unsigned-byte ,(ash 1 numvars)) truth)))
                     ,(- (ash 1 n) (ash 1 m))))))

(defun swap-vars-inner-loop (n m numvars)
  (if (zp m)
      nil
    (cons (list (if (eql m 1) 'otherwise (1- m))
                (swap-vars-case n (1- m) numvars))
          (swap-vars-inner-loop n (1- m) numvars))))

(defun swap-vars-outer-case (n numvars)
  `(case m
     . ,(swap-vars-inner-loop n n numvars)))

(defun swap-vars-outer-loop (n numvars)
  (if (or (zp n) (<= n 2))
      `((otherwise ,(swap-vars-case 1 0 numvars)))
    (cons (list (1- n)
                (swap-vars-outer-case (1- n) numvars))
          (swap-vars-outer-loop (1- n) numvars))))

(defmacro swap-vars-cases (numvars)
  (if (eql numvars 2)
      (swap-vars-case 1 0 numvars)
    `(case n
       . ,(swap-vars-outer-loop numvars numvars))))


(defun swap-polarity-case (m numvars)
  `(logior (the (unsigned-byte ,(ash 1 numvars))
                (ash (the (unsigned-byte ,(ash 1 numvars))
                          (logand ,(var m numvars)
                                  (the (unsigned-byte ,(ash 1 numvars)) truth)))
                     ,(- (ash 1 m))))
           (the (unsigned-byte ,(ash 1 numvars))
                (ash (the (unsigned-byte ,(- (ash 1 numvars) (ash 1 m)))
                          (logand ,(lognot (var m numvars))
                                  (the (unsigned-byte ,(ash 1 numvars)) truth)))
                     ,(ash 1 m)))))

(defun swap-polarity-cases-fn (m numvars)
  (if (zp m)
      nil
    (cons (list (if (eql m 1) 'otherwise (1- m))
                (swap-polarity-case (1- m) numvars))
          (swap-polarity-cases-fn (1- m) numvars))))

(defmacro swap-polarity-cases (numvars)
  `(case m
     . ,(swap-polarity-cases-fn numvars numvars)))

(defun permute-polarity-bindings-fn (m numvars)
  (declare (xargs :measure (nfix (- (nfix numvars) (nfix m)))
                  :mode :program))
  (if (zp (- (nfix numvars) (nfix m)))
      nil
    (cons `(truth (if (logbitp ,m mask)
                      (mbe :logic (swap-polarity ,m truth ,numvars)
                           :exec ,(swap-polarity-case m numvars))
                    truth))
          (permute-polarity-bindings-fn (1+ (nfix m)) numvars))))

(defmacro permute-polarity-bindings (numvars)
  `(b* ,(permute-polarity-bindings-fn 0 numvars)
     truth))




(local (defthmd logcdr-when-not-integerp
         (implies (not (integerp x))
                  (equal (logcdr x) 0))
         :hints(("Goal" :in-theory (enable logcdr)))))
(local (defthmd logcar-when-not-integerp
         (implies (not (integerp x))
                  (equal (logcar x) 0))
         :hints(("Goal" :in-theory (enable logcar)))))

(local
 (encapsulate nil
   (local (defun ind (width a b)
            (if (zp width)
                (list a b)
              (ind (1- width) (logcdr a) (logcdr b)))))
   (defthm logand-with-unsigned-byte
     (implies (and (unsigned-byte-p width b)
                   (syntaxp (and (quotep a)
                                 (quotep width)))
                   (not (unsigned-byte-p width a)))
              (equal (logand a b)
                     (logand (loghead width a) b)))
     :hints (("goal" :induct (ind width a b)
              :in-theory (enable* ihsext-recursive-redefs
                                  logcar-when-not-integerp
                                  logcdr-when-not-integerp))))))

(local (defthm unsigned-byte-p-of-1
         (implies (posp m)
                  (unsigned-byte-p m 1))
         :hints(("Goal" :in-theory (enable unsigned-byte-p)))))

(local (defthm ash-of-minus-1
         (implies (natp n)
                  (equal (ash -1 n)
                         (- (ash 1 n))))
         :hints(("Goal" :in-theory (enable* ihsext-inductions
                                            ihsext-recursive-redefs
                                            logcons)))))

(local (defthm ash-by-bound
         (implies (and (< n bound)
                       (syntaxp (quotep bound))
                       (natp bound)
                       (integerp n)
                       (<= (ash 1 (- bound 1)) m))
                  (<= (ash 1 n) m))
         :hints (("goal" :use ((:instance bitops::|(< (ash a b) (ash a c))|
                                (a 1) (b (- bound 1)) (c n)))
                  :in-theory (disable bitops::|(< (ash a b) (ash a c))|)))))

(local (defthm ash-by-bound-neg
         (implies (and (< n bound)
                       (syntaxp (quotep bound))
                       (natp bound)
                       (integerp n)
                       (<= m (- (ash 1 (- bound 1)))))
                  (<= m (- (ash 1 n))))
         :hints (("goal" :use ((:instance ash-by-bound (m (- m))))
                  :in-theory (disable ash-by-bound)))))


(local (defthm ash-1-n-positive
         (implies (natp n)
                  (posp (ash 1 n)))
         :rule-classes :type-prescription))

(local (defthm ash-of-logand
         (equal (ash (logand a b) sh)
                (logand (ash a sh) (ash b sh)))
         :hints(("Goal" :in-theory (enable* ihsext-inductions
                                            ihsext-recursive-redefs)))))

(local
 (defthm ash-1-monotonic
   (implies (and (< a b)
                 (natp a)
                 (integerp b))
            (< (ash 1 a)
               (ash 1 b)))
   :hints(("Goal" :in-theory (enable bitops::ash-is-expt-*-x)))
   :rule-classes ((:rewrite) (:linear))))

(local (defthm signed-byte-p-by-unsigned-byte-p
         (implies (unsigned-byte-p (1- w) x)
                  (signed-byte-p w x))
         :hints(("Goal" :in-theory (enable unsigned-byte-p signed-byte-p)))))

(local (defthm logcount-of-loghead-+-1
         (implies (natp n)
                  (equal (logcount (loghead (+ 1 n) mask))
                         (+ (logbit n mask)
                            (logcount (loghead n mask)))))
         :hints(("Goal" :in-theory (enable* ihsext-inductions
                                            ihsext-recursive-redefs)))))

(local (defthm logcount-of-loghead-bound
         (<= (logcount (loghead n x)) (nfix n))
         :hints(("Goal" :in-theory (enable* ihsext-inductions
                                            ihsext-recursive-redefs)))
         :rule-classes :linear))

(local (in-theory (disable bitops::logior-<-0-linear-2
                           bitops::logior-<-0-linear-1
                           bitops::logand->=-0-linear-1
                           bitops::upper-bound-of-logand
                           bitops::|(< a (logtail n a))|
                           acl2::natp-posp
                           bitops::lognot-<-const
                           acl2::posp-rw
                           acl2::posp-redefinition
                           acl2::ifix-when-not-integerp)))

(local (defthm truth-norm-when-unsigned-byte-p
         (implies (unsigned-byte-p (ash 1 (nfix numvars)) truth)
                  (equal (truth-norm truth numvars)
                         truth))
         :hints(("Goal" :in-theory (enable truth-norm)))))


(local (defthmd normalize-logand-neg-with-ash-of-unsigned-byte-lemma
         (implies (and ;; (syntaxp (and (quotep n) (quotep k)
                       ;;               (negp (unquote n))))
                       ;;(unsigned-byte-p m x)
                       ;; (syntaxp (quotep m))
                       (natp k))
                  (equal (logand n (ash (loghead m x) k))
                         (logand (loghead (+ (nfix m) k) n) (ash (loghead m x) k))))
         :hints ((acl2::logbitp-reasoning))))

(local (defthm normalize-logand-neg-with-ash-of-unsigned-byte
         (implies (and (syntaxp (and (quotep n) (quotep k)
                                     (negp (unquote n))))
                       (unsigned-byte-p m x)
                       (syntaxp (quotep m))
                       (natp k))
                  (equal (logand n (ash x k))
                         (logand (loghead (+ m k) n) (ash x k))))
         :hints (("goal" :use ((:instance normalize-logand-neg-with-ash-of-unsigned-byte-lemma)))
                 (and stable-under-simplificationp
                      '(:in-theory (enable unsigned-byte-p))))))


(local (defthmd ash-of-logtail-when-loghead-0
         (implies (and (equal (loghead m n) 0)
                       (natp m))
                  (equal (ash (logtail m n) m)
                         (ifix n)))
         :hints ((acl2::logbitp-reasoning))))

(local (defthm normalize-logand-of-ash-to-ash-of-loghead
         (implies (and (syntaxp (and (quotep n)
                                     (quotep m)))
                       (natp m)
                       (equal (loghead m n) 0)
                       (logmaskp (ash n (- m))))
                  (equal (logand n (ash x m))
                         (ash (logand (ash n (- m)) x) m)))
         :hints(("Goal" :in-theory (enable ash-of-logtail-when-loghead-0)))))

(local (defthmd normalize-logand-const-with-loghead-lemma
         (equal (logand (loghead m n) (loghead m x))
                (logand (loghead m n) x))
         :hints ((acl2::logbitp-reasoning))))

(local (defthm normalize-logand-const-with-loghead
         (implies (and (syntaxp (and (quotep n) (quotep m)))
                       (unsigned-byte-p m n))
                  (equal (logand n (loghead m x))
                         (logand n x)))
         :hints (("goal" :use normalize-logand-const-with-loghead-lemma))))

(local (defun normalize-unsigned-byte-p-neg-const-ind (n m x)
         (if (zp n)
             (list m x)
           (normalize-unsigned-byte-p-neg-const-ind (1- n) (logcdr m) (logcdr x)))))

(local (defthmd normalize-unsigned-byte-p-neg-const-lemma
         (implies (and (unsigned-byte-p (integer-length m) x)
                       (equal 0 (loghead (integer-length m) m)))
                  (equal (logand m x) 0))
         :hints (("goal" :induct (logand m x)
                  :in-theory (enable* ihsext-recursive-redefs
                                      ihsext-inductions)
                  :expand ((integer-length m))))))

(local (defthm normalize-unsigned-byte-p-neg-const
         (implies (and (syntaxp (and (quotep n) (quotep m)))
                       (negp m)
                       (unsigned-byte-p (integer-length m) x)
                       (unsigned-byte-p n (loghead (integer-length m) m)))
                  (unsigned-byte-p n (logand m x)))
         :hints (("goal" :induct (normalize-unsigned-byte-p-neg-const-ind n m x)
                  :in-theory (enable* ihsext-recursive-redefs
                                      normalize-unsigned-byte-p-neg-const-lemma)
                  :expand ((integer-length m)
                           (:free (n) (unsigned-byte-p (+ 1 n) x)))))))
         


(local (in-theory (disable (tau-system))))

(progn
  (defconst *truth-defs*
    '(defsection truth<NUMVARS>
       
       (fty::defbitstruct truth<NUMVARS> <WIDTH>)

       (defthm truth<NUMVARS>-fix-is-truth-norm
         (equal (truth<NUMVARS>-fix x)
                (truth-norm x <NUMVARS>))
         :hints(("Goal" :in-theory (enable truth<NUMVARS>-fix
                                           truth-norm))))

       (defthm truth-norm-when-truth<NUMVARS>-p
         (implies (truth<NUMVARS>-p x)
                  (equal (truth-norm x <NUMVARS>) x))
         :hints(("Goal" :in-theory (enable truth<NUMVARS>-p
                                           truth-norm))))

       (defthm truth-norm-under-when-truth<NUMVARS>-equiv
         (truth<NUMVARS>-equiv (truth-norm x <NUMVARS>)
                               x)
         :hints(("Goal" :in-theory (enable truth<NUMVARS>-equiv))))

       (defmacro truth<NUMVARS>-fix$ (x)
         `(mbe :logic (truth-norm ,x <NUMVARS>)
               :exec (truth<NUMVARS>-fix ,x)))

       ;; override
       (fty::deffixtype truth<NUMVARS>
         :pred truth<NUMVARS>-p
         :fix truth<NUMVARS>-fix$
         :equiv truth<NUMVARS>-equiv)

       (fty::deffixcong truth<NUMVARS>-equiv equal (truth-norm x <NUMVARS>) x)



       ;; (local (defthm unsigned-byte-p-when-truth<NUMVARS>-p-strong
       ;;          (implies (and (truth<NUMVARS>-p x)
       ;;                        (natp size)
       ;;                        (>= size <WIDTH>))
       ;;                   (unsigned-byte-p size x))
       ;;          :hints(("Goal" :in-theory (enable truth<NUMVARS>-p)))))

       (local (defthm unsigned-byte-p-when-truth<NUMVARS>-p-forward
                (implies (truth<NUMVARS>-p x)
                         (unsigned-byte-p <WIDTH> x))
                :rule-classes :forward-chaining))

       (define true<NUMVARS> ()
         :inline t :enabled t
         (mbe :logic (truth-norm (true) <NUMVARS>)
              :exec <MASK>))

       (define truth-eval<NUMVARS> ((truth truth<NUMVARS>-p :type (unsigned-byte <WIDTH>))
                                    (env :type (unsigned-byte <NUMVARS>)))
         :guard (and ;; (unsigned-byte-p <WIDTH> truth)
                 (unsigned-byte-p <NUMVARS> env))
         :split-types t
         :guard-hints (("goal" :in-theory (enable truth-eval)))
         :enabled t :inline t
         (mbe :logic (truth-eval truth env <NUMVARS>)
              :exec (logbitp (the (unsigned-byte <NUMVARS>) env)
                             (the (unsigned-byte <WIDTH>) truth))))

       (defconst *vars<NUMVARS>*
         (compress1 'vars<NUMVARS>
                    (cons '(:header :dimensions (<NUMVARS>)
                            :maximum-length <NUMVARS+1>
                            :name 'vars<NUMVARS>)
                          (var-alist <NUMVARS> <NUMVARS>))))
       (defmacro vars<NUMVARS> ()
         (list 'quote *vars<NUMVARS>*))

       (define var<NUMVARS> ((n :type (integer 0 <NUMVARS-1>)))
         :guard (and (natp n) (< n <NUMVARS>))
         :split-types t
         :enabled t :inline t
         (mbe :logic (var n <NUMVARS>)
              :exec (var-cases n <NUMVARS>)
              ;; (aref1 'vars<NUMVARS> (vars<NUMVARS>) n)
              ))

       (define truth-norm<NUMVARS> ((truth integerp))
         :guard-hints (("goal" :in-theory (enable truth-norm)))
         :enabled t :inline t
         (mbe :logic (truth-norm truth <NUMVARS>)
              :exec (logand <MASK> truth)))


       
       (define swap-polarity<NUMVARS> ((m :type (integer 0 <NUMVARS-1>))
                                       (truth truth<NUMVARS>-p :type (unsigned-byte <WIDTH>)))
         :guard (and (natp m) (< m <NUMVARS>)
                     ;; (unsigned-byte-p <WIDTH> truth)
                     )
         ;; :guard-debug t
         :guard-hints (("Goal" :in-theory (enable swap-polarity)))
         :split-types t
         :enabled t
         (:@ :fixnum :inline t) ;; marginal speed improvement
         (mbe :logic (swap-polarity m truth <NUMVARS>)
              :exec (swap-polarity-cases <NUMVARS>)))

       (define permute-polarity<NUMVARS> ((mask :type (unsigned-byte <NUMVARS>))
                                          (truth truth<NUMVARS>-p :type (unsigned-byte <WIDTH>)))
         :guard (and (unsigned-byte-p <NUMVARS> mask)
                     ;; (unsigned-byte-p <WIDTH> truth)
                     )
         :guard-hints (("Goal" ;; :in-theory (enable swap-polarity)
                        :expand ((:free (a b c) (permute-polarity a b c <NUMVARS>))))
                       (and stable-under-simplificationp
                            (let ((lit (car (last clause))))
                              (case-match lit
                                (('equal ('swap-polarity n truth numvars) &)
                                 `(:expand ((swap-polarity ,n ,truth ,numvars))))))))
         ;; :guard-debug t
         :enabled t
         (mbe :logic (permute-polarity 0 mask truth <NUMVARS>)
              :exec (permute-polarity-bindings <NUMVARS>)))


       (define positive-cofactor<NUMVARS> ((n :type (integer 0 <NUMVARS-1>))
                                           (truth truth<NUMVARS>-p :type (unsigned-byte <WIDTH>)))
         :guard (and (natp n) (< n <NUMVARS>)
                     ;; (unsigned-byte-p <WIDTH> truth)
                     )
         :guard-hints(("Goal" :in-theory (enable positive-cofactor)))
         :split-types t
         :enabled t :inline t
         (mbe :logic (positive-cofactor n truth <NUMVARS>)
              :exec
              (B* (((the (unsigned-byte <WIDTH>) mask)
                    (logand (the (unsigned-byte <WIDTH>) (var<NUMVARS> n))
                            (the (unsigned-byte <WIDTH>) truth))))
                (logior (the (unsigned-byte <WIDTH>) mask)
                        (the (unsigned-byte <WIDTH>)
                             (ash (the (unsigned-byte <WIDTH>) mask)
                                  (the (integer <-WIDTH/2> 0)
                                       (ash -1
                                            (the (integer 0 <NUMVARS-1>) (lnfix n))))))))))

       (define negative-cofactor<NUMVARS> ((n :type (integer 0 <NUMVARS-1>))
                                           (truth truth<NUMVARS>-p :type (unsigned-byte <WIDTH>)))
         :guard (and (natp n) (< n <NUMVARS>)
                     ;; (unsigned-byte-p <WIDTH> truth)
                     )
         :guard-hints (("goal" :in-theory (e/d (negative-cofactor)
                                               (var-negated-masked-size
                                                ash-of-logand))
                        :use ((:instance size-of-logand-by-size-of-loghead
                               (a truth) (b (lognot (var n <NUMVARS>)))
                               (m <WIDTH>) (n (- <WIDTH> (ash 1 (nfix n)))))
                              (:instance var-negated-masked-size
                               (numvars <NUMVARS>)))))
         :guard-debug t
         :split-types t
         :enabled t :inline t
         (mbe :logic (negative-cofactor n truth <NUMVARS>)
              :exec (B* (((the (unsigned-byte <WIDTH>) mask)
                          (logand (the (signed-byte <WIDTH+1>)
                                       (lognot (the (unsigned-byte <WIDTH>) (var<NUMVARS> n))))
                                  (the (unsigned-byte <WIDTH>) truth))))
                      (logior (the (unsigned-byte <WIDTH>) mask)
                              (the (unsigned-byte <WIDTH>)
                                   (ash (the (unsigned-byte <WIDTH-1>) mask)
                                        (the (integer 0 <WIDTH/2>)
                                             (ash (the (unsigned-byte 1) 1)
                                                  (the (integer 0 <NUMVARS-1>)
                                                       (lnfix n))))))))))

       (define depends-on<NUMVARS> ((n :type (integer 0 <NUMVARS-1>))
                                    (truth truth<NUMVARS>-p :type (unsigned-byte <WIDTH>)))
         :guard (and (natp n) (< n <NUMVARS>)
                     ;; (unsigned-byte-p <WIDTH> truth)
                     )
         :split-types t
         :guard-hints (("goal" :in-theory (enable depends-on truth-norm)))
         :enabled t
         :inline t
         (mbe :logic (depends-on n truth <NUMVARS>)
              :exec
              (b* ((var (var<NUMVARS> n)))
                (not (eql (the (unsigned-byte <WIDTH>)
                               (logand (the (signed-byte <WIDTH+1>)
                                            (lognot (the (unsigned-byte <WIDTH>) var)))
                                       (the (unsigned-byte <WIDTH>) truth)))
                          (the (unsigned-byte <WIDTH>)
                               (ash (the (unsigned-byte <WIDTH>)
                                         (logand (the (unsigned-byte <WIDTH>) var)
                                                 (the (unsigned-byte <WIDTH>) truth)))
                                    (the (integer <-WIDTH/2> 0)
                                         (ash -1
                                              (the (integer 0 <NUMVARS-1>) (lnfix n)))))))))))

       (define is-xor-with-var<NUMVARS> ((n :type (integer 0 <NUMVARS-1>))
                                         (truth truth<NUMVARS>-p :type (unsigned-byte <WIDTH>)))
         :guard (and (natp n) (< n <NUMVARS>)
                     ;; (unsigned-byte-p <WIDTH> truth)
                     )
         :split-types t
         :guard-hints (("goal" :in-theory (enable is-xor-with-var truth-norm)))
         :enabled t
         (mbe :logic (is-xor-with-var n truth <NUMVARS>)
              :exec
              (eql (the (unsigned-byte <WIDTH>) (positive-cofactor<NUMVARS> n truth))
                   (truth-norm<NUMVARS>
                    (the (signed-byte <WIDTH+1>)
                         (lognot (the (unsigned-byte <WIDTH>)
                                      (negative-cofactor<NUMVARS> n truth))))))))

       ;; Various swap-vars implementations benchmarked below -- enumerating
       ;; all the cases seems fastest for up to 6 vars
       (define swap-vars<NUMVARS> ((n :type (integer 0 <NUMVARS-1>))
                                   (m :type (integer 0 <NUMVARS-1>))
                                   (truth truth<NUMVARS>-p :type (unsigned-byte <WIDTH>)))
         :guard (and (natp n) (< n <NUMVARS>)
                     (natp m) (< m <NUMVARS>)
                     ;; (unsigned-byte-p <WIDTH> truth)
                     )
         :guard-hints (("Goal" :in-theory (enable swap-vars swap-vars-aux)))
         :split-types t
         :enabled t
         (mbe :logic (swap-vars n m truth <NUMVARS>)
              :exec (if (eql n m)
                        truth
                      (mv-let (n m)
                        (if (< m n)
                            (mv n m)
                          (mv m n))
                        (swap-vars-cases <NUMVARS>)))))

       (define swap-vars-ordered<NUMVARS> ((n :type (integer 0 <NUMVARS-1>))
                                           (m :type (integer 0 <NUMVARS-1>))
                                           (truth truth<NUMVARS>-p :type (unsigned-byte <WIDTH>)))
         :guard (and (natp n) (< n <NUMVARS>)
                     (natp m) (<= m n)
                     ;; (unsigned-byte-p <WIDTH> truth)
                     )
         :guard-hints (("Goal" :in-theory (enable swap-vars swap-vars-aux)))
         :split-types t
         :enabled t
         (mbe :logic (swap-vars n m truth <NUMVARS>)
              :exec (if (eql n m)
                        truth
                      (swap-vars-cases <NUMVARS>))))

       ;; very marginally faster for the adjacent variables case
       (define swap-adjacent-vars<NUMVARS> ((m :type (integer 0 <NUMVARS-1>))
                                            (truth truth<NUMVARS>-p :type (unsigned-byte <WIDTH>)))
         :guard (and (natp m) (< m <NUMVARS-1>)
                     ;; (unsigned-byte-p <WIDTH> truth)
                     )
         :guard-hints (("Goal" :in-theory (enable swap-vars swap-vars-aux)))
         :split-types t
         :enabled t
         (:@ :fixnum :inline t) ;; marginal speed improvement
         (mbe :logic (swap-vars (+ 1 (nfix m)) m truth <NUMVARS>)
              :exec (swap-adjacent-cases <NUMVARS>)))

       (define permute-var-up<NUMVARS> ((m :type (integer 0 <NUMVARS-1>))
                                        (n :type (integer 0 <NUMVARS-1>))
                                        (truth truth<NUMVARS>-p :type (unsigned-byte <WIDTH>)))
         :guard (and (natp m) (natp n)
                     ;; (unsigned-byte-p <WIDTH> truth)
                     (<= m n) (< n <NUMVARS>))
         :split-types t
         :enabled t
         :guard-hints (("goal" :expand ((:free (n numvars) (permute-var-up m n truth numvars)))
                        :in-theory (enable truth-norm
                                           permute-var-up<NUMVARS>)))
         (mbe :logic (permute-var-up m n truth <NUMVARS>)
              :exec (b* (((when (eql n m))
                          truth)
                         (next (1+ m))
                         (truth (swap-adjacent-vars<NUMVARS> m truth)))
                      (permute-var-up<NUMVARS> next n truth))))

       (define permute-var-down<NUMVARS> ((m :type (integer 0 <NUMVARS-1>))
                                          (n :type (integer 0 <NUMVARS-1>))
                                          (truth truth<NUMVARS>-p :type (unsigned-byte <WIDTH>)))
         :guard (and (natp m) (natp n)
                     ;; (unsigned-byte-p <WIDTH> truth)
                     (<= m n) (< n <NUMVARS>))
         :split-types t
         :enabled t
         :guard-hints (("goal" :expand ((:free (n numvars) (permute-var-down m n truth numvars)))
                        :in-theory (enable truth-norm
                                           permute-var-down<NUMVARS>)))
         (mbe :logic (permute-var-down m n truth <NUMVARS>)
              :exec (b* (((when (eql n m))
                          truth)
                         (next (1+ m))
                         (truth (permute-var-down<NUMVARS> next n truth)))
                      (swap-adjacent-vars<NUMVARS> m truth))))

       (define permute-stretch<NUMVARS> ((n :type (integer 0 <NUMVARS>))
                                         (count :type (integer 0 <NUMVARS>))
                                         (mask :type (unsigned-byte <NUMVARS>))
                                         (truth truth<NUMVARS>-p :type (unsigned-byte <WIDTH>)))
         :guard (and (natp n) (<= n <NUMVARS>)
                     ;; (unsigned-byte-p <WIDTH> truth)
                     (unsigned-byte-p <NUMVARS> mask)
                     (equal count (logcount (loghead n mask))))
         :guard-hints (("goal" :expand ((:free (count numvars)
                                         (permute-stretch n count mask truth numvars)))
                        :in-theory (enable truth-norm
                                           permute-stretch<NUMVARS>)))
         :split-types t
         :enabled t
         (mbe :logic (permute-stretch n count mask truth <NUMVARS>)
              :exec
              (b* (((when (eql n <NUMVARS>)) truth)
                   (bit (logbit (the (integer 0 <NUMVARS-1>) n)
                                (the (unsigned-byte <NUMVARS>) mask)))
                   (truth (permute-stretch<NUMVARS> (1+ n) (+ bit count) mask truth)))
                (if (eql (the bit bit) 1)
                    (permute-var-up<NUMVARS> count n truth)
                  truth))))

       (define permute-shrink<NUMVARS> ((n :type (integer 0 <NUMVARS>))
                                        (count :type (integer 0 <NUMVARS>))
                                        (mask :type (unsigned-byte <NUMVARS>))
                                        (truth truth<NUMVARS>-p :type (unsigned-byte <WIDTH>)))
         :guard (and (natp n) (<= n <NUMVARS>)
                     ;; (unsigned-byte-p <WIDTH> truth)
                     (unsigned-byte-p <NUMVARS> mask)
                     (equal count (logcount (loghead n mask))))
         :guard-hints (("goal" :expand ((:free (count numvars)
                                         (permute-shrink n count mask truth numvars)))
                        :in-theory (enable truth-norm
                                           permute-shrink<NUMVARS>)))
         :split-types t
         :enabled t
         (mbe :logic (permute-shrink n count mask truth <NUMVARS>)
              :exec (b* (((when (eql n <NUMVARS>))
                          truth)
                         (bit (logbit (the (integer 0 <NUMVARS-1>) n)
                                      (the (unsigned-byte <NUMVARS>) mask)))
                         (truth (if (eql (the bit bit) 1)
                                    (permute-var-down<NUMVARS> count n truth)
                                  truth)))
                      (permute-shrink<NUMVARS> (1+ n) (+ bit count) mask truth))))
       



       ;; (define swap-vars-old<NUMVARS> ((n :type (integer 0 <NUMVARS-1>))
       ;;                             (m :type (integer 0 <NUMVARS-1>))
       ;;                             (truth truth<NUMVARS>-p :type (unsigned-byte <WIDTH>)))
       ;;   :guard (and (natp n) (< n <NUMVARS>)
       ;;               (natp m) (< m <NUMVARS>)
       ;;               ;; (unsigned-byte-p <WIDTH> truth)
       ;; )
       ;;   :guard-hints (("goal" :in-theory (enable swap-vars)))
       ;;   :enabled t
       ;;   :split-types t
       ;;   ;; (mbe :logic (swap-vars n m truth <NUMVARS>)
       ;;   (b* (((the (unsigned-byte <WIDTH>) xn1)
       ;;         (the (unsigned-byte <WIDTH>)
       ;;              (positive-cofactor<NUMVARS>
       ;;               (the (integer 0 <NUMVARS-1>) n)
       ;;               (the (unsigned-byte <WIDTH>) truth))))
       ;;        ((the (unsigned-byte <WIDTH>) xn0) (negative-cofactor<NUMVARS> n truth))
       ;;        ((the (unsigned-byte <WIDTH>) xn1m1) (positive-cofactor<NUMVARS> m xn1))
       ;;        ((the (unsigned-byte <WIDTH>) xn1m0) (negative-cofactor<NUMVARS> m xn1))
       ;;        ((the (unsigned-byte <WIDTH>) xn0m1) (positive-cofactor<NUMVARS> m xn0))
       ;;        ((the (unsigned-byte <WIDTH>) xn0m0) (negative-cofactor<NUMVARS> m xn0))
       ;;        ((the (unsigned-byte <WIDTH>) mvar) (var<NUMVARS> m))
       ;;        ((the (unsigned-byte <WIDTH>) nvar) (var<NUMVARS> n))
       ;;        ((the (signed-byte <WIDTH+1>) ~mvar) (lognot mvar))
       ;;        ((the (signed-byte <WIDTH+1>) ~nvar) (lognot nvar))
       ;;        ;; want (if n (if m xn1m1 xn0m1) (if m xn1m0 xn0m0))
       ;;        ((the (unsigned-byte <WIDTH>) n1case)
       ;;         (the (unsigned-byte <WIDTH>)
       ;;              (logior (the (unsigned-byte <WIDTH>)
       ;;                           (logand (the (unsigned-byte <WIDTH>) mvar)
       ;;                                   (the (unsigned-byte <WIDTH>) xn1m1)))
       ;;                      (the (unsigned-byte <WIDTH>)
       ;;                           (logand (the (signed-byte <WIDTH+1>) ~mvar)
       ;;                                   (the (unsigned-byte <WIDTH>) xn0m1))))))
       ;;        ((the (unsigned-byte <WIDTH>) n0case)
       ;;         (logior (the (unsigned-byte <WIDTH>) (logand mvar xn1m0))
       ;;                 (the (unsigned-byte <WIDTH>) (logand ~mvar xn0m0)))))
       ;;     (logior (the (unsigned-byte <WIDTH>) (logand nvar n1case))
       ;;             (the (unsigned-byte <WIDTH>) (logand ~nvar n0case)))))


       ;; (define swap-vars*<NUMVARS> ((n :type (integer 0 <NUMVARS-1>))
       ;;                             (m :type (integer 0 <NUMVARS-1>))
       ;;                             (truth truth<NUMVARS>-p :type (unsigned-byte <WIDTH>)))
       ;;   :guard (and (natp n) (< n <NUMVARS>)
       ;;               (natp m) (< m n)
       ;;               ;; (unsigned-byte-p <WIDTH> truth)
       ;; )
       ;;   :guard-hints (("Goal" :in-theory (enable swap-vars)))
       ;;   :split-types t
       ;;   :enabled t
       ;;   (mbe :logic (swap-vars n m truth <NUMVARS>)
       ;;        :exec (b* (((the (unsigned-byte <WIDTH>) varn) (var<NUMVARS> n))
       ;;                   ((the (unsigned-byte <WIDTH>) varm) (var<NUMVARS> m))
       ;;                   ((the (signed-byte <WIDTH+1>) same) (logeqv varn varm))
       ;;                   ((the (unsigned-byte <WIDTH>) n&~m) (logand varn (lognot varm)))
       ;;                   ((the (unsigned-byte <WIDTH>) m&~n) (logand varm (lognot varn)))
       ;;                   ((the (unsigned-byte <WIDTH>) shift)
       ;;                    (- (the (unsigned-byte <WIDTH>) (ash 1 (lnfix n)))
       ;;                       (the (unsigned-byte <WIDTH>) (ash 1 (lnfix m))))))
       ;;                (logior (the (unsigned-byte <WIDTH>) (logand same truth))
       ;;                        (the (unsigned-byte <WIDTH>)
       ;;                             (ash (the (unsigned-byte <WIDTH>) (logand n&~m truth))
       ;;                                  (- shift)))
       ;;                        (the (unsigned-byte <WIDTH>)
       ;;                             (ash (the (unsigned-byte <WIDTH>) (logand m&~n truth))
       ;;                                  shift))))))


       ))

  (defmacro deftruthsize (n)
    `(make-event
      (acl2::template-subst *truth-defs*
                            :str-alist '(("<NUMVARS>" ,(coerce (explode-atom n 10) 'string) . truthpkg))
                            :atom-alist '((<NUMVARS> . ,n)
                                          (<NUMVARS-1> . ,(1- n))
                                          (<NUMVARS+1> . ,(1+ n))
                                          (<WIDTH> . ,(ash 1 n))
                                          (<WIDTH-1> . ,(1- (ash 1 n)))
                                          (<WIDTH/2> . ,(ash 1 (1- n)))
                                          (<-WIDTH/2> . ,(- (ash 1 (1- n))))
                                          (<WIDTH+1> . ,(1+ (ash 1 n)))
                                          (<MASK> . ,(1- (ash 1 (ash 1 n)))))
                            :features ',(and (< n 6) '(:fixnum)))))

  (deftruthsize 6)
  (deftruthsize 5)
  (deftruthsize 4)
  (deftruthsize 3))


#||

;; 0.35 sec:
(time
 (loop for i from 1 to 10000000 do
       (let ((truth (logand #xffff i)))
         (loop for n from 1 to 3 do
               (loop for m from 0 to (1- n) do
                     (swap-vars-ordered4 n m truth))))))

;; 0.40 sec:
(time
 (loop for i from 1 to 10000000 do
       (let ((truth (logand #xffff i)))
         (loop for n from 1 to 3 do
               (loop for m from 0 to (1- n) do
                     (swap-vars4 n m truth))))))
;; 2.6 sec:
(time
 (loop for i from 1 to 10000000 do
       (let ((truth (logand #xffff i)))
         (loop for n from 1 to 3 do
               (loop for m from 0 to (1- n) do
                     (swap-vars*4 n m truth))))))

;; 1.4 sec:
(time
 (loop for i from 1 to 10000000 do
       (let ((truth (logand #xffff i)))
         (loop for n from 1 to 3 do
               (loop for m from 0 to (1- n) do
                     (swap-vars-old4 n m truth))))))

;; 0.20 sec:
(time
 (loop for i from 1 to 10000000 do
       (let ((truth (logand #xffff i)))
         (loop for n from 1 to 3 do
               (loop for m from 0 to (1- n) do
                     (swap-adjacent-vars4 m truth))))))


;; 0.73 sec:
(time
 (loop for i from 1 to 10000000 do
       (let ((truth (* i 429)))
         (loop for n from 1 to 4 do
               (loop for m from 0 to (1- n) do
                     (swap-vars5 n m truth))))))

;; 0.58 sec:
(time
 (loop for i from 1 to 10000000 do
       (let ((truth (* i 429)))
         (loop for n from 1 to 4 do
               (loop for m from 0 to (1- n) do
                     (swap-vars-ordered5 n m truth))))))
;; 4.3 sec:
(time
 (loop for i from 1 to 10000000 do
       (let ((truth (* i 429)))
         (loop for n from 1 to 4 do
               (loop for m from 0 to (1- n) do
                     (swap-vars*5 n m truth))))))

;; 2.6 sec:
(time
 (loop for i from 1 to 10000000 do
       (let ((truth (* i 429)))
         (loop for n from 1 to 4 do
               (loop for m from 0 to (1- n) do
                     (swap-vars-old5 n m truth))))))

;; 0.51 sec:
(time
 (loop for i from 1 to 10000000 do
       (let ((truth (* i 429)))
         (loop for n from 1 to 4 do
               (loop for m from 0 to (1- n) do
                     (swap-adjacent-vars4 m truth))))))



;; 11.8 sec:
(time
 (loop for i from 1 to 10000000 do
       (let ((truth (* i #x1AD7F29ABCA)))
         (loop for n from 1 to 5 do
               (loop for m from 0 to (1- n) do
                     (swap-vars6 n m truth))))))

;; 54.6 sec:
(time
 (loop for i from 1 to 10000000 do
       (let ((truth (* i #x1AD7F29ABCA)))
         (loop for n from 1 to 5 do
               (loop for m from 0 to (1- n) do
                     (swap-vars*6 n m truth))))))

;; 124 sec:
(time
 (loop for i from 1 to 10000000 do
       (let ((truth (* i #x1AD7F29ABCA)))
         (loop for n from 1 to 5 do
               (loop for m from 0 to (1- n) do
                     (swap-vars-old6 n m truth))))))

;; 13.3 sec:
(time
 (loop for i from 1 to 10000000 do
       (let ((truth (* i #x1AD7F29ABCA)))
         (loop for n from 1 to 5 do
               (loop for m from 0 to (1- n) do
                     (swap-adjacent-vars6 m truth))))))




||#
