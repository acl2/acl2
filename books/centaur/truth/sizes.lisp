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

(progn
  (defconst *truth-defs*
    '(defsection truth<NUMVARS>
       (local (include-book "centaur/bitops/ihsext-basics" :dir :system))
       (local (include-book "centaur/bitops/signed-byte-p" :dir :system))
       (local (include-book "centaur/bitops/ash-bounds" :dir :system))
       (local (include-book "arithmetic/top-with-meta" :dir :system))
       (local (include-book "std/basic/arith-equivs" :dir :system))
       (local (in-theory (disable unsigned-byte-p signed-byte-p)))

       (define true<NUMVARS> ()
         :inline t :enabled t
         (mbe :logic (truth-norm (true) <NUMVARS>)
              :exec <MASK>))

       (define truth-eval<NUMVARS> ((truth :type (unsigned-byte <WIDTH>))
                                    (env :type (unsigned-byte <NUMVARS>)))
         :guard (and (unsigned-byte-p <WIDTH> truth)
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



       (define positive-cofactor<NUMVARS> ((n :type (integer 0 <NUMVARS-1>))
                                           (truth :type (unsigned-byte <WIDTH>)))
         :guard (and (natp n) (< n <NUMVARS>)
                     (unsigned-byte-p <WIDTH> truth))
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

       (local (defthm ash-1-n-positive
                (implies (natp n)
                         (posp (ash 1 n)))
                :rule-classes :type-prescription))

       (define negative-cofactor<NUMVARS> ((n :type (integer 0 <NUMVARS-1>))
                                           (truth :type (unsigned-byte <WIDTH>)))
         :guard (and (natp n) (< n <NUMVARS>)
                     (unsigned-byte-p <WIDTH> truth))
         :guard-hints (("goal" :in-theory (e/d (negative-cofactor)
                                               (var-negated-masked-size))
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
                                    (truth :type (unsigned-byte <WIDTH>)))
         :guard (and (natp n) (< n <NUMVARS>)
                     (unsigned-byte-p <WIDTH> truth))
         :split-types t
         :guard-hints (("goal" :in-theory (enable depends-on truth-norm)))
         :enabled t
         (mbe :logic (depends-on n truth <NUMVARS>)
              :exec
              (not (eql (the (unsigned-byte <WIDTH>) (positive-cofactor<NUMVARS> n truth))
                        (the (unsigned-byte <WIDTH>) truth)))))

       (define is-xor-with-var<NUMVARS> ((n :type (integer 0 <NUMVARS-1>))
                                         (truth :type (unsigned-byte <WIDTH>)))
         :guard (and (natp n) (< n <NUMVARS>)
                     (unsigned-byte-p <WIDTH> truth))
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

       (define swap-vars<NUMVARS> ((n :type (integer 0 <NUMVARS-1>))
                                   (m :type (integer 0 <NUMVARS-1>))
                                   (truth :type (unsigned-byte <WIDTH>)))
         :guard (and (natp n) (< n <NUMVARS>)
                     (natp m) (< m <NUMVARS>)
                     (unsigned-byte-p <WIDTH> truth))
         :guard-hints (("goal" :in-theory (enable swap-vars)))
         :enabled t
         :split-types t
         (mbe :logic (swap-vars n m truth <NUMVARS>)
              :exec (b* (((the (unsigned-byte <WIDTH>) xn1)
                          (the (unsigned-byte <WIDTH>)
                               (positive-cofactor<NUMVARS>
                                (the (integer 0 <NUMVARS-1>) n)
                                (the (unsigned-byte <WIDTH>) truth))))
                         ((the (unsigned-byte <WIDTH>) xn0) (negative-cofactor<NUMVARS> n truth))
                         ((the (unsigned-byte <WIDTH>) xn1m1) (positive-cofactor<NUMVARS> m xn1))
                         ((the (unsigned-byte <WIDTH>) xn1m0) (negative-cofactor<NUMVARS> m xn1))
                         ((the (unsigned-byte <WIDTH>) xn0m1) (positive-cofactor<NUMVARS> m xn0))
                         ((the (unsigned-byte <WIDTH>) xn0m0) (negative-cofactor<NUMVARS> m xn0))
                         ((the (unsigned-byte <WIDTH>) mvar) (var<NUMVARS> m))
                         ((the (unsigned-byte <WIDTH>) nvar) (var<NUMVARS> n))
                         ((the (signed-byte <WIDTH+1>) ~mvar) (lognot mvar))
                         ((the (signed-byte <WIDTH+1>) ~nvar) (lognot nvar))
                         ;; want (if n (if m xn1m1 xn0m1) (if m xn1m0 xn0m0))
                         ((the (unsigned-byte <WIDTH>) n1case)
                          (the (unsigned-byte <WIDTH>)
                               (logior (the (unsigned-byte <WIDTH>)
                                            (logand (the (unsigned-byte <WIDTH>) mvar)
                                                    (the (unsigned-byte <WIDTH>) xn1m1)))
                                       (the (unsigned-byte <WIDTH>)
                                            (logand (the (signed-byte <WIDTH+1>) ~mvar)
                                                    (the (unsigned-byte <WIDTH>) xn0m1))))))
                         ((the (unsigned-byte <WIDTH>) n0case)
                          (logior (the (unsigned-byte <WIDTH>) (logand mvar xn1m0))
                                  (the (unsigned-byte <WIDTH>) (logand ~mvar xn0m0)))))
                      (logior (the (unsigned-byte <WIDTH>) (logand nvar n1case))
                              (the (unsigned-byte <WIDTH>) (logand ~nvar n0case))))))))

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
                                          (<MASK> . ,(1- (ash 1 (ash 1 n))))))))

  (deftruthsize 6)
  (deftruthsize 5)
  (deftruthsize 4)
  (deftruthsize 3))

                      
