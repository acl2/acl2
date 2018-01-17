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

(in-package "BITOPS")

(include-book "std/util/define" :dir :system)
(include-book "ihs/logops-definitions" :dir :system)
(include-book "centaur/fty/fixequiv" :dir :system)
(include-book "std/basic/arith-equiv-defs" :dir :system)

(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable unsigned-byte-p logmask)))
(local (std::add-default-post-define-hook :fix))


(local (encapsulate nil
         (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

         (defthm mod-when-less
           (implies (and (natp n) (natp w)
                         (< n w))
                    (equal (mod n w) n)))

         (defthm mod-when-greater
           (implies (and (natp n) (natp w)
                         (<= w n)
                         (syntaxp (not (equal w ''0))))
                    (equal (mod n w)
                           (mod (- n w) w))))

         (defthm natp-of-mod
           (implies (and (natp n) (natp w))
                    (natp (mod n w)))
           :hints(("Goal" :in-theory (disable (force)))))

         (defthm mod-less-than-modulus
           (implies (and (natp n) (posp w))
                    (< (mod n w) w)))))

(local (defthm lognot-of-logapp
         (equal (lognot (logapp w a b))
                (logapp w (lognot a) (lognot b)))
         :hints(("Goal" :in-theory (e/d* (ihsext-inductions)
                                         (bitops::logapp-of-i-0))
                 :induct (logapp w a b)
                 :expand ((:free (a b) (logapp w a b)))))))

(define logrepeat ((times natp) (width natp) (data integerp))
  :returns (reps natp :rule-classes :type-prescription)
  (if (zp times)
      0
    (logapp width data (logrepeat (1- times) width data)))
  ///
  (local (defret size-of-logrepeat-lemma
           (unsigned-byte-p (* (nfix width) (nfix times)) reps)))

  (defret size-of-logrepeat
    (implies (and (<= (* (nfix width) (nfix times)) n)
                  (natp n))
             (unsigned-byte-p n reps)))


  (defret logrepeat-of-loghead
    (equal (logrepeat times width (loghead width data))
           (logrepeat times width data))
    :hints (("goal" :induct <call>
             :expand ((:free (data) <call>)))))

  ;; (local (defthm unsigned-byte-p-implies-natp-width
  ;;          (implies (unsigned-byte-p m data)
  ;;                   (natp m))
  ;;          :hints(("Goal" :in-theory (enable unsigned-byte-p)))
  ;;          :rule-classes :forward-chaining))
  (local (in-theory (enable unsigned-byte-p-implies-natp-width)))

  (local (defret size-of-logrepeat-by-data-size-lemma
           (implies (and (unsigned-byte-p m (loghead width data))
                         (<= m (nfix width))
                         (posp times))
                    (unsigned-byte-p (+ m (- (nfix width))
                                        (* (nfix width) (nfix times)))
                                     reps))
           :hints (("goal" :induct <call>
                    :expand ((:free (data) <call>))))))

  (defret size-of-logrepeat-by-data-size
    (implies (and (unsigned-byte-p m (loghead width data))
                  (<= (+ m (- (nfix width))
                         (* (nfix width) (nfix times))) n)
                  (<= m (nfix width))
                  (natp n))
             (unsigned-byte-p n reps))
    :hints (("goal" :use ((:instance size-of-logrepeat-by-data-size-lemma))
             :in-theory (disable size-of-logrepeat-by-data-size-lemma))))

  (local (defun logbitp-of-logrepeat-ind (n width times)
           (if (zp times)
               (list n width)
             (logbitp-of-logrepeat-ind (- (nfix n) (nfix width)) width (1- (nfix times))))))

  (defret logbitp-of-logrepeat
    (equal (logbitp n reps)
           (and (< (nfix n) (* (nfix width) (nfix times)))
                (logbitp (mod (nfix n) (nfix width)) data)))
    :hints(("Goal" :in-theory (enable bitops::logbitp-of-logapp-split)
            :induct (logbitp-of-logrepeat-ind n width times))))

  (defthm logrepeat-1
    (equal (logrepeat 1 width data)
           (loghead width data))
    :hints (("goal" :expand ((logrepeat 1 width data)) )))


  (local (defun mod-less-ind (n width)
           (declare (Xargs :measure (nfix n)))
           (if (zp n)
               width
             (mod-less-ind (- n (* 2 (acl2::pos-fix width))) width))))

  (local (defthm plus-two-minuses
           (equal (+ (- x) (- x))
                  (- (* 2 x)))))

  (local (defthm mod-when-less-than-half
           (implies (and (natp n) (natp w)
                         (< (mod n (* 2 w)) w))
                    (equal (mod n (* 2 w))
                           (mod n w)))
           :hints (("goal"
                   :induct (mod-less-ind n w))
                   (and stable-under-simplificationp
                        '(:cases ((posp w))))
                   (and stable-under-simplificationp
                        '(:cases ((< n (* 2 w))))))))

  (local (defthm mod-when-greater-than-half
           (implies (and (natp n) (natp w)
                         (<= w (mod n (* 2 w))))
                    (equal (mod n (* 2 w))
                           (+ (mod n w) w)))
           :hints (("goal"
                   :induct (mod-less-ind n w))
                   (and stable-under-simplificationp
                        '(:cases ((posp w))))
                   (and stable-under-simplificationp
                        '(:cases ((< n (* 2 w))))))))

  (defthm logrepeat-2x
    (implies (natp width)
             (equal (logrepeat times (* 2 width) (logapp width data data))
                    (logrepeat (* 2 (nfix times)) width data)))
    :hints (("goal" :in-theory (disable logrepeat)
             :do-not-induct t)
            (bitops::equal-by-logbitp-hammer)))

  ;; (defthm logapp-right-assoc
  ;;   (implies (<= (nfix w2) (nfix w1))
  ;;            (equal (logapp w1 (logapp w2 a b) c)
  ;;                   (logapp w2 a
  ;;                           (logapp (- (nfix w1) (nfix w2)) b c))))
  ;;   :hints ((bitops::logbitp-reasoning)))
  (local (in-theory (enable logapp-right-assoc)))

  (defthm lognot-of-logrepeat
    (equal (lognot (logrepeat times width data))
           (logapp (* (nfix times) (nfix width))
                   (logrepeat times width (lognot data))
                   -1)))

  ;; (local (defthm hack
  ;;          (implies (and (posp width) (posp times)
  ;;                        (integerp wbit0)
  ;;                        (< wbit0 width))
  ;;                   (< wbit0 (* times width)))
  ;;          :hints ((and stable-under-simplificationp
  ;;                       '(:nonlinearp t)))))

  ;; (local (defthm hack2
  ;;          (implies (and (posp width) (integerp times)
  ;;                        (< 1 times)
  ;;                        (integerp wbit0)
  ;;                        (< wbit0 width))
  ;;                   (< wbit0 (+ (- width) (* times width))))
  ;;          :hints ((and stable-under-simplificationp
  ;;                       '(:nonlinearp t)))))

  ;; (local
  ;;  (encapsulate nil
  ;;    (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
  ;;    (defthm mod-of-x-minus-modulus
  ;;      (implies (and (posp a)
  ;;                    (integerp n))
  ;;               (equal (mod (+ n (- a)) a)
  ;;                      (mod n a))))
  ;;    ;; (local (defthm a/a
  ;;    ;;          (implies (posp 
  ;;    ;;          (equal (* a (/ a)) 1)

  ;;    (local (defthm equal-minus-floor
  ;;             (implies (integerp c)
  ;;                      (equal (equal (- (floor a b)) c)
  ;;                             (equal (floor a b) (- c))))))

  ;;    (local (defthm floor-prop
  ;;             (implies (and (posp b)
  ;;                           (integerp a)
  ;;                           (<

  ;;    (defthm mod-lemma
  ;;      (implies (and (posp width)
  ;;                    (integerp times)
  ;;                    (< 1 times)
  ;;                    (integerp n)
  ;;                    (< n (* times width))
  ;;                    (<= (+ (- width) (* times width)) n))
  ;;               (equal (mod n width)
  ;;                      (+ n width (- (* times width)))))
  ;;      :hints(("Goal" :in-theory (enable acl2::linearize-mod))))
  ;;    ))

  ;; (local (in-theory (disable mod-when-greater)))

  (local (defthm equal-of-logapp
           ;; (implies (and (syntaxp (equal width 'width))
           ;;               (syntaxp
           ;;                (or (acl2::rewriting-positive-literal-fn
           ;;                     `(equal (logapp ,width ,a ,b) ,c) mfc state)
           ;;                    (acl2::rewriting-positive-literal-fn
           ;;                     `(equal ,c (logapp ,width ,a ,b)) mfc state))))
                    (equal (equal (logapp width a b) c)
                           (and (integerp c)
                                (equal (loghead width a) (loghead width c))
                                (equal (ifix b) (logtail width c))))
           :hints ((logbitp-reasoning))
           :rule-classes nil))

  (local (defthm blah
           (equal (+ width  (- (* 2 width)) x)
                  (+ (- width) x))))


  (local (defthm lemma
           (implies (AND (NOT (EQUAL TIMES 1))
                         (NOT (ZP TIMES))
                         (NATP WIDTH))
                    (not (< (+ (- WIDTH) (* TIMES WIDTH)) WIDTH)))
           :hints (("goal" :nonlinearp t))))

  (local (in-theory (enable loghead-of-logapp-split
                            logtail-of-logapp-split)))

  (local (defthm loghead-width-of-logrepeat
           (equal (loghead width (logrepeat times width data))
                  (if (zp times)
                      0
                    (loghead width data)))))

  (local (defthm logtail-width-of-logrepeat
           (equal (logtail width (logrepeat times width data))
                  (if (zp times)
                      0
                    (logrepeat (1- times) width data)))))

  (local (defthm lemma2
           (implies (and (integerp times)
                         (< 1 times)
                         (not (equal times 2))
                         (posp width))
                    (< width
                       (+ (- width)
                          (* TIMES width))))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (local (defthm logrepeat-when-zp-width
           (implies (zp width)
                    (Equal (logrepeat times width data) 0))))
           

  (local (defthm blah2
           (implies (integerp w)
                    (equal (+ (- w) (* 2 w)) w))))

  (local (defthm blah3
           (implies (integerp w)
                    (equal (+ w (- (* 2 w))) (- w)))))

  (local (defthm blah4
           (implies (integerp w)
                    (equal (+ (- w) (- w) x)
                           (+ (- (* 2 w)) x)))))
           

  (defretd logrepeat-reverse
    (implies (posp times)
             (equal reps
                    (logapp (* (1- times) (nfix width))
                            (logrepeat (1- times) width data)
                            (loghead width data))))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:cases ((equal times 2))))
            (and stable-under-simplificationp
                 '(:cases ((zp width)))))))


(define logrepeat-power2 ((n natp "Repeat the value 2^n times")
                          (width natp)
                          (data integerp))
  :guard-hints (("goal" :in-theory (enable ash-is-expt-*-x
                                           logrepeat-power2)
                 :expand ((expt 2 n))))
  :enabled t
  (mbe :logic (logrepeat (ash 1 (nfix n)) width data)
       :exec (if (zp n)
                 (loghead width data)
               (logrepeat-power2 (1- n)
                                 (ash width 1)
                                 (logapp width data data)))))

(define fast-logrepeat! ((n natp)
                         (width natp)
                         (data integerp))
  :guard (unsigned-byte-p width data)
  :enabled t
  :guard-hints (("goal" :in-theory (e/d (ash-is-expt-*-x
                                         fast-logrepeat!
                                         logcons)
                                        (logcons-destruct))
                 :do-not-induct t
                 :use ((:instance logcons-destruct (x n))
                       (:instance logrepeat-reverse
                        (times (+ 1 (* 2 (logcdr n))))))
                 :expand ((logbitp 0 n)
                          (logrepeat 0 width data))))
  (mbe :logic (logrepeat n width data)
       :exec (b* (((when (zp n))
                   0)
                  ((when (eql n 1)) data)
                  ((unless (logbitp 0 n))
                   (fast-logrepeat! (logcdr n) (ash width 1)
                                    (logapp width data data)))
                  (rest (fast-logrepeat! (logcdr n) (ash width 1)
                                         (logapp width data data))))
               (logapp (* (1- n) width) rest data))))

(define fast-logrepeat ((n natp)
                        (width natp)
                        (data integerp))
  :enabled t
  (mbe :logic (logrepeat n width data)
       :exec (fast-logrepeat! n width (loghead width data))))
    

