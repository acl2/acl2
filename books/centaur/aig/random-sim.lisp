; Centaur AIG Library
; Copyright (C) 2012 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")

;; Functions for performing fixnum-length data-parallel simulations on AIGs.
;; Much slower than AIGPU, you can be sure :-)
(include-book "aig-equivs")
(include-book "system/random" :dir :system)
(include-book "centaur/bitops/equal-by-logbitp" :dir :system)
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(set-state-ok t)
(local (in-theory (enable* arith-equiv-forwarding)))
(local (in-theory (disable aig-vars)))


(defxdoc aig-random-sim
  :parents (aig-other)
  :short "Functions for randomly vector simulations of Hons @(see aig)s."

  :long "<p>Simulating AIGs on random vectors is useful in algorithms such as
<a
href='http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.66.3434'>fraiging</a>,
to look for nodes that are probably equivalent and might be merged.</p>

<p>Our hons-based @(see aig) representation is not especially efficient or
well-suited for carrying out random simulations, and nowadays @(see aignet) is
a much faster alternative.  Nevertheless, we have developed various routines
for vector-simulations of Hons AIGs.</p>

<p>Note that some of these routines make use of 60-bit natural numbers, which
are fixnums on 64-bit CCL and SBCL.  They may perform quite badly on other
Lisps with smaller fixnum ranges.</p>")


(define n-random-60-bit-nats ((n natp "How many to generate.") state)
  :parents (aig-random-sim)
  :short "Generate a list of 60-bit naturals."
  :long "<p>We just leave this enabled.</p>"
  :enabled t
  (random-list n (ash 1 60) state))


(define init-random-state
  :parents (aig-random-sim)
  :short "Create a fast alist binding each variable to a random 60-bit natural."
  (vars state)
  :returns (mv fal state)
  (b* ((vars (list-fix vars))
       ((mv nums state)
        (n-random-60-bit-nats (length vars) state)))
    (mv (make-fast-alist (pairlis$ vars nums))
        state))
  ///
  (defthm state-p1-of-init-random-state
    (implies (force (state-p1 state))
             (state-p1 (mv-nth 1 (init-random-state vars state))))))


(defsection *60-bit-mask*
  :parents (aig-random-sim)
  :short "The largest 60-bit natural, all ones."
  (defconst *60-bit-mask* (1- (ash 1 60)))

  (local (include-book "arithmetic/top-with-meta" :dir :system))

  (defthm logbitp-of-60-bit-mask
    (implies (natp i)
             (equal (logbitp i *60-bit-mask*)
                    (< i 60)))
    :hints (("goal" :in-theory (enable logbitp**)))))


(define 60-bit-fix (x)
  :parents (aig-random-sim)
  :short "Coerce an object to a 60-bit natural."
  :long "<p>A previous definition for this function was:</p>

@({
    (the (signed-byte 61)
      (if (integerp x)
          (logand x (the (signed-byte 61) *60-bit-mask*))
        0))
})

<p>But the new definition is slightly faster because we avoid the lookup of the
@(see *60-bit-mask*).</p>

<p>We could make this almost twice as fast by redefining it under the hood as
@('(if (typep x '(signed-byte 61)) x 0)'), but I had some trouble getting this
to properly inline, and probably it's best to avoid a ttag for such a minor
optimization.</p>"

  :inline t
  :enabled t
  :guard-hints(("Goal" :in-theory (disable bitops::logand-with-bitmask)))
  (if (integerp x)
      (the (signed-byte 61) (logand x (- (ash 1 60) 1)))
    0))


(define aig-vecsim60
  :parents (aig-random-sim)
  :short "Do a 60-bit wide evaluation of an AIG."
  ((aig "The AIG to simulate.")
   (alst "An alist that should bind the variables of @('aig') to 60-bit
          naturals.  If there are any missing or invalid bindings, we
          just @(see 60-bit-fix) them."))
  :verify-guards nil
  (aig-cases aig
   :true -1
   :false 0
   :var (let ((look (hons-get aig alst)))
                  (if look
                      (60-bit-fix (cdr look))
                    -1))
   :inv
   (the (signed-byte 61)
        (lognot (the (signed-byte 61)
                     (aig-vecsim60 (car aig) alst))))
   :and (let ((a (aig-vecsim60 (car aig) alst)))
          (mbe
           :logic (logand a (aig-vecsim60 (cdr aig) alst))
           :exec (if (= (the (signed-byte 61) a) 0)
                     0
                   (the (signed-byte 61)
                        (logand (the (signed-byte 61) a)
                                (the (signed-byte 61)
                                     (aig-vecsim60 (cdr aig) alst))))))))
  ///
  (defthm aig-vecsim60-60-bits
    (signed-byte-p 61 (aig-vecsim60 aig alst))
    :hints(("Goal" :in-theory (disable bitops::logand-with-bitmask))))

  (verify-guards aig-vecsim60)

  (memoize 'aig-vecsim60 :condition '(and (consp aig) (cdr aig))))



(define logbitp-env60 (i alst)
  :parents (aig-random-sim)
  :short "Given an ALST binding variables to 60-bit integers as in @(see
aig-vecsim60), we extract an ordinary, Boolean-valued alist by using the Ith
bit of each variable."
  :verify-guards nil ;; Not meant to be executed
  (cond ((atom alst)
         nil)
        ((atom (car alst))
         (logbitp-env60 i (cdr alst)))
        (t
         (cons (cons (caar alst)
                     (if (natp i)
                         (if (< i 60)
                             (logbitp i (cdar alst))
                           nil)
                       (logbitp 0 (cdar alst))))
               (logbitp-env60 i (cdr alst))))))

(local (include-book "arithmetic/top-with-meta" :dir :system))

(encapsulate
  ()
  (local (in-theory (enable logbitp-env60)))

  (local
   (progn
     (defthm hons-assoc-equal-logbitp-env60
       (equal (cdr (hons-assoc-equal v (logbitp-env60 i alst)))
              (if (natp i)
                  (and (< i 60)
                       (logbitp i (cdr (hons-assoc-equal v alst))))
                (logbitp 0 (cdr (hons-assoc-equal v alst)))))
       :hints(("Goal" :in-theory (enable hons-assoc-equal))))

     (defthm hons-assoc-equal-logbitp-env60-iff
       (iff (hons-assoc-equal v (logbitp-env60 i alst))
            (hons-assoc-equal v alst)))

     (defthm logbitp-env60-non-natp
       (implies (not (natp i))
                (equal (logbitp-env60 i alst)
                       (logbitp-env60 0 alst))))))

  (defthm logbitp-of-aig-vecsim60
    (equal (aig-eval aig (logbitp-env60 i alst))
           (logbitp i (aig-vecsim60 aig alst)))
    :hints (("Goal" :induct (aig-vecsim60 aig alst)
             :in-theory (enable natp aig-env-lookup
                                aig-vecsim60))
            (and stable-under-simplificationp
                 '(:cases ((natp i)))))))




(defund aig-vecsim60-diff (a b vecs)
  ;; Returns an environment that differentiates between A and B, if that's
  ;; possible.
  (let* ((avec (aig-vecsim60 a vecs))
         (bvec (aig-vecsim60 b vecs))
         (bit  (logbitp-mismatch avec bvec)))
    (logbitp-env60 bit vecs)))

(defthm aig-vecsim60-diff-correct
  (implies (not (equal (aig-vecsim60 a vecs)
                       (aig-vecsim60 b vecs)))
           (not (equal (aig-eval a (aig-vecsim60-diff a b vecs))
                       (aig-eval b (aig-vecsim60-diff a b vecs)))))
  :hints(("Goal"
          :in-theory (e/d (aig-vecsim60-diff)
                          (logbitp-mismatch-correct))
          :use ((:instance logbitp-mismatch-correct
                           (a (aig-vecsim60 a vecs))
                           (b (aig-vecsim60 b vecs))))
          :do-not '(generalize fertilize)
          :do-not-induct t)))

(defthm not-aig-equiv-by-aig-vecsim60
  (implies (not (equal (aig-vecsim60 a vecs)
                       (aig-vecsim60 b vecs)))
           (not (aig-equiv a b)))
  :hints(("Goal"
          :use ((:instance aig-equiv-necc
                           (env (aig-vecsim60-diff a b vecs))
                           (x a) (y b)))
          ;:in-theory (disable aig-equiv-implies-equal-aig-eval-1)
          )))



(defun nonzero-logbitp-witness (x)
  (if (and (integerp x) (< 0 x))
      (1- (integer-length x))
    (integer-length x)))

(local
 (progn
   (defthm logbitp-of-nonzero-logbitp-witness
     (equal (logbitp (nonzero-logbitp-witness x) x)
            (not (equal (ifix x) 0)))
     :hints(("Goal" :in-theory (enable* logbitp** integer-length**
                                        ihsext-inductions)
             :induct (integer-length x))))

   ;; (defthmd nonzero-logbitp-witness-zero
   ;;   (implies (and (integerp x)
   ;;                 (not (equal x 0)))
   ;;            (logbitp (nonzero-logbitp-witness x) x))
   ;;   :hints(("Goal" :in-theory (enable* logbitp** integer-length**
   ;;                                      ihsext-inductions)
   ;;           :induct (integer-length x))))

   ;; (defthmd not-equal-0-by-logbitp
   ;;   (implies (integerp x)
   ;;            (equal (equal x 0)
   ;;                   (not (logbitp (nonzero-logbitp-witness x) x))))
   ;;   :hints(("Goal" :in-theory (enable* logbitp** integer-length**
   ;;                                      ihsext-inductions)
   ;;           :induct (integer-length x))))

   (defthm natp-nonzero-logbitp-witness
     (natp (nonzero-logbitp-witness x))
     :hints(("Goal" :expand ((integer-length x))))
     :rule-classes :type-prescription)

   (in-theory (disable nonzero-logbitp-witness
                       cancel-equal-lognot (lognot)))))


(defun aig-oneoff-random-sim (aig state)
  (b* ((vars (aig-vars aig))
       ((mv alst state) (init-random-state vars state))
       (ans (aig-vecsim60 aig alst)))
    (mv (if (logbitp 0 ans)
            (let ((masked-ans (logxor (logand ans *60-bit-mask*) *60-bit-mask*)))
              (if (eql 0 masked-ans)
                  (list (cons 'true (logbitp-env60 0 alst)))
                (list (cons 'true (logbitp-env60 0 alst))
                      (cons 'false (logbitp-env60
                                    (nonzero-logbitp-witness masked-ans)
                                    alst)))))
          (let ((masked-ans (logand ans *60-bit-mask*)))
            (if (eql 0 masked-ans)
                (list (cons 'false (logbitp-env60 0 alst)))
              (list (cons 'false (logbitp-env60 0 alst))
                    (cons 'true (logbitp-env60
                                 (nonzero-logbitp-witness masked-ans) alst))))))
        state)))


(defthm aig-oneoff-random-sim-correct
  (b* (((mv sim-res &) (aig-oneoff-random-sim aig state))
       (falsep (assoc 'false sim-res))
       (truep (assoc 'true sim-res)))
    (and (implies falsep
                  (not (aig-eval aig (cdr falsep))))
         (implies truep
                  (aig-eval aig (cdr truep)))))
  :hints (("goal" :do-not-induct t)
          (and stable-under-simplificationp
               (let ((concl (car (last clause))))
                 (let ((x (case-match concl
                            (('not ('logbitp ('nonzero-logbitp-witness x . &) . &) . &)
                             x)
                            (('logbitp ('nonzero-logbitp-witness x . &) . &)
                             x))))
                   (and x
                        `(:use ((:instance logbitp-of-nonzero-logbitp-witness
                                 (x ,x)))
                          :in-theory (e/d (b-xor
                                           bitops::logbitp-of-loghead-split)
                                          (logbitp-of-nonzero-logbitp-witness)))))))))


(defun aig-vecsim (aig alst)
  ;; Same as aig-vecsim60, but the vectors in ALST can have any arbitrary
  ;; size.
  (declare (xargs :guard t))
  (aig-cases
   aig
   :true -1
   :false 0
   :var
   (let ((look (hons-get aig alst)))
     (if look
         (ifix (cdr look))
       -1))
   :inv
   (lognot (the integer (aig-vecsim (car aig) alst)))
   :and
   (let ((a (the integer (aig-vecsim (car aig) alst))))
     (mbe :logic (logand a (aig-vecsim (cdr aig) alst))
          :exec (if (= a 0)
                    0
                  (logand a (the integer
                                 (aig-vecsim (cdr aig) alst))))))))

(memoize 'aig-vecsim :condition '(and (consp aig) (cdr aig)))

(defun logbitp-env (i alst)
  ;; Same as logbitp-env60, but the vectors in ALST can have any arbitrary
  ;; size.
  (if (atom alst)
      nil
    (if (atom (car alst))
        (logbitp-env i (cdr alst))
      (cons (cons (caar alst)
                  (logbitp (ifix i) (cdar alst)))
            (logbitp-env i (cdr alst))))))

(local
 (progn
   (defthm hons-assoc-equal-logbitp-env
     (equal (cdr (hons-assoc-equal v (logbitp-env i alst)))
            (logbitp (ifix i) (cdr (hons-assoc-equal v alst))))
     :hints(("Goal" :in-theory (enable hons-assoc-equal))))

   (defthm hons-assoc-equal-logbitp-env-iff
     (iff (hons-assoc-equal v (logbitp-env i alst))
          (hons-assoc-equal v alst)))

   (defthm logbitp-env-non-natp
     (implies (not (natp i))
              (equal (logbitp-env i alst)
                     (logbitp-env 0 alst))))



   (defthm logbitp-integer-length-minus-one
     (implies (and (integerp n) (< 0 n))
              (equal (logbitp (1- (integer-length n)) n) t))
     :hints (("goal" :in-theory (e/d* (integer-length**
                                       logbitp**
                                       ihsext-inductions)
                                     (logcar logcdr))
              :induct (integer-length n))))

   (defthm logbitp-integer-length-negative
     (implies (and (integerp n) (< n 0))
              (equal (logbitp (integer-length n) n) t))
     :hints (("goal" :in-theory (e/d* (integer-length**
                                       logbitp**
                                       ihsext-inductions)
                                     (logcar logcdr))
              :induct (integer-length n))))))


(defthm logbitp-of-aig-vecsim
  (equal (logbitp i (aig-vecsim aig alst))
         (aig-eval aig (logbitp-env i alst)))
  :hints (("Goal" :induct (aig-vecsim aig alst)
           :in-theory (enable natp aig-env-lookup))
          (and stable-under-simplificationp
               '(:cases ((natp i))))))


(defund aig-alist-vecsim (x sig-alist)
  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((atom (car x))
         (aig-alist-vecsim (cdr x) sig-alist))
        (t
         (cons (cons (caar x) (aig-vecsim (cdar x) sig-alist))
               (aig-alist-vecsim (cdr x) sig-alist)))))

(comp t) ; can be needed when host Lisp doesn't automatically compile, e.g., Allegro CL





(make-event
 (mv-let (nums state)
   (n-random-60-bit-nats 10000 state)
   (value `(defconst *10000-random-vecs* ',nums))))



(defun repeat-list-to-length-n (n lst len)
  (if (or (<= (nfix n) (nfix len))
          (eql (nfix len) 0))
      (take n lst)
    (append lst (repeat-list-to-length-n
                 (- (nfix n) (nfix len))
                 lst len))))

(defun init-fake-random-state (vars)
  (make-fal (pairlis$
             vars
             (repeat-list-to-length-n
              (len vars) *10000-random-vecs* 10000))
            nil))

(defun pseudorandom-offset-selection (n vecs nvecs)
  (mod (nfix (nth (mod n nvecs) vecs)) nvecs))

(local (in-theory (disable mod)))

(defthm pseudorandom-offset-selection-less-than-len
  (implies (and (integerp nvecs) (< 0 nvecs))
           (< (pseudorandom-offset-selection n vecs nvecs)
              nvecs))
  :rule-classes :linear)

(defthm pseudorandom-offset-selection-nonneg
  (implies (and (integerp nvecs) (< 0 nvecs))
           (<= 0 (pseudorandom-offset-selection n vecs nvecs)))
  :rule-classes :linear)

(defthm pseudorandom-offset-selection-integer
  (implies (integerp nvecs)
           (integerp (pseudorandom-offset-selection n vecs nvecs)))
  :rule-classes :type-prescription)

(in-theory (disable pseudorandom-offset-selection))


;; Here N is a "random seed" (some integer), vecs is a list of random vectors
;; such as *10000-random-vecs*, and nvars is the number of vectors to
;; select.  Basically this function just chooses a pseudorandom offset into the
;; vectors and assigns the vectors starting at that point.
(defun pseudorandom-vec-selection (n vecs nvars)
  (b* ((nvecs (length vecs))
       (startidx (pseudorandom-offset-selection n vecs nvecs))
       (rem-vars (- (+ startidx nvars) nvecs))
       ((when (eql 0 rem-vars))
        (nthcdr startidx vecs))
       ((unless (< 0 rem-vars))
        (take nvars (nthcdr startidx vecs)))
       (prefix (nthcdr startidx vecs))
       (rest (repeat-list-to-length-n rem-vars vecs nvecs)))
    (append prefix rest)))



(defthm len-first-n-ac
  (equal (len (first-n-ac n lst acc))
         (+ (nfix n) (len acc))))

(defthm len-repeat-list-to-length-n
  (implies (and (consp lst)
                (equal (len lst) len))
           (equal (len (repeat-list-to-length-n n lst len))
                  (nfix n))))

(defthm equal-len-0-is-atom
  (equal (equal (len x) 0)
         (atom x)))

(defthm len-pseudorandom-vec-selection
  (implies (and (consp vecs) (integerp nvars))
           (equal (len (pseudorandom-vec-selection n vecs nvars))
                  (nfix nvars)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (length)
                           (pseudorandom-offset-selection-less-than-len
                            pseudorandom-offset-selection-nonneg))
           :use ((:instance pseudorandom-offset-selection-less-than-len
                            (nvecs (len vecs)))
                 (:instance pseudorandom-offset-selection-nonneg
                            (nvecs (len vecs))))))
  :otf-flg t)



(defun aig-alist-vecsim60 (al vecs)
  (declare (xargs :guard t))
  (cond ((atom al)
         nil)
        ((atom (car al))
         (aig-alist-vecsim60 (cdr al) vecs))
        (t
         (cons (cons (caar al) (aig-vecsim60 (cdar al) vecs))
               (aig-alist-vecsim60 (cdr al) vecs)))))

(defun faig-alist-vecsim60 (al vecs)
  (declare (xargs :guard t))
  (cond ((atom al)
         nil)
        ((atom (car al))
         (faig-alist-vecsim60 (cdr al) vecs))
        (t
         (b* ((name (caar al))
              (faig (cdar al))
              ((cons onset offset)
               (if (atom faig)
                   (prog2$ (er hard? 'faig-alist-vecsim60
                               "Alleged FAIG for ~x0 is not even a consp." name)
                           (cons nil nil))
                 faig))
              (new-faig (cons (aig-vecsim60 onset vecs)
                              (aig-vecsim60 offset vecs))))
           (cons (cons name new-faig)
                 (faig-alist-vecsim60 (cdr al) vecs))))))





; AIG-RSIM60 is an alternative to AIG-VECSIM60 that makes it cheaper to do
; random simulations with many vectors.
;
; In particular, if there are K variables and we want to generate N random
; vec-alists to feed to aig-vecsim60, we would need to build N fast-alists of
; size K, and populate them with random numbers.  This is a lot of overhead.
;
; With AIG-RSIM60, we instead begin by building two structures:
;
;   - VMAP, a fast-alist that maps the AIG variables to natural numbered
;     indicies 0, 1, ..., K-1
;
;   - ARR, an ordinary ACL2 Array that contains K + N random integers
;
; Then, in the Ith simulation, the value of variable V is ARR[I + VMAP[V]].  In
; other words, the 0th variable is ARR[0] in the first simulation, ARR[1] in
; the next, and so on.  Even though we're reusing random numbers, we're
; assigning them to different variables.
;
; This approach reduces our overhead from building N fast alists of size K to
; building a single fast alist of size K and a single array of size K+N.
;
; One disadvantage of this approach is that individual executions might be
; slightly slower due to the array lookups.  But this overhead only impacts
; looking up individual variables at the tips of the AIG, and is probably very
; small compared to memoizing the AND nodes in the AIG.
;
; To minimize memoization overhead, we pack the current simulation number,
; along with the VMAP, ARR, and the length of the array into a structure
; named RENV.  The format of the RENV is:
;
;    ((SIMULATION-NUMBER . VMAP) . (ARR . ARRLEN))
;
; The name of the array is always 'aig-rsim60-arr.

(defund aig-rsim60-renvp (x)
  (declare (xargs :guard t))
  (and (consp x)
       (consp (car x))
       (consp (cdr x))
       (let ((sim-number (caar x))
             (arr        (cadr x))
             (len        (cddr x)))
         (and (natp sim-number)
              (array1p 'aig-rsim60-arr arr)
              (equal (car (dimensions 'aig-rsim60-arr arr)) len)))))

(local (in-theory (enable aig-rsim60-renvp)))



(defund aig-rsim60-free-renv (x)
  (declare (xargs :guard (aig-rsim60-renvp x)))
  (progn$
   (fast-alist-free (cdar x))
   (flush-compress 'aig-rsim60-arr)
   nil))



(defsection aig-rsim60-initialize-renv

; (AIG-RSIM60-INITIALIZE-RENV N VARS STATE) --> (MV RENV STATE)
;
; We construct a new RENV that can be used to perform N random simulations of
; AIGs involving VARS.  This is cumbersome because of ACL2 array nonsense.

  (local (include-book "data-structures/array1" :dir :system))

  (defund aig-rsim60-initialize-vmap-aux (i vars map)
    (declare (xargs :guard (natp i)))
    (if (atom vars)
        map
      (let ((map (hons-acons (car vars) i map)))
        (aig-rsim60-initialize-vmap-aux (+ 1 i) (cdr vars) map))))

  (defund aig-rsim60-initialize-vmap (vars len)
    (declare (xargs :guard t))
    (aig-rsim60-initialize-vmap-aux 0 vars len))

  (defund aig-rsim60-initialize-array-aux (len state alist)
    ;; Initializes ARR[0] ... ARR[len-1]
    (declare (xargs :guard (natp len)))
    (if (zp len)
        (mv alist state)
      (b* (((mv elem state) (random$ (ash 1 60) state))
           (len             (- len 1))
           (alist           (cons (cons len elem) alist)))
        (aig-rsim60-initialize-array-aux len state alist))))

  (local (defthm state-p1-of-aig-rsim60-initialize-array-aux
           (implies (state-p1 state)
                    (state-p1 (mv-nth 1 (aig-rsim60-initialize-array-aux len state alist))))
           :hints(("Goal" :in-theory (enable aig-rsim60-initialize-array-aux)))))

  (local (defthm alistp-of-aig-rsim60-initialize-array-aux
           (implies (alistp alist)
                    (alistp
                     (mv-nth 0 (aig-rsim60-initialize-array-aux len1 state alist))))
           :hints(("Goal" :in-theory (enable aig-rsim60-initialize-array-aux)))))

  (local (defthm bounded-integer-alistp-of-aig-rsim60-initialize-array-aux
           (implies
            (and (bounded-integer-alistp alist len2)
                 (natp len1)
                 (natp len2)
                 (<= len1 len2))
            (bounded-integer-alistp
             (mv-nth 0 (aig-rsim60-initialize-array-aux len1 state alist))
             len2))
           :hints(("Goal"
                   :in-theory (enable aig-rsim60-initialize-array-aux
                                      bounded-integer-alistp)))))

  (defund aig-rsim60-initialize-array (len state)
    (declare (xargs :guard (posp len)))
    (b* ((len
          (if (< len *maximum-positive-32-bit-integer*)
              len
            (prog2$
             (er hard? 'aig-rsim60-initialize-array
                 "ACL2 refuses to allow arrays beyond 2^32 bits, and you ~
                probably don't want to try to make one anyway.")
             1)))
         ((mv alist state)
          (aig-rsim60-initialize-array-aux len state nil))
         (alist (cons (list :HEADER
                            :DIMENSIONS (list len)
                            :MAXIMUM-LENGTH (+ 1 len)
                            :DEFAULT 0
                            :NAME 'aig-rsim60-arr)
                      alist))
         (arr (compress1 'aig-rsim60-arr alist)))
      (mv arr len state)))

  (local (defthm state-p1-of-aig-rsim60-initialize-array
           (implies (state-p1 state)
                    (state-p1 (mv-nth 2 (aig-rsim60-initialize-array len state))))
           :hints(("Goal" :in-theory (enable aig-rsim60-initialize-array)))))

  (local (defthm arrayp1-of-aig-rsim60-initialize-array
           (implies (posp len)
                    (array1p 'aig-rsim60-arr (mv-nth 0 (aig-rsim60-initialize-array len state))))
           :hints(("Goal" :in-theory (e/d (aig-rsim60-initialize-array)
                                          (compress1))))))

  (local (defthm dimensions-of-aig-rsim60-initialize-array
           (implies (posp len)
                    (equal (dimensions name (mv-nth 0 (aig-rsim60-initialize-array len state)))
                           (list (mv-nth 1 (aig-rsim60-initialize-array len state)))))
           :hints(("Goal" :in-theory (enable aig-rsim60-initialize-array)))))

  (defund aig-rsim60-initialize-renv (n vars state)
    (declare (xargs :guard (natp n)))
    (b* ((n      (nfix n))
         (k      (len vars))
         ;; we make the vmap hash table 2x the length of vars, so that we
         ;; hopefully have very few collisions... probably silly
         (vmap   (aig-rsim60-initialize-vmap vars (* k 2)))
         ;; adding 1 lets us use natp as a guard
         (arrlen (+ 1 k n))
         ((mv arr true-arrlen state)
          (aig-rsim60-initialize-array arrlen state))
         (renv (cons (cons 0 vmap)
                     (cons arr true-arrlen))))
      (mv renv state)))

  (defthm state-p1-of-aig-rsim60-initialize-renv
    (implies (force (state-p1 state))
             (state-p1 (mv-nth 1 (aig-rsim60-initialize-renv n vars state))))
    :hints(("Goal" :in-theory (enable aig-rsim60-initialize-renv))))

  (defthm aig-rsim60-renvp-of-aig-rsim60-initialize-renv
    (aig-rsim60-renvp (mv-nth 0 (aig-rsim60-initialize-renv n vars state)))
    :hints(("Goal" :in-theory (e/d (aig-rsim60-initialize-renv)
                                   (array1p dimensions))))))



(defsection aig-rsim60-next-simulation

; (AIG-RSIM60-NEXT-SIMULATION RENV) --> RENV'
;
; We just increment the simulation number in the RENV.

  (defund aig-rsim60-next-simulation (renv)
    (declare (xargs :guard (aig-rsim60-renvp renv)
                    :guard-hints(("Goal" :in-theory (enable aig-rsim60-renvp)))))
    (cons (cons (+ 1 (caar renv)) (cdar renv))
          (cdr renv)))

  (local (in-theory (enable aig-rsim60-next-simulation)))

  (defthm aig-rsim60-renvp-of-aig-rsim60-next-simulation
    (implies (aig-rsim60-renvp renv)
             (aig-rsim60-renvp (aig-rsim60-next-simulation renv)))))





(defsection aig-rsim60

; (AIG-RSIM60 AIG RENV) --> Signature
;
; We show that if (AIG-RSIM60 A RENV) != (AIG-RSIM60 B RENV), then A and B are
; not equivalent in the sense of AIG-EQUIV.

  (defund aig-rsim60-lookup (var renv)
    (declare (xargs :guard (aig-rsim60-renvp renv)))
    (b* ((sim-number (caar renv))
         (vmap       (cdar renv))
         (arr        (cadr renv))
         (arrlen     (cddr renv))
         (vmap[var]  (cdr (hons-get var vmap)))
         ;; Special extension: if the varmap binds the variable to T or NIL,
         ;; we assume you want it always T or always NIL.
         ((when (eq vmap[var] nil))
          0)
         ((when (eq vmap[var] t))
          (60-bit-fix -1))
         ;; Otherwise, we look up the value in the random-number array at
         ;; the appropriate offset.
         (idx        (+ sim-number (nfix vmap[var])))
         (idx        (if (< idx arrlen)
                         idx
                       0)))
      (60-bit-fix (aref1 'aig-rsim60-arr arr idx))))

  (defthm natp-aig-rsim60-lookup
    (natp (aig-rsim60-lookup var renv))
    :hints(("Goal" :in-theory (enable aig-rsim60-lookup)))
    :rule-classes :type-prescription)

  (defund aig-rsim60 (aig renv)
    (declare (xargs :guard (aig-rsim60-renvp renv)
                    :verify-guards nil))
    (aig-cases
     aig
     :true -1
     :false 0
     :var
     (aig-rsim60-lookup aig renv)
     :inv
     (the (signed-byte 61)
          (lognot (the (signed-byte 61)
                       (aig-rsim60 (car aig) renv))))
     :and
     (let ((a (aig-rsim60 (car aig) renv)))
       (mbe
        :logic (logand a (aig-rsim60 (cdr aig) renv))
        :exec (if (= (the (signed-byte 61) a) 0)
                  0
                (the (signed-byte 61)
                     (logand (the (signed-byte 61) a)
                             (the (signed-byte 61)
                                  (aig-rsim60 (cdr aig) renv)))))))))

  (defthm aig-rsim60-lookup-60-bits
    (unsigned-byte-p 60 (aig-rsim60-lookup var renv))
    :hints(("Goal" :in-theory (e/d (aig-rsim60-lookup)
                                   (bitops::logand-with-bitmask)))))

  (defthm aig-rsim60-60-bits
    (signed-byte-p 61 (aig-rsim60 aig renv))
    :hints(("Goal" :in-theory (e/d (aig-rsim60)
                                   (bitops::logand-with-bitmask
                                    aig-rsim60-lookup-60-bits))
            :induct t)
           (and stable-under-simplificationp
                '(:use ((:instance aig-rsim60-lookup-60-bits
                         (var aig)))))))

  (verify-guards aig-rsim60)

  (memoize 'aig-rsim60 :condition '(and (consp aig) (cdr aig)))


  (local (defthm logbitp-beyond-60-of-aig-rsim60-lookup
           (implies (and (natp i)
                         (<= 60 i))
                    (not (logbitp i (aig-rsim60-lookup aig renv))))
           :hints(("Goal" :in-theory (enable aig-rsim60-lookup)))))

  (defund aig-rsim60-env (vars renv)
    (if (atom vars)
        nil
      (hons-acons (car vars)
                  (aig-rsim60-lookup (car vars) renv)
                  (aig-rsim60-env (cdr vars) renv))))

  (defthm hons-assoc-equal-of-aig-rsim60-env
    (equal (hons-assoc-equal v (aig-rsim60-env vars renv))
           (and (member-equal v vars)
                (cons v (aig-rsim60-lookup v renv))))
    :hints(("Goal" :in-theory (enable aig-rsim60-env))))

  ;; ;; Copied from random-sim.  BOZO consider unlocalizing these
  ;; (local
  ;;  (progn
  ;;    (local (include-book "arithmetic/top-with-meta" :dir :system))

  ;;    (defthm hons-assoc-equal-logbitp-env60
  ;;      (equal (cdr (hons-assoc-equal v (logbitp-env60 i alst)))
  ;;             (if (natp i)
  ;;                 (and (< i 60)
  ;;                      (logbitp i (cdr (hons-assoc-equal v alst))))
  ;;               (logbitp 0 (cdr (hons-assoc-equal v alst)))))
  ;;      :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  ;;    (defthm hons-assoc-equal-logbitp-env60-iff
  ;;      (iff (hons-assoc-equal v (logbitp-env60 i alst))
  ;;           (hons-assoc-equal v alst)))

  ;;    (defthm logbitp-env60-non-natp
  ;;      (implies (not (natp i))
  ;;               (equal (logbitp-env60 i alst)
  ;;                      (logbitp-env60 0 alst))))))


  (local (defthmd logbitp-when-unsigned-byte-p-out-of-bounds
           (implies (and (unsigned-byte-p n x)
                         (<= n (nfix m)))
                    (not (logbitp m x)))
           :hints(("Goal" :in-theory (e/d* (logbitp**
                                            unsigned-byte-p**
                                            ihsext-inductions)
                                           (unsigned-byte-p))))))

  (local (defthm logbitp-out-of-bounds-of-aig-rsim60-lookup
           (implies (<= 60 (nfix i))
                    (not (logbitp i (aig-rsim60-lookup aig renv))))
           :hints (("goal" :use ((:instance
                                  logbitp-when-unsigned-byte-p-out-of-bounds
                                  (n 60) (m i) (x (aig-rsim60-lookup aig
                                                                     renv))))
                    :in-theory (e/d () (unsigned-byte-p))))))

  (local (defthm logbitp-of-aig-rsim60-general
           (implies (subsetp-equal (aig-vars aig) vars)
                    (equal (logbitp i (aig-rsim60 aig renv))
                           (aig-eval aig (logbitp-env60 i (aig-rsim60-env vars renv)))))
           :hints(("Goal"
                   :do-not '(generalize fertilize)
                   :induct (aig-rsim60 aig renv)
                   :in-theory (enable aig-rsim60 aig-vars aig-eval aig-env-lookup
                                      aig-vecsim60
                                      subsetp-equal
                                      bitops::logbitp-of-loghead-split)))))

  (defthm logbitp-of-aig-rsim60
    (equal (logbitp i (aig-rsim60 aig renv))
           (aig-eval aig (logbitp-env60 i (aig-rsim60-env (aig-vars aig) renv))))
    :hints(("Goal"
            :in-theory (disable logbitp-of-aig-rsim60-general)
            :use ((:instance logbitp-of-aig-rsim60-general
                             (vars (aig-vars aig)))))))


  (local (defund aig-rsim60-diff (a b vars renv)
           ;; Returns an environment that differentiates between A and B, if that's
           ;; possible.
           (let* ((avec (aig-rsim60 a renv))
                  (bvec (aig-rsim60 b renv))
                  (bit  (logbitp-mismatch avec bvec)))
             (logbitp-env60 bit (aig-rsim60-env vars renv)))))

  (local (defthm aig-rsim60-diff-correct-general
           ;; Generalized version that fixes up the problem with having two
           ;; sets of vars.
           (implies (and (subsetp-equal (aig-vars a) vars)
                         (subsetp-equal (aig-vars b) vars)
                         (not (equal (aig-rsim60 a renv)
                                     (aig-rsim60 b renv))))
                    (not (equal (aig-eval a (aig-rsim60-diff a b vars renv))
                                (aig-eval b (aig-rsim60-diff a b vars renv)))))
           :hints(("Goal"
                   :in-theory (e/d (aig-rsim60-diff)
                                   (logbitp-mismatch-correct
                                    logbitp-of-aig-rsim60))
                   :use ((:instance logbitp-mismatch-correct
                                    (a (aig-rsim60 a renv))
                                    (b (aig-rsim60 b renv))))
                   :do-not '(generalize fertilize)
                   :do-not-induct t))))

  (local (defthm aig-rsim60-diff-correct
           (implies (not (equal (aig-rsim60 a renv)
                                (aig-rsim60 b renv)))
                    (not (equal (aig-eval a (aig-rsim60-diff a b (append (aig-vars a)
                                                                         (aig-vars b))
                                                             renv))
                                (aig-eval b (aig-rsim60-diff a b (append (aig-vars a)
                                                                         (aig-vars b))
                                                             renv)))))))

  (defthm not-aig-equiv-by-aig-rsim60
    (implies (not (equal (aig-rsim60 a renv)
                         (aig-rsim60 b renv)))
             (not (aig-equiv a b)))
    :hints(("Goal"
            :use ((:instance aig-equiv-necc
                             (env (aig-rsim60-diff a b (append (aig-vars a)
                                                               (aig-vars b))
                                                   renv))
                             (x a) (y b)))
            ;:in-theory (disable aig-equiv-implies-equal-aig-eval-1)
            ))))


(defsection aig-rsim60-bind-variable

  (defund aig-rsim60-get-variable-binding (var renv)
    (declare (xargs :guard (aig-rsim60-renvp renv)))
    (b* ((vmap (cdar renv)))
      (cdr (hons-get var vmap))))


  (defund aig-rsim60-bind-variable (var val renv)
    ;; Bind var to val in the variable map.
    ;; Practically speaking, val should be either:
    ;;   (1) a boolean, to say that you want this bound to a constant, or
    ;;   (2) an index into the renv, to say you want this variable to assume
    ;;       random values.
    ;;
    ;; NOTE: this steals the hash table for the variable map!  If you are going
    ;; to do this temporarily, you probably want to first extract the old value
    ;; using aig-rsim60-get-variable-binding, and then restore the old binding
    ;; later.
    (declare (xargs :guard (aig-rsim60-renvp renv)))
    (b* ((sim-number (caar renv))
         (vmap       (cdar renv))
         (arr        (cadr renv))
         (arrlen     (cddr renv))
         (vmap       (hons-acons var val vmap)))
      (cons (cons sim-number vmap)
            (cons arr arrlen))))

  (defthm aig-rsim60-renvp-of-aig-rsim60-bind-variable
    (implies (force (aig-rsim60-renvp renv))
             (aig-rsim60-renvp (aig-rsim60-bind-variable var val renv)))
    :hints(("Goal" :in-theory (enable aig-rsim60-bind-variable)))))




(defsection aig-rsim60-mk-renv-list

  (defund aig-rsim60-renv-listp (x)
    (declare (xargs :guard t))
    (if (atom x)
        (eq x nil)
      (and (aig-rsim60-renvp (car x))
           (aig-rsim60-renv-listp (cdr x)))))

  (local (in-theory (disable aig-rsim60-renvp)))

  (defund aig-rsim60-mk-renv-list (max-random-sim renv)
    (declare (xargs :guard (and (natp max-random-sim)
                                (aig-rsim60-renvp renv))))
    (if (zp max-random-sim)
        (list renv)
      (cons renv
            (aig-rsim60-mk-renv-list
             (1- max-random-sim)
             (aig-rsim60-next-simulation renv)))))

  (local (in-theory (enable aig-rsim60-renv-listp
                            aig-rsim60-mk-renv-list)))

  (defthm aig-rsim60-renv-listp-of-mk-renv-list
    (implies (aig-rsim60-renvp x)
             (aig-rsim60-renv-listp
              (aig-rsim60-mk-renv-list n x))))

  (defund aig-rsim60-init-renv-list (max-random-sim vars state)
    (declare (xargs :guard (natp max-random-sim)
                    :stobjs state))
    (b* (((mv renv state) (aig-rsim60-initialize-renv
                           max-random-sim vars state)))
      (mv (aig-rsim60-mk-renv-list max-random-sim renv)
          state)))

  (local (in-theory (enable aig-rsim60-init-renv-list)))

  (defthm aig-rsim60-renv-listp-of-init-renv-list
    (aig-rsim60-renv-listp
     (mv-nth 0 (aig-rsim60-init-renv-list max-random-sim vars state))))

  (defthm state-p1-of-aig-rsim60-init-renv-list
    (implies (force (state-p1 state))
             (state-p1 (mv-nth 1 (aig-rsim60-init-renv-list n vars state)))))

  (defthm len-aig-rsim60-mk-renv-list
    (equal (len (aig-rsim60-mk-renv-list n x))
           (+ 1 (nfix n))))

  (defthm len-aig-rsim60-init-renv-list
    (equal (len (mv-nth 0 (aig-rsim60-init-renv-list n vars state)))
           (+ 1 (nfix n)))))


(defsection aig-rsim60-satisfying-assign

  (defund aig-rsim60-renv-to-env1 (vmap bit renv)
    (declare (xargs :guard (and (natp bit)
                                (aig-rsim60-renvp renv))
                    :guard-hints (("goal" :in-theory
                                   (disable aig-rsim60-renvp)))))
    (if (atom vmap)
        nil
      (if (atom (car vmap))
          (aig-rsim60-renv-to-env1 (cdr vmap) bit renv)
        (cons (cons (caar vmap)
                    (logbitp bit (aig-rsim60-lookup (caar vmap) renv)))
              (aig-rsim60-renv-to-env1 (cdr vmap) bit renv)))))

  (defund aig-rsim60-renv-to-env (bit renv)
    (declare (Xargs :guard (and (natp bit)
                                (aig-rsim60-renvp renv))))
    (b* ((vmap       (cdar renv)))
      (aig-rsim60-renv-to-env1 vmap bit renv)))

  (local (defthm integer-length-0-when-natp
           (implies (natp x)
                    (equal (equal (integer-length x) 0)
                           (equal x 0)))
           :hints(("Goal" :expand ((integer-length x))))))

  ;; BOZO prove this correct


  ;; If result is (aig-rsim60 aig renv), then this pulls out an AIG evaluation
  ;; environment from renv such that (aig-eval aig res).
  (defund aig-rsim60-satisfying-assign (result renv)
    (declare (xargs :guard (aig-rsim60-renvp renv)
                    :guard-hints (("goal" :in-theory
                                   (disable aig-rsim60-renvp)))))
    ;; The result is a signed-byte-p 61, but may be positive or negative.  We
    ;; 60-bit-fix it to make it positive so that we can use integer-length to
    ;; find a 1-bit.
    (b* ((res60 (60-bit-fix result))
         ;; bozo.  Fails when the result is not actually a satisfying
         ;; assignment.
         ((when (eql res60 0))
          (cw "Problem in aig-rsim60-satisfying-assign -- no satisfying assignment. ~x0~%"
              result)
          nil)
         (one-bit (1- (integer-length res60))))
      (aig-rsim60-renv-to-env one-bit renv))))
