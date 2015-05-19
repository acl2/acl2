; Bit Blasting ACL2 Theorems - Supporting Materials
; Copyright (C) 2011 by Centaur Technology
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
; Original authors: Sol Swords and Jared Davis {sswords,jared}@centtech.com



; NOTES.
;
; This script contains experiments and code in support of "Bit Blasting ACL2
; Theorems", submitted to the ACL2 Workshop 2011.
;
; This is NOT a proper ACL2 book and should not be expected to certify.
;
; Test machine information.  (fv-1)
;   - 8-core Intel Xeon E5450 @ 3.00 GHz
;   - 64 GB of memory (but our examples are not particularly memory intensive)
;   - 64-bit Linux 2.6.18-164
;   - ACL2 from SVN revision 390
;   - CCL from SVN revision 14718
;   - GL from ACL2-Books SVN revision 817


; -----------------------------------------------------------------------------
;
;                              PRELIMINARY
;                          SUPPORTING UTILITIES
;
; -----------------------------------------------------------------------------

(include-book "centaur/gl/gl" :dir :system)
(assign verbose-theory-warning nil)

(defun numlist (start by n)
  (declare (xargs :guard (and (acl2-numberp start)
                              (acl2-numberp by)
                              (natp n))))
  (if (zp n)
      nil
      (cons start
            (numlist (+ start by) by (1- n)))))

(defun g-int (start by n)
  (g-number (list (numlist start by n))))

(defun 32* (x y)
  (logand (* x y) (1- (expt 2 32))))

(defun 64* (x y)
  (logand (* x y) (1- (expt 2 64))))

(defun 128* (x y)
  (logand (* x y) (1- (expt 2 128))))

(defun 128+ (x y)
  (logand (+ x y) (1- (expt 2 128))))

(defun 128-fix (x)
  (logand x (1- (expt 2 128))))


; For timing purposes, we often work in a fresh session to avoid reusing any
; memoized results.  It is useful to leave this I-AM-HERE marker here, so that
; we can reload the file just up to here.

(i-am-here)


; -----------------------------------------------------------------------------
;
;                             (INTRODUCTION)
;                            FAST-LOGCOUNT-32
;
; -----------------------------------------------------------------------------


; We initially did not realize we had to use a 32-bit multiply.

(defun fast-logcount-32-wrong (v)
  (let* ((v (- v (logand (ash v -1) #x55555555)))
         (v (+ (logand v #x33333333)
               (logand (ash v -2) #x33333333))))
    (ash (* (logand (+ v (ash v -4))
                    #xF0F0F0F)
              #x1010101)
         -24)))

; But it still works for several test-cases.

(fast-logcount-32-wrong 0)
(fast-logcount-32-wrong 1)
(fast-logcount-32-wrong #b111)
(fast-logcount-32-wrong #b10111)


; The attempted GL proof fails and gives us some counterexamples.

(def-gl-thm fast-logcount-32-wrong-correct
  :hyp (unsigned-byte-p 32 x)
  :concl (equal (fast-logcount-32-wrong x)
                (logcount x))
  :g-bindings
  `((x ,(g-number (list (numlist 0 1 33))))))




; Here is the corrected definition.  It turns out we did not have to use
; 32-bit addition and subtraction.

(defun fast-logcount-32 (v)
  (let* ((v (- v (logand (ash v -1) #x55555555)))
         (v (+ (logand v #x33333333)
               (logand (ash v -2) #x33333333))))
    (ash (32* (logand (+ v (ash v -4))
                      #xF0F0F0F)
              #x1010101)
         -24)))


; With the correct definition, the GL proof takes 0.09 seconds, in a fresh
; ACL2 session.

(def-gl-thm fast-logcount-32-correct
  :hyp (unsigned-byte-p 32 x)
  :concl (equal (fast-logcount-32 x)
                (logcount x))
  :g-bindings
  `((x ,(g-int 0 1 33))))




; -----------------------------------------------------------------------------
;
;                             (INTRODUCTION)
;                   FAST-LOGCOUNT-32 BY EXHAUSTIVE TESTING
;
; -----------------------------------------------------------------------------

; We aren't going to bother with the lemmas to prove that our testers are
; correct, and we'll just skip the proofs of their guards.

; With guards but no fixnum optimizations, it takes 249 seconds.

(skip-proofs
 (defun guard-32* (x y)
   (declare (xargs :guard (and (natp x)
                               (natp y))))
   (logand (* x y) (1- (expt 2 32)))))

(skip-proofs
 (defun guard-fast-logcount-32 (v)
   (declare (xargs :guard (natp v)))
   (let* ((v (- v (logand (ash v -1) #x55555555)))
          (v (+ (logand v #x33333333)
                (logand (ash v -2) #x33333333))))
     (ash (guard-32* (logand (+ v (ash v -4)) #xF0F0F0F)
                     #x1010101)
          -24))))

(skip-proofs
 (defun test (n)
   (declare (xargs :guard (natp n)
                   :ruler-extenders :all))
   (and (equal (guard-fast-logcount-32 n)
               (logcount n))
        (if (mbe :logic (zp n)
                 :exec (= n 0))
            t
          (test (- n 1))))))

(time$ (test (1- (expt 2 32)))) ;; 249 sec



; If we add fixnum optimizations the time drops to 143 seconds.  The guard
; proofs probably wouldn't be too bad with the right arithmetic books.

(defmacro un (x)
  `(the (unsigned-byte 32) ,x))

(defmacro un32* (x y)
  `(un (logand (un (* (un ,x) (un ,y)))
               (1- (expt 2 32)))))

(skip-proofs
 (defun opt-fast-logcount-32 (v)
   (declare (type (unsigned-byte 32) v))
   (let* ((v (un (- v (un (logand (un (ash v -1)) #x55555555)))))
          (v (un (+ (un (logand v #x33333333))
                    (un (logand (un (ash v -2)) #x33333333))))))
     (un (ash (un32* (logand (+ v (un (ash v -4))) #xF0F0F0F)
                     #x1010101)
              -24)))))

(skip-proofs
 (defun test2 (n)
   (declare (type (unsigned-byte 32) n))
   (and (= (un (opt-fast-logcount-32 n))
           (un (logcount n)))
        (if (= n 0)
            t
          (test2 (un (- n 1)))))))

(time$ (test2 (1- (expt 2 32)))) ;; 143 sec





; We were surprised this took 143 seconds since the UTF-8 example, which seems
; harder, only takes 67 seconds.  So we started looking into its performance.

; We use MY-PROG2$ here because we found out that ordinary PROG2$ is slow!  It
; turns out that it's binding the special variable *aokp*, and binding specials
; is a bit expensive.  Maybe PROG2$ should be changed NOT to do this binding,
; and some alternative to PROG2$ should be introduced that does the *aokp*
; binding for use in attachments.

(defmacro my-prog2$ (x y)
  `(let* ((ignore-me-my-prog2$-do-not-use-elsewhere ,x))
     (declare (ignore ignore-me-my-prog2$-do-not-use-elsewhere))
     ,y))


; Test to see how much of the time is due to fast-logcount-32.
; This took 73.05 seconds with prog2$, 43.18 seconds with my-prog2$

(skip-proofs
 (defun test-flc (n)
   (declare (type (unsigned-byte 32) n))
   (my-prog2$
    (un (opt-fast-logcount-32 n))
    (if (= n 0)
        t
      (test-flc (un (- n 1)))))))

(time$ (test-flc (1- (expt 2 32))))



; Test to see how much of the time is due to logcount.
; This took 150.12 seconds with prog2$, 116.39 seconds with my-prog2$.

(skip-proofs
 (defun test-lc (n)
   (declare (type (unsigned-byte 32) n))
   (my-prog2$ (un (logcount n))
              (if (= n 0)
                  t
                (test-lc (un (- n 1)))))))

(time$ (test-lc (1- (expt 2 32))))

; So it seems like the basic moral of the story is that LOGCOUNT is pretty
; expensive in our current version of CCL, and our user-level, optimized
; fast-logcount-32 function is in fact faster.  It looks like SBCL has a much
; faster version of LOGCOUNT, but we didn't bother to test other Lisps.




; -----------------------------------------------------------------------------
;
;                             (INTRODUCTION)
;                64- AND 128-BIT VERSIONS OF FAST-LOGCOUNT
;
; -----------------------------------------------------------------------------

; GL can also prove the correctness of 64-bit and 128-bit versions of the
; algorithm, where exhaustive testing obviously wouldn't work.

; We ran these in a fresh session to be sure that no memoized results were
; being reused.  The time needed for the 64-bit case is 0.18 seconds, and
; for the 128-bit case is 0.58 seconds.

(defun fast-logcount-64 (v)
  (let* ((v (- v (logand (ash v -1) #x5555555555555555)))
         (v (+ (logand v #x3333333333333333)
               (logand (ash v -2) #x3333333333333333))))
    (ash (64* (logand (+ v (ash v -4))
                      #x0F0F0F0F0F0F0F0F)
              #x0101010101010101)
         -56)))

;; This takes 0.13 seconds.

(def-gl-thm fast-logcount-64-correct
  :hyp (unsigned-byte-p 64 x)
  :concl (equal (fast-logcount-64 x)
                (logcount x))
  :g-bindings
  `((x ,(g-int 0 1 65))))


(defun 128* (x y)
  (logand (* x y) (1- (expt 2 128))))

(defun fast-logcount-128 (v)
  (let* ((v (- v (logand (ash v -1) #x55555555555555555555555555555555)))
         (v (+ (logand v #x33333333333333333333333333333333)
               (logand (ash v -2) #x33333333333333333333333333333333))))
    (ash (128* (logand (+ v (ash v -4))
                      #x0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F)
              #x01010101010101010101010101010101)
         -120)))

(def-gl-thm fast-logcount-128-correct
  :hyp (unsigned-byte-p 128 x)
  :concl (equal (fast-logcount-128 x)
                (logcount x))
  :g-bindings
  `((x ,(g-int 0 1 129))))



; -----------------------------------------------------------------------------
;
;                             (INTRODUCTION)
;                             UTF8 DECODING
;
; -----------------------------------------------------------------------------

; This book has the hard lemma:

(include-book "unicode/utf8-decode" :dir :system)

; We just typed it in, and GL proves it immediately.

(def-gl-thm lemma-5-by-gl
 :hyp (utf8-combine4-guard x1 x2 x3 x4)
 :concl (and
         (uchar? (utf8-combine4 x1 x2 x3 x4))
         (utf8-table35-ok? (utf8-combine4 x1 x2 x3 x4)
                           (list x1 x2 x3 x4))
         (utf8-table36-ok? (utf8-combine4 x1 x2 x3 x4)
                           (list x1 x2 x3 x4))
         (equal (uchar=>utf8 (utf8-combine4 x1 x2 x3 x4))
                (list x1 x2 x3 x4)))
 :rule-classes nil
 :g-bindings `((x1 ,(g-int 0 1 9))
               (x2 ,(g-int 9 1 9))
               (x3 ,(g-int 18 1 9))
               (x4 ,(g-int 27 1 9))))





; -----------------------------------------------------------------------------
;
;                    (OPTIMIZING SYMBOLIC EXECUTION)
;                  GL THEOREMS ABOUT STOBJS! AND STATE!
;
; -----------------------------------------------------------------------------

; A GL theorem about a user-defined stobj.

(defstobj my-stobj (fld))

(def-gl-thm stobj-thm
  :hyp (and (unsigned-byte-p 3 x)
            (my-stobjp my-stobj))
  :concl (equal (fld (update-fld x my-stobj))
                x)
  :g-bindings
  `((x ,(g-int 0 1 4))
    (my-stobj ((:g-var . fld)))))

; A (pretty pathetic) GL theorem about STATE!

(def-gl-thm state-thm
  :hyp   t
  :concl (equal (f-get-global :a (f-put-global :a x (build-state)))
                x)
  :g-bindings nil)




; -----------------------------------------------------------------------------
;
;                    (OPTIMIZING SYMBOLIC EXECUTION)
;                      USING PREFERRED DEFINITIONS
;
; -----------------------------------------------------------------------------

(defun element-okp (x)
  (natp x))

(defun filter1 (x)
  (cond ((atom x)
         nil)
        ((element-okp (car x))      ;; keep it
         (cons (car x)
               (filter1 (cdr x))))
        (t                          ;; skip it
         (filter1 (cdr x)))))

(defun filter2 (x)
  (if (atom x)
      nil
    (let ((rest (filter2 (cdr x))))
      (if (element-okp (car x))
          (cons (car x) rest)
        rest))))

(defthm filter1-is-filter2
  (equal (filter1 y)
         (filter2 y))
  :rule-classes nil)

(gl::set-preferred-def filter1 filter1-is-filter2)

(def-gl-thm crock-filter
  :hyp (and (equal (len x) 1)
            (true-listp x)
            (unsigned-byte-p 3 (car x)))
  :concl (equal (filter1 x)
                (filter2 x))
  :g-bindings
  `((x (,(g-int 0 1 4)))))





; -----------------------------------------------------------------------------
;
;                            (CASE SPLITTING)
;                     FAST-LOGCOUNT SPLIT INTO CASES
;
; -----------------------------------------------------------------------------

;; Fast logcount by parameterization

(def-gl-param-thm fast-logcount-32-correct-alt
 :hyp (unsigned-byte-p 32 x)
 :concl (equal (fast-logcount-32 x)
               (logcount x))
 :param-bindings
 `((((msb 1) (low nil)) ((x ,(g-int 32 -1 33))))
   (((msb 0) (low 0))   ((x ,(g-int 0 1 33))))
   (((msb 0) (low 1))   ((x ,(g-int 5 1 33))))
   (((msb 0) (low 2))   ((x ,(g-int 0 2 33))))
   (((msb 0) (low 3))   ((x ,(g-int 3 1 33)))))
 :param-hyp (and (equal msb (ash x -31))
                 (or (equal msb 1)
                     (equal (logand x 3) low)))
 :cov-bindings
 `((x ,(g-int 0 1 33)))
 :run-before-cases (cw "~@0~%" id))






; -----------------------------------------------------------------------------
;
;                          (DEBUGGING FAILURES)
;                      SOME USES OF DEBUGGING TOOLS
;
; -----------------------------------------------------------------------------

(gl::trace-gl-interp)

(gl::break-on-g-apply)

;; Indeterminate result debugging demo
(def-gl-thm integer-half
  :hyp (and (unsigned-byte-p 5 x)
            (not (logbitp 0 x)))
  :concl (equal (* 1/2 x)
                (ash x -1))
  :g-bindings `((x ,(g-int 0 1 6))))




; -----------------------------------------------------------------------------
;
;                             (RELATED WORK)
;                COMPARISON WITH ANTHONY FOX'S HOL BIT BLASTING
;
; -----------------------------------------------------------------------------

; We wanted to compare GL's performance against that of Anthony Fox's procedure
; for bit-blasting in HOL4.  The paper is:
;
;  Anthony Fox.  LCF-style Bit-Blasting in HOL4.  ITP 2011.
;
; In the "performance" section, Fox discusses the performance of his
; bit-blasting tactic on a few sample problems involving 128-bit numbers.
; We'll try to recreate these examples in GL.

; WARNING --- The test machines are not the same!  Fox reports that he is using
; a 2.5 GHz Core 2 Duo machine with 4 GB of memory, whereas we are using a 3
; GHz Xeon E5450 with 64 GB of memory.  We do not think memory is really an
; issue here.  We imagine the Xeon is probably faster than the Core 2 Duo, but
; we don't know for sure.


; Goal 1.  (193 * a) && 7 = 7 && a
;
; We were not sure if the this is a signed or unsigned multiply, so we try
; both cases.
;
; Fox says this takes 45 seconds for his system to solve.
;
; Here are the results we get for GL.  Note that we always use a fresh session
; to avoid any memoized results from screwing up the results.
;
;          | GL, BDD Mode   | GL, AIG Mode  |
;  --------+----------------+---------------+
;   FOX1   |   0.38 sec     |   0.04 sec    |
;   FOX1s  |   0.44 sec     |   0.04 sec    |
;  --------+----------------+---------------+

(def-gl-thm fox1
  :hyp (unsigned-byte-p 128 a)
  :concl (equal (logand (128* 193 a) 7)
                (logand 7 a))
  :g-bindings `((a ,(g-int 0 1 129))))

(def-gl-thm fox1s
  :hyp (signed-byte-p 128 a)
  :concl (equal (logand (128* 193 a) 7)
                (logand 7 a))
  :g-bindings `((a ,(g-int 0 1 129))))




; Goal 2.  (a && b) + (a || b) = a + b
;
; Fox doesn't say how long this takes, but from Figure 2 it looks like it is
; a bit over 5 seconds.  Here we do signed and unsigned versions in GL:
;
;          | GL, BDD Mode   | GL, AIG Mode  |
;  --------+----------------+---------------+
;   FOX2   |    0.07 sec    |    0.58 sec   |
;   FOX2s  |    0.10 sec    |    0.14 sec   |
;  --------+----------------+---------------+

(def-gl-thm fox2
  :hyp (and (unsigned-byte-p 128 a)
            (unsigned-byte-p 128 b))
  :concl (equal (128+ (logand a b)
                      (logior a b))
                (128+ a b))
  :g-bindings `((a ,(g-int 0 2 129))
                (b ,(g-int 1 2 129))))

(def-gl-thm fox2s
  :hyp (and (signed-byte-p 128 a)
            (signed-byte-p 128 b))
  :concl (equal (128+ (logand a b)
                      (logior a b))
                (128+ a b))
  :g-bindings `((a ,(g-int 0 2 129))
                (b ,(g-int 1 2 129))))



; Goal 3.  (8 * a + (b && 7)) >>> 3 = a && ( 1 >>> 3)
;
; Fox doesn't say how long this takes but from Figure 2 it appears to take
; almost no time at all.  GL also handles it with ease:
;
;          | GL, BDD Mode   | GL, AIG Mode  |
;  --------+----------------+---------------+
;   FOX3   |     0.07 sec   |    0.03 sec   |
;   FOX3s  |     0.09 sec   |    0.04 sec   |
;  --------+----------------+---------------+

(def-gl-thm fox3
  :hyp (and (unsigned-byte-p 128 a)
            (unsigned-byte-p 128 b))
  :concl (equal (ash (128+ (128* 8 a)
                           (logand b 7))
                     -3)
                (logand a (ash (128-fix -1) -3)))
  :g-bindings `((a ,(g-int 0 2 129))
                (b ,(g-int 1 2 129))))

(def-gl-thm fox3s
  :hyp (and (signed-byte-p 128 a)
            (signed-byte-p 128 b))
  :concl (equal (ash (128+ (128* 8 a)
                           (logand b 7))
                     -3)
                (logand a (ash (128-fix -1) -3)))
  :g-bindings `((a ,(g-int 0 2 129))
                (b ,(g-int 1 2 129))))



; Fox also says that the following series of nested additions is a bad case for
; his tactic, and that it takes four minutes to convert the second equation
; here when using 128-bit words.
;
;    x = a + b
;    x = a + b + c
;    x = a + b + c + d
;    x = a + b + c + d + e
;     ...
;
; It appears that here, Fox is not asking his tactic to prove a goal, but just
; seeing how long it takes to convert the goal formula into the FCP binders and
; things that the SAT solver then tries to handle.
;
; There is not a direct GL equivalent of this, but the closest thing we can
; think of is to simply ask GL to prove the above formulas even though they are
; not true.
;
; When we do this, GL will still symbolically execute the formula, and in order
; to do this it still has to:
;
;   (1) Construct the :g-number objects representing each sum, and eventually
;   (2) Construct the :g-boolean object representing their equality
;
; It will then inspect the object and produce counterexamples from it.  We have
; asked GL to do this for the sequences above, with 128-bit numbers.  For our
; BDD order, we just interleave all the bits.
;
;         |  GL, BDD Mode  |  GL, AIG Mode
;  -------+----------------+-----------------
;   Seq-1 |   0.29 sec     |    0.08 sec
;   Seq-2 |   0.49 sec     |    0.13 sec
;   Seq-3 |   0.95 sec     |    0.15 sec
;   Seq-4 |   1.45 sec     |    0.18 sec
; --------+----------------+-----------------

(def-gl-thm fox-seq-1
  :hyp (and (unsigned-byte-p 128 x)
            (unsigned-byte-p 128 a)
            (unsigned-byte-p 128 b))
  :concl (equal x (+ a b))
  :g-bindings
  `((a ,(g-int 0 3 129))
    (b ,(g-int 1 3 129))
    (x ,(g-int 2 3 129)))
  :rule-classes nil)

(def-gl-thm fox-seq-2
  :hyp (and (unsigned-byte-p 128 x)
            (unsigned-byte-p 128 a)
            (unsigned-byte-p 128 b)
            (unsigned-byte-p 128 c))
  :concl (equal x (+ a b c))
  :g-bindings
  `((a ,(g-int 0 4 129))
    (b ,(g-int 1 4 129))
    (c ,(g-int 2 4 129))
    (x ,(g-int 3 4 129)))
  :rule-classes nil)

(def-gl-thm fox-seq-3
  :hyp (and (unsigned-byte-p 128 x)
            (unsigned-byte-p 128 a)
            (unsigned-byte-p 128 b)
            (unsigned-byte-p 128 c)
            (unsigned-byte-p 128 d))
  :concl (equal x (+ a b c d))
  :g-bindings
  `((a ,(g-int 0 5 129))
    (b ,(g-int 1 5 129))
    (c ,(g-int 2 5 129))
    (d ,(g-int 3 5 129))
    (x ,(g-int 4 5 129)))
  :rule-classes nil)

(def-gl-thm fox-seq-4
  :hyp (and (unsigned-byte-p 128 x)
            (unsigned-byte-p 128 a)
            (unsigned-byte-p 128 b)
            (unsigned-byte-p 128 c)
            (unsigned-byte-p 128 d)
            (unsigned-byte-p 128 e))
  :concl (equal x (+ a b c d e))
  :g-bindings
  `((a ,(g-int 0 6 129))
    (b ,(g-int 1 6 129))
    (c ,(g-int 2 6 129))
    (d ,(g-int 3 6 129))
    (e ,(g-int 4 6 129))
    (x ,(g-int 5 6 129)))
  :rule-classes nil)





; -----------------------------------------------------------------------------
;
;                             (RELATED WORK)
;                        COMPARISON WITH ACL2 BDDS
;
; -----------------------------------------------------------------------------



(defun v-adder (c a b)
  (if (atom a)
      (list c)
    (cons (xor c (xor (car a) (car b)))
          (v-adder (if c
                       (or (car a) (car b))
                     (and (car a) (car b)))
                   (cdr a) (cdr b)))))

(defthm v-adder-open
  (equal (v-adder c (cons a x) b)
         (cons (xor c (xor a (car b)))
               (v-adder (if c
                            (or a (car b))
                          (and a (car b)))
                        x (cdr b)))))

(defthm v-adder-open2
  (equal (v-adder c nil b)
         (list c)))


(defun make-indexed-sym-list (v n)
  (if (zp n)
      nil
    (cons (intern$ (concatenate 'string
                                (symbol-name v)
                                (coerce (explode-atom (1- n) 10) 'string))
                   "ACL2")
          (make-indexed-sym-list v (1- n)))))

(defmacro list-of-vars (v n)
  `(list . ,(reverse (make-indexed-sym-list v n))))

(defun interleave3 (a b c)
  (if (atom a)
      nil
    (list* (car a) (car b) (car c)
           (interleave3 (cdr a) (cdr b) (cdr c)))))

(defun interleave2 (a b)
  (if (atom a)
      nil
    (list* (car a) (car b)
           (interleave2 (cdr a) (cdr b)))))


;; 300 -- 3.00 sec
;; 500 -- 14.36 seconds
;; 700 -- 42.25 seconds
(time$
 (defthm acl2-plus-commutes-700
   (let ((a (list-of-vars a 700))
         (b (list-of-vars b 700)))
     (implies (and (boolean-listp a)
                   (boolean-listp b))
              (equal (v-adder nil b a)
                     (v-adder nil a b))))
   :hints (`(:bdd (:vars ,(interleave2 (reverse (make-indexed-sym-list 'a 700))
                                       (reverse (make-indexed-sym-list 'b 700))))))))

;; GL:
;;  300 -- 0.22 seconds
;;  500 -- 0.70 seconds
;;  700 -- 1.68 seconds
;;  1000 -- 4.20 seconds
;;  2000 -- 21.68 seconds

(progn$
 (clear-memoize-tables)
 (clear-memoize-statistics)
;(clear-hash-tables) ; Matt K. mod: removed for v7-2, replacements just below
 #+static-hons (hons-wash)
 #-static-hons (hons-clear t)
)

(time$
 (def-gl-thm gl-plus-commutes-500
   :hyp (and (unsigned-byte-p 500 a)
             (unsigned-byte-p 500 b))
   :concl (equal (+ b a) (+ a b))
   :g-bindings
   `((a ,(g-int 0 2 501))
     (b ,(g-int 1 2 501)))))
