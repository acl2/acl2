; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
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

; contextual rewriting for bitops

;; We treat loghead as a fixing function for congruence-style rewriting via
;; context-rw.lisp.  We also introduce logsquash (name subject to change),
;; which is kind of the "opposite" of loghead, but not the same as logtail.
;; (logsquash n x) is the same as (ash (logtail n x) n) or as
;; (logand (lognot (logmask n)) x), i.e. it squashes the first N bits of X to
;; 0 (whereas loghead squashes all but the first N bits of X.)

;; We also go even further with this and use logand as a fixing function when
;; its left argument is a constant.

;; principle: rewrite rules should propagate fixing functions outward,
;; and our context-rw meta rules will propagate them inward.  For example,
;; (defthmd ash-of-loghead
;;   (equal (ash (loghead n x) m)
;;          (loghead (+ (nfix n) (ifix m)) (ash x m))))
;; is a reasonable rewrite rule, because it pulls a loghead out of an ash.
;; Correspondingly,
;; (def-context-rule loghead-of-ash-context
;;   (equal (loghead n (ash (loghead (- (nfix n) (ifix m)) a) m))
;;          (loghead n (ash a m)))
;;   :fnname loghead)
;; is a context rule that propagates the loghead context into the argument of
;; ash.  This way, generally, contextual information is normalized to the
;; outside but is still available for simplifications deep inside nestings of
;; bit operations.
;; --------------------------------------------------------------------
;; Context-rw.lisp (like coi/nary) allows us to do congruence-like reasoning
;; with parameters, i.e.

(in-package "BITOPS")
(include-book "tools/rulesets" :dir :system)
(include-book "centaur/misc/context-rw" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "ihsext-basics")
(local (include-book "ihs-extensions"))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "equal-by-logbitp"))

; Added by Matt K., 7/2014: disable waterfall parallelism for the proofs below,
; since some call logbitp-reasoning.  See the long comment near the form
; (non-parallel-book) in centaur/bitops/equal-by-logbitp.lisp.

(local (include-book "std/system/non-parallel-book" :dir :system))
(local (non-parallel-book)) ; probably need not be local

(defmacro def-context-rule (name body &rest args)
  (let* ((fnname-look (ec-call (assoc-keyword :fnname args)))
         (fnname (cadr fnname-look))
         (rest-args (append (take (- (len args) (len fnname-look)) args)
                            (cddr fnname-look))))
    `(progn (defthmd ,name ,body . ,rest-args)
            (add-context-rule ,fnname (:rewrite ,name)))))



;; Since we're normalizing to logsquash of loghead, propagate a logsquash
;; context inside loghead:
;; This is its own removal rule.
(def-context-rule logsquash-of-loghead-context
  (equal (logsquash n (loghead m (logsquash n x)))
         (logsquash n (loghead m x)))
  :fnname logsquash$inline)
(in-theory (disable apply-context-for-logsquash$inline))

(in-theory (enable logsquash-of-loghead-context))

;; ;; Logbitp induces both a logsquash and loghead context.
;; (defthm logbitp-remove-logsquash
;;   (implies (<= (nfix m) (nfix n))
;;            (equal (logbitp n (logsquash m i))
;;                   (logbitp n i))))

;; (defthm logbitp-remove-loghead
;;   (implies (< (nfix n) (nfix m))
;;            (equal (logbitp n (loghead m i))
;;                   (logbitp n i))))

;; Removal rule: logbitp-of-logsquash-in-bounds
(def-context-rule logbitp-induces-logsquash/loghead-context
  (implies (syntaxp (not (quotep n)))
           ;; if n is quotep we'll prefer a logand context instead
           (equal (logbitp n (logsquash n (loghead (+ 1 (nfix n)) i)))
                  (logbitp n i)))
  :fnname logbitp)

(in-theory (disable common-lisp::apply-context-for-logbitp))

;; ;; Logtail induces a logsquash context.
;; It also passes a (modified) loghead context.

;; Removal rule: logtail-of-logsquash
(def-context-rule logtail-induces-logsquash-context
  (equal (logtail n (logsquash n i))
         (logtail n i))
  :fnname acl2::logtail$inline)

(in-theory (disable acl2::apply-context-for-logtail$inline))

;; Removal rule: logtail-of-loghead
(def-context-rule logtail-pass-loghead-context
  (equal (loghead n (logtail m (loghead (+ (nfix n) (nfix m)) i)))
         (loghead n (logtail m i)))
  :hints(("Goal" :in-theory (disable logsquash)))
  :fnname acl2::loghead$inline)

(in-theory (disable acl2::apply-context-for-loghead$inline))


;; Logic ops are transparent to both types of context.

;; Logior:
(defthm logior-remove-loghead-1
  (implies (<= (nfix n) (nfix m))
           (equal (loghead n (logior (loghead m a) b))
                  (loghead n (logior a b)))))

(def-context-rule logior-pass-loghead-context-1
  (equal (loghead n (logior (loghead n a) b))
         (loghead n (logior a b)))
  :fnname acl2::loghead$inline)

(defthm logior-remove-loghead-2
  (implies (<= (nfix n) (nfix m))
           (equal (loghead n (logior a (loghead m b)))
                  (loghead n (logior a b)))))

(def-context-rule logior-pass-loghead-context-2
  (equal (loghead n (logior a (loghead n b)))
         (loghead n (logior a b)))
  :fnname acl2::loghead$inline)

(defthm logior-remove-logsquash-1
  (implies (<= (nfix m) (nfix n))
           (equal (logsquash n (logior (logsquash m a) b))
                  (logsquash n (logior a b))))
  :hints ((logbitp-reasoning)))

(defthm logior-remove-logsquash-2
  (implies (<= (nfix m) (nfix n))
           (equal (logsquash n (logior a (logsquash m b)))
                  (logsquash n (logior a b))))
  :hints ((logbitp-reasoning)))

(def-context-rule logior-pass-logsquash-context-1
  (equal (logsquash n (logior (logsquash n a) b))
         (logsquash n (logior a b)))
  :fnname logsquash$inline)

(def-context-rule logior-pass-logsquash-context-2
  (equal (logsquash n (logior a (logsquash n b)))
         (logsquash n (logior a b)))
  :fnname logsquash$inline)

;; Logand:
(defthm logand-remove-loghead-1
  (implies (<= (nfix n) (nfix m))
           (equal (loghead n (logand (loghead m a) b))
                  (loghead n (logand a b)))))

(defthm logand-remove-loghead-2
  (implies (<= (nfix n) (nfix m))
           (equal (loghead n (logand a (loghead m b)))
                  (loghead n (logand a b)))))

(def-context-rule logand-pass-loghead-context-1
  (equal (loghead n (logand (loghead n a) b))
         (loghead n (logand a b)))
  :fnname acl2::loghead$inline)

(def-context-rule logand-pass-loghead-context-2
  (equal (loghead n (logand a (loghead n b)))
         (loghead n (logand a b)))
  :fnname acl2::loghead$inline)

(local (set-default-hints
        '((logbitp-reasoning)
          (and stable-under-simplificationp
               '(:in-theory (enable b-ior b-and b-not b-xor
                                    nfix))))))

(defthm logand-remove-logsquash-1
  (implies (<= (nfix m) (nfix n))
           (equal (logsquash n (logand (logsquash m a) b))
                  (logsquash n (logand a b)))))

(defthm logand-remove-logsquash-2
  (implies (<= (nfix m) (nfix n))
           (equal (logsquash n (logand a (logsquash m b)))
                  (logsquash n (logand a b)))))

(def-context-rule logand-pass-logsquash-context-1
  (equal (logsquash n (logand (logsquash n a) b))
         (logsquash n (logand a b)))
  :fnname logsquash$inline)

(def-context-rule logand-pass-logsquash-context-2
  (equal (logsquash n (logand a (logsquash n b)))
         (logsquash n (logand a b)))
  :fnname logsquash$inline)

;; Logxor:
(defthm logxor-remove-loghead-1
  (implies (<= (nfix n) (nfix m))
           (equal (loghead n (logxor (loghead m a) b))
                  (loghead n (logxor a b)))))

(defthm logxor-remove-loghead-2
  (implies (<= (nfix n) (nfix m))
           (equal (loghead n (logxor a (loghead m b)))
                  (loghead n (logxor a b)))))

(def-context-rule logxor-pass-loghead-context-1
  (equal (loghead n (logxor (loghead n a) b))
         (loghead n (logxor a b)))
  :fnname acl2::loghead$inline)

(def-context-rule logxor-pass-loghead-context-2
  (equal (loghead n (logxor a (loghead n b)))
         (loghead n (logxor a b)))
  :fnname acl2::loghead$inline)

(defthm logxor-remove-logsquash-1
  (implies (<= (nfix m) (nfix n))
           (equal (logsquash n (logxor (logsquash m a) b))
                  (logsquash n (logxor a b)))))

(defthm logxor-remove-logsquash-2
  (implies (<= (nfix m) (nfix n))
           (equal (logsquash n (logxor a (logsquash m b)))
                  (logsquash n (logxor a b)))))

(def-context-rule logxor-pass-logsquash-context-1
  (equal (logsquash n (logxor (logsquash n a) b))
         (logsquash n (logxor a b)))
  :fnname logsquash$inline)

(def-context-rule logxor-pass-logsquash-context-2
  (equal (logsquash n (logxor a (logsquash n b)))
         (logsquash n (logxor a b)))
  :fnname logsquash$inline)

;; Lognot:
;; (defthm lognot-remove-loghead
;;   (implies (<= (nfix n) (nfix m))
;;            (equal (loghead n (lognot (loghead m a)))
;;                   (loghead n (lognot a)))))

;; Removal rule: loghead-cancel-in-lognot
(def-context-rule lognot-pass-loghead-context
  (equal (loghead n (lognot (loghead n a)))
         (loghead n (lognot a)))
  :fnname acl2::loghead$inline)

;; (defthm lognot-remove-logsquash
;;   (implies (<= (nfix m) (nfix n))
;;            (equal (logsquash n (lognot (logsquash m a)))
;;                   (logsquash n (lognot a)))))

;; Removal rule: logsquash-cancel-in-lognot
(def-context-rule lognot-pass-logsquash-context
  (equal (logsquash n (lognot (logsquash n a)))
         (logsquash n (lognot a)))
  :fnname logsquash$inline)



;; Ash propagates a modified loghead/logsquash context.  Right shift also
;; induces a logsquash context (same as logtail-induces-logsquash-context).

;; This is not compatible with loghead-of-ash.  But loghead-of-ash doesn't work
;; as a context removal rule; it just pushes the outer context inside.  This
;; works because it pulls the inner context out.
(defthmd ash-of-loghead
  (equal (ash (loghead m i) n)
         (loghead (+ (nfix m) (ifix n)) (ash i n))))

(local (in-theory (disable loghead-of-ash)))

(def-context-rule ash-propagate-loghead-context
  (equal (loghead n (ash (loghead (- (nfix n) (ifix m)) i) m))
         (loghead n (ash i m)))
  :fnname acl2::loghead$inline)

(defthmd ash-of-logsquash
  (equal (ash (logsquash m i) n)
         (logsquash (+ (nfix m) (ifix n)) (ash i n))))

(def-context-rule ash-propagate-logsquash-context
  (equal (logsquash n (ash (logsquash (- (nfix n) (ifix m)) i) m))
         (logsquash n (ash i m)))
  :fnname logsquash$inline)

;; (defthm right-shift-remove-logsquash
;;   (implies (and (<= (ifix m) 0)
;;                 (<= (nfix n) (- (ifix m))))
;;            (equal (ash (logsquash n i) m)
;;                   (ash i m)))
;;   :hints(("Goal" :in-theory (e/d (ash-of-logsquash logsquash**)
;;                                  (right-shift-to-logtail)))))

;; ash-of-logsquash should work as the removal rule for this too
(def-context-rule right-shift-induces-logsquash-context
  (implies (<= (ifix m) 0)
           (equal (ash (logsquash (- (ifix m)) i) m)
                  (ash i m)))
  :hints(("Goal" :in-theory (e/d (ifix nfix))))
  :fnname ash)



;; Addition/subtraction pass loghead, but not logsquash, contexts

(local
 (encapsulate
   nil
   (local (defun ind (n m a b c)
            (if (zp n)
                (list m a b c)
              (ind (1- n) (1- m)
                   (logcdr a)
                   (logcdr b)
                   (b-ior (b-and (logcar a) (logcar b))
                          (b-ior
                           (b-and (logcar a) (logcar c))
                           (b-and (logcar b) (logcar c))))))))

   (local (defthm logxor-1
            (implies (bitp x)
                     (equal (logxor 1 x)
                            (b-not x)))))

   (local (set-default-hints nil))

; Reordering the rewrite-clause-type-alist: I added the uppercase text below to
; make this work.  See the comment in rewrite-clause-type-alist.
; JSM April 7, 2013.

   (defthm loghead-of-sum-lemma
     (implies (and (integerp a)
                   (integerp b)
                   (bitp c)
                   (<= (nfix n) (nfix m)))
              (equal (loghead n (+ c a (loghead m b)))
                     (loghead n (+ c a b))))
     :hints (("goal"
              :induct (ind n m a b c)
              :do-not '(generalize fertilize)
              :expand ((:free (b) (loghead n b))
                       (:free (b) (loghead m b)))
              :in-theory (e/d (nfix logcdr-of-bit b-and b-ior b-not)
                              (loghead-identity
                               (:FORWARD-CHAINING LOGCAR-POSSIBILITIES)
                               ))
              :do-not-induct t))
     :rule-classes nil)))


;; Rewrite rules for plus/minus under loghead
(defthmd loghead-of-minus-of-loghead
  (implies (and (integerp b)
                (<= (nfix n) (nfix m)))
           (equal (loghead n (- (loghead m b)))
                  (loghead n (- b))))
  :hints (("goal" :in-theory (e/d (minus-to-lognot))
           :use ((:instance loghead-of-sum-lemma
                  (c 1) (a 0) (b (lognot (loghead m b))))
                 (:instance loghead-of-sum-lemma
                  (c 1) (a 0) (b (lognot b)))))))

(defthmd loghead-of-plus-loghead-first
  (implies (and (integerp a)
                (integerp b)
                (<= (nfix n) (nfix m)))
           (equal (loghead n (+ (loghead m b) a))
                  (loghead n (+ a b))))
  :hints (("goal" :use ((:instance loghead-of-sum-lemma (c 0))))))

(defthmd loghead-of-plus-loghead-second
  (implies (and (integerp a)
                (integerp b)
                (<= (nfix n) (nfix m)))
           (equal (loghead n (+ a (loghead m b)))
                  (loghead n (+ a b))))
  :hints (("goal" :use ((:instance loghead-of-sum-lemma (c 0))))))

;; Context rules for plus/minus
(def-context-rule loghead-of-minus-context
  (implies (integerp b)
           (equal (loghead n (- (loghead n b)))
                  (loghead n (- b))))
  :hints(("Goal" :in-theory (enable loghead-of-minus-of-loghead)))
  :fnname acl2::loghead$inline)

(def-context-rule loghead-of-plus-context-1
  (implies (and (integerp a) (integerp b))
           (equal (loghead n (+ (loghead n a) b))
                  (loghead n (+ a b))))
  :hints(("Goal" :in-theory (enable loghead-of-plus-loghead-second)))
  :fnname acl2::loghead$inline)

(def-context-rule loghead-of-plus-context-2
  (implies (and (integerp a) (integerp b))
           (equal (loghead n (+ a (loghead n b)))
                  (loghead n (+ a b))))
  :hints(("Goal" :in-theory (enable loghead-of-plus-loghead-second)))
  :fnname acl2::loghead$inline)





;; Logand.  This is the most general, but only works with a constant as the
;; mask.  Doesn't work with add/subtract.

;; This is useful for removal of logbitp-of-logand
(defthm bool->bit-equal-1
  (implies (booleanp x)
           (equal (equal 1 (bool->bit x))
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(def-context-rule logbitp-induces-logand-context
  (implies (syntaxp (quotep n))
           (equal (logbitp n (logand (ash 1 (nfix n)) m))
                  (logbitp n m)))
  :fnname logbitp)

(defthm logior-remove-logand
  (implies (and (syntaxp (and (quotep n1) (quotep n2)))
                (equal (logior n1 n2) -1))
           (equal (logior n1 (logand n2 m))
                  (logior n1 m))))

(def-context-rule logior-induces-logand-context
  (implies (syntaxp (quotep n))
           (equal (logior n (logand (lognot n) m))
                  (logior n m)))
  :fnname binary-logior)

(defthm lognot-remove-logand-context
  (implies (and (syntaxp (and (quotep n1) (quotep n2)))
                (equal (logand n1 (lognot n2)) 0))
           (equal (logand n1 (lognot (logand n2 m)))
                  (logand n1 (lognot m)))))

(def-context-rule lognot-pass-logand-context
  (implies (syntaxp (quotep n))
           (equal (logand n (lognot (logand n m)))
                  (logand n (lognot m))))
  :fnname binary-logand)

(defthm logior-remove-logand-context-1
  (implies (and (syntaxp (and (quotep n1)
                              (quotep n2)))
                (equal (logand n1 (lognot n2)) 0))
           (equal (logand n1 (logior (logand n2 m1) m2))
                  (logand n1 (logior m1 m2)))))

(def-context-rule logior-pass-logand-context-1
  (implies (syntaxp (quotep n))
           (equal (logand n (logior (logand n m1) m2))
                  (logand n (logior m1 m2))))
  :fnname binary-logand)

(defthm logior-remove-logand-context-2
  (implies (and (syntaxp (and (quotep n1)
                              (quotep n2)))
                (equal (logand n1 (lognot n2)) 0))
           (equal (logand n1 (logior m2 (logand n2 m1)))
                  (logand n1 (logior m2 m1)))))

(def-context-rule logior-pass-logand-context-2
  (implies (syntaxp (quotep n))
           (equal (logand n (logior m2 (logand n m1)))
                  (logand n (logior m2 m1))))
  :fnname binary-logand)

(defthm logand-remove-logand-context-1
  (implies (and (syntaxp (and (quotep n1)
                              (quotep n2)))
                (equal (logand n1 (lognot n2)) 0))
           (equal (logand n1 (logand (logand n2 m1) m2))
                  (logand n1 (logand m1 m2)))))

(def-context-rule logand-pass-logand-context-1
  (implies (syntaxp (quotep n))
           (equal (logand n (logand (logand n m1) m2))
                  (logand n (logand m1 m2))))
  :fnname binary-logand)

(defthm logand-remove-logand-context-2
  (implies (and (syntaxp (and (quotep n1)
                              (quotep n2)))
                (equal (logand n1 (lognot n2)) 0))
           (equal (logand n1 (logand m2 (logand n2 m1)))
                  (logand n1 (logand m2 m1)))))

(def-context-rule logand-pass-logand-context-2
  (implies (syntaxp (quotep n))
           (equal (logand n (logand m2 (logand n m1)))
                  (logand n (logand m2 m1))))
  :fnname binary-logand)

(defthm logxor-remove-logand-context-1
  (implies (and (syntaxp (and (quotep n1)
                              (quotep n2)))
                (equal (logand n1 (lognot n2)) 0))
           (equal (logand n1 (logxor (logand n2 m1) m2))
                  (logand n1 (logxor m1 m2)))))

(def-context-rule logxor-pass-logand-context-1
  (implies (syntaxp (quotep n))
           (equal (logand n (logxor (logand n m1) m2))
                  (logand n (logxor m1 m2))))
  :fnname binary-logand)

(defthm logxor-remove-logand-context-2
  (implies (and (syntaxp (and (quotep n1)
                              (quotep n2)))
                (equal (logand n1 (lognot n2)) 0))
           (equal (logand n1 (logxor m2 (logand n2 m1)))
                  (logand n1 (logxor m2 m1)))))

(def-context-rule logxor-pass-logand-context-2
  (implies (syntaxp (quotep n))
           (equal (logand n (logxor m2 (logand n m1)))
                  (logand n (logxor m2 m1))))
  :fnname binary-logand)


(defthm logand-loghead-combine-contexts
  (implies (syntaxp (and (quotep n1)
                         (quotep n2)))
           (equal (logand n1 (loghead n2 m))
                  (logand (logand n1 (1- (ash 1 (nfix n2)))) m)))
  :hints (("goal" :use ((:instance logand-with-bitmask
                         (mask (1- (ash 1 (nfix n2))))
                         (i m)))
           :in-theory (e/d ()
                           (ash-1-removal)))))

(defthm loghead-logand-combine-contexts
  (implies (syntaxp (and (quotep n1)
                         (quotep n2)))
           (equal (loghead n1 (logand n2 m))
                  (logand (logand n2 (1- (ash 1 (nfix n1)))) m)))
  :hints (("goal" :use ((:instance logand-with-bitmask
                         (mask (1- (ash 1 (nfix n1))))
                         (i (logand n2 m))))
           :in-theory (disable ash-1-removal))
          (equal-by-logbitp-hammer)))

(defthm logand-logsquash-combine-contexts
  (implies (syntaxp (and (quotep n1)
                         (quotep n2)))
           (equal (logand n1 (logsquash n2 m))
                  (logand (logand n1 (lognot (1- (ash 1 (nfix n2))))) m)))
  :hints (("goal" :in-theory (disable ash-1-removal))
          (equal-by-logbitp-hammer)))

(defthm logsquash-logand-combine-contexts
  (implies (syntaxp (and (quotep n1)
                         (quotep n2)))
           (equal (logsquash n1 (logand n2 m))
                  (logand (logand n2 (lognot (1- (ash 1 (nfix n1))))) m)))
  :hints (("goal" :use ((:instance logand-with-negated-bitmask
                         (mask (lognot (1- (ash 1 (nfix n1)))))
                         (i (logand n2 m))))
           :in-theory (e/d () (ash-1-removal
                               logand-with-negated-bitmask)))))

(defthm ash-remove-logand-context
  (implies (and (syntaxp (and (quotep n1)
                              (quotep n2)))
                (equal (logand (lognot (ash n2 (ifix m))) n1) 0))
           (equal (logand n1 (ash (logand n2 i) m))
                  (logand n1 (ash i m)))))


(def-context-rule ash-propagate-logand-context
  (implies (syntaxp (quotep n))
           (equal (logand n (ash (logand (ash n (- (ifix m))) i) m))
                  (logand n (ash i m))))
  :fnname binary-logand)

;; Rewrite a logsquash of loghead to a logand when sizes are constant:
(defthm logsquash-of-loghead-to-logand
  (implies (syntaxp (and (quotep n) (quotep m)))
           (equal (logsquash n (loghead m i))
                  (logand (logsquash n (loghead m -1)) i))))

(local (defthm logbitp-when-gte-integer-length
         (implies (<= (integer-length n) (nfix i))
                  (equal (logbitp i n)
                         (< (ifix n) 0)))
         :hints (("goal" :in-theory (enable* ihsext-inductions
                                             ihsext-recursive-redefs)
                  :induct (logbitp i n)
                  :expand ((integer-length n))))))

;; logand can create a loghead context, but for the most part we don't want it
;; to:
(defthmd logand-of-loghead-context-lemma
  (implies (<= 0 (ifix n))
           (equal (logand n (loghead (integer-length n) b))
                  (logand n b))))



(defthm equal-of-logands-by-equal-of-logheads
  (implies (and (equal (loghead h a) (loghead h b))
                (equal (logsquash h n) 0))
           (equal (logand n a) (logand n b)))
  :rule-classes nil)

(defthm logand-minus-remove-loghead-context
  (implies (and (syntaxp (and (quotep n)
                              (quotep h)))
                (<= 0 (ifix n))
                (equal (logsquash h n) 0)
                (integerp b))
           (equal (logand n (- (loghead h b)))
                  (logand n (- b))))
  :hints (("goal" :use ((:instance equal-of-logands-by-equal-of-logheads
                         (a (- (loghead h b))) (b (- b))))
           :in-theory (enable loghead-of-minus-of-loghead))))

;; Logand can create a loghead context for +/-
;; Context rules for plus/minus
(def-context-rule logand-of-minus-context
  (implies (and (syntaxp (quotep n))
                (<= 0 (ifix n))
                (integerp b))
           (equal (logand n (- (loghead (integer-length n) b)))
                  (logand n (- b))))
  :hints(("Goal" :use ((:instance logand-of-loghead-context-lemma
                        (b (- b)))
                       (:instance logand-of-loghead-context-lemma
                        (b (- (loghead (integer-length n) b)))))
          :in-theory (enable loghead-of-minus-of-loghead)))
  :fnname binary-logand)

(defthm logand-plus-remove-loghead-context-1
  (implies (and (syntaxp (and (quotep n)
                              (quotep h)))
                (<= 0 (ifix n))
                (equal (logsquash h n) 0)
                (integerp b) (integerp c))
           (equal (logand n (+ (loghead h b) c))
                  (logand n (+ b c))))
  :hints (("goal" :use ((:instance equal-of-logands-by-equal-of-logheads
                         (a (+ (loghead h b) c)) (b (+ b c))))
           :in-theory (enable loghead-of-plus-loghead-second))))

(def-context-rule logand-of-plus-context-first
  (implies (and (syntaxp (quotep n))
                (<= 0 (ifix n))
                (integerp a)
                (integerp b))
           (equal (logand n (+ (loghead (integer-length n) a) b))
                  (logand n (+ a b))))
  :hints(("Goal" :use ((:instance logand-of-loghead-context-lemma
                        (b (+ a b)))
                       (:instance logand-of-loghead-context-lemma
                        (b (+ (loghead (integer-length n) a) b))))
          :in-theory (enable loghead-of-plus-loghead-second)))
  :fnname binary-logand)

(defthm logand-plus-remove-loghead-context-2
  (implies (and (syntaxp (and (quotep n)
                              (quotep h)))
                (<= 0 (ifix n))
                (equal (logsquash h n) 0)
                (integerp b) (integerp c))
           (equal (logand n (+ c (loghead h b)))
                  (logand n (+ c b))))
  :hints (("goal" :use ((:instance equal-of-logands-by-equal-of-logheads
                         (a (+ c (loghead h b))) (b (+ c b))))
           :in-theory (enable loghead-of-plus-loghead-second))))

(def-context-rule logand-of-plus-context-second
  (implies (and (syntaxp (quotep n))
                (<= 0 (ifix n))
                (integerp a)
                (integerp b))
           (equal (logand n (+ a (loghead (integer-length n) b)))
                  (logand n (+ a b))))
  :hints(("Goal" :use ((:instance logand-of-loghead-context-lemma
                        (b (+ a b)))
                       (:instance logand-of-loghead-context-lemma
                        (b (+ a (loghead (integer-length n) b)))))
          :in-theory (enable loghead-of-plus-loghead-first
                             loghead-of-plus-loghead-second)))
  :fnname binary-logand)

(def-ruleset! bitops-congruences
  '(acl2::apply-context-for-loghead$inline
    apply-context-for-logsquash$inline
    acl2::apply-context-for-binary-logior
    acl2::apply-context-for-binary-logand
    common-lisp::apply-context-for-logbitp
    common-lisp::apply-context-for-ash
    acl2::apply-context-for-logtail$inline
    loghead-of-logsquash-commute
    logsquash-of-loghead-zero
    logsquash-of-loghead-context
    logsquash-idempotent
    logsquash-of-logsquash-split
    loghead-of-loghead-split
    logbitp-of-logsquash-in-bounds
    logbitp-of-loghead-out-of-bounds
    logtail-of-logsquash
    logtail-of-loghead
    logior-remove-loghead-1
    logior-remove-loghead-2
    logior-pass-loghead-context-1
    logior-pass-loghead-context-2
    logior-remove-logsquash-1
    logior-remove-logsquash-2
    logior-pass-logsquash-context-1
    logior-pass-logsquash-context-2
    logand-remove-loghead-1
    logand-remove-loghead-2
    logand-pass-loghead-context-1
    logand-pass-loghead-context-2
    logand-remove-logsquash-1
    logand-remove-logsquash-2
    logand-pass-logsquash-context-1
    logand-pass-logsquash-context-2
    logxor-remove-loghead-1
    logxor-remove-loghead-2
    logxor-pass-loghead-context-1
    logxor-pass-loghead-context-2
    logxor-remove-logsquash-1
    logxor-remove-logsquash-2
    logxor-pass-logsquash-context-1
    logxor-pass-logsquash-context-2
    loghead-cancel-in-lognot
    logsquash-cancel-in-lognot
    lognot-pass-loghead-context
    lognot-pass-logsquash-context
    ash-of-loghead
    ash-of-logsquash
    loghead-of-minus-of-loghead
    loghead-of-plus-loghead-first
    loghead-of-plus-loghead-second
    loghead-of-minus-context
    loghead-of-plus-context-1
    loghead-of-plus-context-2
    logbitp-induces-logand-context
    logior-induces-logand-context
    lognot-remove-logand-context
    lognot-pass-logand-context
    logior-remove-logand-context-1
    logior-pass-logand-context-1
    logior-remove-logand-context-2
    logior-pass-logand-context-2
    logand-remove-logand-context-1
    logand-pass-logand-context-1
    logand-remove-logand-context-2
    logand-pass-logand-context-2
    logxor-remove-logand-context-1
    logxor-pass-logand-context-1
    logxor-remove-logand-context-2
    logxor-pass-logand-context-2
    logand-loghead-combine-contexts
    loghead-logand-combine-contexts
    logand-logsquash-combine-contexts
    logsquash-logand-combine-contexts
    ash-propagate-logand-context
    logsquash-of-loghead-to-logand
    logand-minus-remove-loghead-context
    logand-of-minus-context
    logand-plus-remove-loghead-context-1
    logand-of-plus-context-first
    logand-plus-remove-loghead-context-2
    logand-of-plus-context-second))

(def-ruleset! bitops-congruence-incompatible
  '(;; loghead-of-logior
    loghead-of-ash
    logsquash-of-ash
    ;; loghead-of-logxor
    ;; loghead-of-logand
    ))
;; logand-with-bitmask?

(in-theory (disable* acl2::apply-context-for-loghead$inline
                     apply-context-for-logsquash$inline
                     acl2::apply-context-for-binary-logior
                     acl2::apply-context-for-binary-logand
                     common-lisp::apply-context-for-logbitp
                     common-lisp::apply-context-for-ash
                     acl2::apply-context-for-logtail$inline))
