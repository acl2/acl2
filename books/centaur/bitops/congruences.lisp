
; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

; contextual rewriting for bitops

;; We treat loghead as a fixing function for congruence-style rewriting via
;; context-rw.lisp.  We also introduce logsquash (name subject to change),
;; which is kind of the "opposite" of loghead, but not the same as logtail.
;; (logsquash n x) is the same as (ash (logtail n x) n) or as
;; (logand (lognot (logmask n)) x), i.e. it squashes the first N bits of X to
;; 0 (whereas loghead squashes all but the first N bits of X.)

;; We could go even further with this and use logand as a fixing function.
;; However, this is a bit awkward since logand is commutative (we'd want one
;; argument to be the mask and the other the operand to be fixed).

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


(in-package "ACL2")
(include-book "tools/rulesets" :dir :system)
(include-book "centaur/misc/context-rw" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "ihsext-basics")
(local (include-book "ihs-extensions"))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "equal-by-logbitp"))
(defmacro def-context-rule (name body &rest args)
  (let* ((fnname-look (ec-call (assoc-keyword :fnname args)))
         (fnname (cadr fnname-look))
         (rest-args (append (take (- (len args) (len fnname-look)) args)
                            (cddr fnname-look))))
    `(progn (defthmd ,name ,body . ,rest-args)
            (add-context-rule ,fnname (:rewrite ,name)))))

(defun logsquash (n i)
  (declare (xargs :guard (and (natp n)
                              (integerp i))))
  (ash (ash i (- (lnfix n))) (lnfix n)))

(defthmd logsquash**
  (equal (logsquash n i)
         (if (zp n)
             (ifix i)
           (logcons 0 (logsquash (1- n) (logcdr i)))))
  :hints(("Goal" :in-theory (enable logtail** ash**)))
  :rule-classes ((:definition :clique (logsquash)
                  :controller-alist ((logsquash t nil)))))

(defcong nat-equiv equal (logsquash n i) 1)
(defcong int-equiv equal (logsquash n i) 2
  :hints(("Goal" :in-theory (disable int-equiv))))

(defthm loghead-of-logsquash-commute
  (equal (loghead m (logsquash n i))
         (logsquash n (loghead m i)))
  :hints(("Goal" :in-theory (enable loghead-of-ash nfix ifix))))

(defthm logsquash-of-loghead-zero
  (implies (<= (nfix n) (nfix m))
           (equal (logsquash m (loghead n i)) 0))
  :hints(("Goal" :in-theory (enable loghead-of-ash nfix ifix loghead**))))

(defthm logsquash-idempotent
  (equal (logsquash n (logsquash n i))
         (logsquash n i)))

(defthm logsquash-combine-1
  (implies (<= (nfix n) (nfix m))
           (equal (logsquash n (logsquash m i))
                  (logsquash m i))))

(defthm logsquash-combine-2
  (implies (<= (nfix m) (nfix n))
           (equal (logsquash n (logsquash m i))
                  (logsquash n i))))

(defthmd logsquash-combine-split
  (equal (logsquash n (logsquash m i))
         (logsquash (max (nfix n) (nfix m)) i))
  :hints(("Goal" :in-theory (disable logsquash))))

;; Since we're normalizing to logsquash of loghead, propagate a logsquash
;; context inside loghead:
(def-context-rule logsquash-of-loghead-context
  (equal (logsquash n (loghead m (logsquash n x)))
         (logsquash n (loghead m x)))
  :fnname logsquash)

;; Logbitp induces both a logsquash and loghead context.
(defthm logbitp-remove-logsquash
  (implies (<= (nfix m) (nfix n))
           (equal (logbitp n (logsquash m i))
                  (logbitp n i))))

(defthm logbitp-remove-loghead
  (implies (< (nfix n) (nfix m))
           (equal (logbitp n (loghead m i))
                  (logbitp n i))))

(def-context-rule logbitp-induces-logsquash/loghead-context
  (equal (logbitp n (logsquash n (loghead (+ 1 (nfix n)) i)))
         (logbitp n i))
  :fnname logbitp)

;; Logtail induces a logsquash context.
(defthm logtail-remove-logsquash
  (implies (<= (nfix m) (nfix n))
           (equal (logtail n (logsquash m i))
                  (logtail n i))))

(def-context-rule logtail-induces-logsquash-context
  (equal (logtail n (logsquash n i))
         (logtail n i))
  :fnname logtail$inline)

;; It also passes a (modified) loghead context.
;; We already have logtail-of-loghead to remove this context.
(def-context-rule logtail-pass-loghead-context
  (equal (loghead n (logtail m (loghead (+ (nfix n) (nfix m)) i)))
         (loghead n (logtail m i)))
  :hints(("Goal" :in-theory (disable logsquash)))
  :fnname loghead$inline)


;; Logic ops are transparent to both types of context.

;; Logior:
(defthm logior-remove-loghead-1
  (implies (<= (nfix n) (nfix m))
           (equal (loghead n (logior (loghead m a) b))
                  (loghead n (logior a b)))))

(defthm logior-remove-loghead-2
  (implies (<= (nfix n) (nfix m))
           (equal (loghead n (logior a (loghead m b)))
                  (loghead n (logior a b)))))

(def-context-rule logior-pass-loghead-context-1
  (equal (loghead n (logior (loghead n a) b))
         (loghead n (logior a b)))
  :fnname loghead$inline)

(def-context-rule logior-pass-loghead-context-2
  (equal (loghead n (logior a (loghead n b)))
         (loghead n (logior a b)))
  :fnname loghead$inline)

(defthm logior-remove-logsquash-1
  (implies (<= (nfix m) (nfix n))
           (equal (logsquash n (logior (logsquash m a) b))
                  (logsquash n (logior a b)))))

(defthm logior-remove-logsquash-2
  (implies (<= (nfix m) (nfix n))
           (equal (logsquash n (logior a (logsquash m b)))
                  (logsquash n (logior a b)))))

(def-context-rule logior-pass-logsquash-context-1
  (equal (logsquash n (logior (logsquash n a) b))
         (logsquash n (logior a b)))
  :fnname logsquash)

(def-context-rule logior-pass-logsquash-context-2
  (equal (logsquash n (logior a (logsquash n b)))
         (logsquash n (logior a b)))
  :fnname logsquash)

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
  :fnname loghead$inline)

(def-context-rule logand-pass-loghead-context-2
  (equal (loghead n (logand a (loghead n b)))
         (loghead n (logand a b)))
  :fnname loghead$inline)

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
  :fnname logsquash)

(def-context-rule logand-pass-logsquash-context-2
  (equal (logsquash n (logand a (logsquash n b)))
         (logsquash n (logand a b)))
  :fnname logsquash)

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
  :fnname loghead$inline)

(def-context-rule logxor-pass-loghead-context-2
  (equal (loghead n (logxor a (loghead n b)))
         (loghead n (logxor a b)))
  :fnname loghead$inline)

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
  :fnname logsquash)

(def-context-rule logxor-pass-logsquash-context-2
  (equal (logsquash n (logxor a (logsquash n b)))
         (logsquash n (logxor a b)))
  :fnname logsquash)

;; Lognot:
(defthm lognot-remove-loghead
  (implies (<= (nfix n) (nfix m))
           (equal (loghead n (lognot (loghead m a)))
                  (loghead n (lognot a)))))

(def-context-rule lognot-pass-loghead-context
  (equal (loghead n (lognot (loghead n a)))
         (loghead n (lognot a)))
  :fnname loghead$inline)

(defthm lognot-remove-logsquash
  (implies (<= (nfix m) (nfix n))
           (equal (logsquash n (lognot (logsquash m a)))
                  (logsquash n (lognot a)))))

(def-context-rule lognot-pass-logsquash-context
  (equal (logsquash n (lognot (logsquash n a)))
         (logsquash n (lognot a)))
  :fnname logsquash)



;; Ash propagates a modified loghead/logsquash context.  Right shift also
;; induces a logsquash context (same as logtail-induces-logsquash-context).

;; This is not compatible with loghead-of-ash.
(defthmd ash-of-loghead
  (equal (ash (loghead m i) n)
         (loghead (+ (nfix m) (ifix n)) (ash i n)))
  :hints(("Goal" :in-theory (e/d (loghead-of-ash ifix nfix loghead**)
                                 (loghead-identity)))))

(local (in-theory (disable loghead-of-ash)))

(def-context-rule ash-propagate-loghead-context
  (equal (loghead n (ash (loghead (- (nfix n) (ifix m)) i) m))
         (loghead n (ash i m)))
  :hints(("Goal" :in-theory (e/d (ash-of-loghead
                                  ifix nfix loghead-of-loghead-split
                                  loghead**)
                                 (loghead-identity))))
  :fnname loghead$inline)

(defthmd ash-of-logsquash
  (equal (ash (logsquash m i) n)
         (logsquash (+ (nfix m) (ifix n)) (ash i n)))
  :hints(("Goal" :in-theory (enable ifix nfix))))

(def-context-rule ash-propagate-logsquash-context
  (equal (logsquash n (ash (logsquash (- (nfix n) (ifix m)) i) m))
         (logsquash n (ash i m)))
  :hints(("Goal" :in-theory (enable ifix nfix)))
  :fnname logsquash)

(def-context-rule right-shift-induces-logsquash-context
  (implies (<= (ifix m) 0)
           (equal (ash (logsquash (- (ifix m)) i) m)
                  (ash i m)))
  :hints(("Goal" :in-theory (enable ifix)))
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
              :in-theory (e/d (nfix logcdr-of-bit b-and b-ior)
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
  :fnname loghead$inline)

(def-context-rule loghead-of-plus-context-1
  (implies (and (integerp a) (integerp b))
           (equal (loghead n (+ (loghead n a) b))
                  (loghead n (+ a b))))
  :hints(("Goal" :in-theory (enable loghead-of-plus-loghead-second)))
  :fnname loghead$inline)

(def-context-rule loghead-of-plus-context-2
  (implies (and (integerp a) (integerp b))
           (equal (loghead n (+ a (loghead n b)))
                  (loghead n (+ a b))))
  :hints(("Goal" :in-theory (enable loghead-of-plus-loghead-second)))
  :fnname loghead$inline)


(def-ruleset! bitops-congruences
  '(apply-context-for-loghead$inline
    apply-context-for-logsquash
    common-lisp::apply-context-for-logbitp
    common-lisp::apply-context-for-ash
    apply-context-for-logtail$inline
    loghead-of-logsquash-commute
    logsquash-of-loghead-zero
    logsquash-idempotent
    logsquash-combine-split
    loghead-of-loghead-split
    logbitp-remove-logsquash
    logbitp-remove-loghead
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
    lognot-remove-loghead
    lognot-pass-loghead-context
    lognot-remove-logsquash
    lognot-pass-logsquash-context
    ash-of-loghead
    ash-of-logsquash
    loghead-of-minus-of-loghead
    loghead-of-plus-loghead-first
    loghead-of-plus-loghead-second
    loghead-of-minus-context
    loghead-of-plus-context-1
    loghead-of-plus-context-2))

(def-ruleset! bitops-congruence-incompatible
  '(loghead-of-logior
    loghead-of-ash
    loghead-of-logxor
    loghead-of-logand))

(in-theory (disable* apply-context-for-loghead$inline
                     apply-context-for-logsquash
                     common-lisp::apply-context-for-logbitp
                     common-lisp::apply-context-for-ash
                     apply-context-for-logtail$inline))
