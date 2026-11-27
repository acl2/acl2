; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug fixed before ACL2 Version 8.8.

; The type-alist and linear pot-lst of a metafunction context can contain facts
; derived from forward-chaining or linear rules with forced hypotheses; such a
; fact depends on an assumption that is proved only if it gets into the ttree
; of the proof.  Meta-extract-contextual-fact trusted answers of mfc-ts,
; mfc-rw, mfc-rw+, mfc-relieve-hyp and mfc-ap computed with :forcep nil, but
; those functions discarded the ttree, so an answer depending on such a fact
; left its forced hypothesis unproved.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun mpp (x) (declare (xargs :guard t)) (equal x 'magic))
(defun mbar (x) (declare (xargs :guard t)) (equal x 'magic))
(defun mtrig (x) (declare (xargs :guard t) (ignore x)) t)
(defun foo (x) (declare (xargs :guard t)) (if (mbar x) nil 7))
(defun mval (x) (declare (xargs :guard t)) (if (mpp x) -1 1))
(defun foo2 (x) (declare (xargs :guard t)) (if (< 0 (mval x)) 7 nil))

(defthm foo-when-mbar ; for mfc-relieve-hyp below
  (implies (mbar x) (equal (foo x) nil)))

(defthm mpp-forward-to-mbar
  (implies (and (mtrig x) (force (mpp x)))
           (mbar x))
  :rule-classes ((:forward-chaining :trigger-terms ((mtrig x)))))

(defthm mval-negative
  (implies (force (mpp x))
           (< (mval x) 0))
  :rule-classes :linear)

(in-theory (disable mpp mbar mtrig foo mval foo2
                    (mpp) (mbar) (mtrig) (foo) (mval) (foo2)
                    (:t mpp) (:t mbar) (:t mtrig) (:t foo) (:t mval) (:t foo2)
                    foo-when-mbar))

(defevaluator mev mev-lst
  ((typespec-check ts x) (if a b c) (equal a b) (not a) (iff a b) (< a b)
   (foo x) (mbar x) (foo2 x) (mval x))
  :namedp t)

; Part 1: (mbar x) in the type-alist, from forward chaining.  The metafunction
; rewrites (foo x) to nil if any of four mfc- functions says that (mbar x) is
; true.

(defun mf (term mfc state)
  (declare (xargs :stobjs state :verify-guards nil))
  (if (and (equal term '(foo x))
           (or (equal (logand *ts-nil*
                              (mfc-ts '(mbar x) mfc state :forcep nil))
                      0)
               (equal (mfc-rw '(mbar x) t t mfc state :forcep nil)
                      *t*)
               (equal (mfc-rw+ '(mbar v) '((v . x)) t t mfc state
                               :forcep nil)
                      *t*)
               (mfc-relieve-hyp '(mbar x) '((x . x))
                                '(:rewrite foo-when-mbar) '(foo x) 1
                                mfc state :forcep nil)))
      ''nil
    term))

(defthm mf-correct
  (implies (and (mev (meta-extract-contextual-fact
                      '(:typeset (mbar x)) mfc state)
                     a)
                (mev (meta-extract-contextual-fact
                      '(:rw (mbar x) t t) mfc state)
                     a)
                (mev (meta-extract-contextual-fact
                      '(:rw+ (mbar v) ((v . x)) t t) mfc state)
                     a)
                (mev (meta-extract-contextual-fact
                      '(:relieve-hyp (mbar x) ((x . x))
                                     (:rewrite foo-when-mbar) (foo x) 1)
                      mfc state)
                     a))
           (equal (mev term a)
                  (mev (mf term mfc state) a)))
  :hints (("Goal" :in-theory (enable foo)))
  :rule-classes ((:meta :trigger-fns (foo))))

; Before the fix, the following proof of nil succeeded without a forcing round.

(must-fail
 (encapsulate
   ()
   (defthm foo-nil
     (implies (mtrig x) (equal (foo x) nil))
     :rule-classes nil)
   (defthm nil-proved
     nil
     :hints (("Goal" :use (:instance foo-nil (x 'a))
              :in-theory (enable foo mbar mtrig (foo) (mbar) (mtrig))))
     :rule-classes nil)))

; The metafunction still works when the hypothesis is not forced.

(defthm foo-nil-when-mpp
  (implies (and (mtrig x) (mpp x)) (equal (foo x) nil))
  :rule-classes nil)

; Part 2: (< (mval x) 0) in the linear pot-lst, from a linear rule.

(defun mf2 (term mfc state)
  (declare (xargs :stobjs state :verify-guards nil))
  (if (and (equal term '(foo2 x))
           (mfc-ap '(< '0 (mval x)) mfc state :forcep nil))
      ''nil
    term))

(defthm mf2-correct
  (implies (mev (meta-extract-contextual-fact
                 '(:ap (< '0 (mval x))) mfc state)
                a)
           (equal (mev term a)
                  (mev (mf2 term mfc state) a)))
  :hints (("Goal" :in-theory (enable foo2)))
  :rule-classes ((:meta :trigger-fns (foo2))))

; Before the fix, the following proof of nil succeeded without a forcing round.

(must-fail
 (encapsulate
   ()
   (defthm foo2-nil
     (implies (< (mval x) 5) (equal (foo2 x) nil))
     :rule-classes nil)
   (defthm nil-proved
     nil
     :hints (("Goal" :use (:instance foo2-nil (x 'a))
              :in-theory (enable foo2 mval mpp (foo2) (mval) (mpp))))
     :rule-classes nil)))

; The metafunction still works when the hypothesis is not forced.

(defthm foo2-nil-when-mpp
  (implies (and (mpp x) (< (mval x) 5)) (equal (foo2 x) nil))
  :rule-classes nil)
