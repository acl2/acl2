; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Fails because only one signature function is transparent.
(encapsulate
  ((f1 (x) t :transparent t)
   (f2 (x) t))
  (local (defun f1 (x) x))
  (local (defun f2 (x) x))
  (defthm f1-is-f2
    (equal (f2 x) (f1 x))
    :rule-classes nil))

; Fails similarly to just above
(encapsulate
  (((f1 *) => *)
   ((f2 *) => * :transparent t))
  (local (defun f1 (x) x))
  (local (defun f2 (x) x))
  (defthm f1-is-f2
    (equal (f2 x) (f1 x))
    :rule-classes nil))

; Fails similarly to just above
(encapsulate
  (((f1 *) => * :transparent t)
   ((f2 *) => * :transparent nil))
  (local (defun f1 (x) x))
  (local (defun f2 (x) x))
  (defthm f1-is-f2
    (equal (f2 x) (f1 x))
    :rule-classes nil))

; Fails because parent encapsulate signatures specify transparent but
; sub-encapsulate signature does not.
(encapsulate
  ((f1 (x) t :transparent t)
   (f2 (x) t :transparent t))
  (local (defun f1 (x) x))
  (local (defun f2 (x) x))
  (encapsulate ((f3 (x) t))
    (local (defun f3 (x) x))
    (defthm f3-is-f1
      (equal (f3 x) (f1 x))))
  (defthm f1-is-f2 (or (equal (f2 x) (f1 x))
                       (equal (f2 x) (f2 x)))
    :rule-classes nil))

; Fails because parent encapsulate signatures do not specify transparent but
; sub-encapsulate signature does.
(encapsulate
  ((f1 (x) t)
   (f2 (x) t))
  (local (defun f1 (x) x))
  (local (defun f2 (x) x))
  (encapsulate ((f3 (x) t :transparent t))
    (local (defun f3 (x) x))
    (defthm f3-is-f1
      (equal (f3 x) (f1 x))))
  (defthm f1-is-f2 (or (equal (f2 x) (f1 x))
                       (equal (f2 x) (f2 x)))
    :rule-classes nil))

; As just above, but check that error message uses the singular for the outer
; signature.
(encapsulate
  ((f1 (x) t))
  (local (defun f1 (x) x))
  (encapsulate ((f3 (x) t :transparent t))
    (local (defun f3 (x) x))
    (defthm f3-is-f1
      (equal (f3 x) (f1 x)))))

; Fails because the value of :transparent must be Boolean.
(encapsulate
  ((f1 (x) t :transparent 7)
   (f2 (x) t))
  (local (defun f1 (x) x))
  (local (defun f2 (x) x))
  (defthm f1-is-f2
    (equal (f2 x) (f1 x))
    :rule-classes nil))

; Fails because signature fns can't be transparent for partial-encapsulate.
; The error message comes late, because a partial-encapsulate is just an
; encapsulate with a suitable call of set-unknown-constraints-supporters; so we
; wait till after we see that call, and in fact until pass 2, to cause the
; error.
(partial-encapsulate
 ((f (x) t :transparent t)
  (g (x) t :transparent t))
 nil
 (local (defun f (x) (declare (xargs :guard t)) (consp x)))
 (local (defun g (x) (declare (xargs :guard t)) (consp x)))
 (defthm booleanp-f
   (booleanp (f x))
   :rule-classes :type-prescription))

(defstub f0 (x) t)

(encapsulate
  ((f1 (x) t :transparent t)
   ((f2 *) => * :transparent t))
  (local (defun f1 (x) (f0 x)))
  (local (defun f2 (x) (f0 x)))
  (defthm f2-is-f1
    (implies (f0 x)
             (equal (f2 x) (f1 x)))
    :rule-classes nil))

(defn f3 (x) x)

(defattach f0 f3)

(with-output :off :all ; avoid noisy output when perusing it
  (defevaluator evl evl-list
    ((f0 x))))

(defn meta-fn1 (x)
  (if (f1 x)
      x
    x))

; Error because f0 is a common-anc.
(defthm thm1
  (equal (evl x a)
         (evl (meta-fn1 x) a))
  :rule-classes ((:meta :trigger-fns (nth))))

; Error because we are attaching to f1 but not f2, yet both are transparent
; from the same encapsulate.
(defattach (f1 consp))

; Same error as just above
(defattach (f1 consp) (f2 nil))

; Error because f1 is transparent and f0 was not introduced with it.
(defattach (f1 consp) (f2 consp) (f0 f3))

(defattach (f1 consp) (f2 consp))

; Error: both attachment and erasure
(defattach (f1 consp) (f2 nil))

; Error because defaxiom cannot generate a :meta or :clause-processor rule.
(defaxiom thm1
  (equal (evl x a)
         (evl (meta-fn1 x) a))
  :rule-classes ((:meta :trigger-fns (nth))))

; We could allow the following, since it would unattach f2 as well.  But we
; don't.  That seems like a minor wart, and maybe it's actually for the best:
; after all, we insist on specifying all siblings of a transparent function
; when attaching, so by analogy we make such a requirement when unattaching.
(defattach (f1 nil))

(defattach (f1 nil) (f2 nil))

; OK; restoring attachments
(defattach (f1 consp) (f2 consp))

; OK to do again
;; !! Ouch -- this is weird.  Maybe a pre-existing problem?
#|
ACL2 Observation in ( DEFATTACH (F1 CONSP) ...):  The pre-existing
attachments are being removed for functions F1, F2, F1 and F2, before
adding the requested attachments.
|#
(defattach (f1 consp) (f2 consp))

; Legal this time because attachments to transparent fns eliminate common
; ancestors.
(defthm thm1
  (equal (evl x a)
         (evl (meta-fn1 x) a))
  :rule-classes ((:meta :trigger-fns (nth))))

; Error, since this would create common ancestors for thm1
(defattach (f1 nil) (f2 nil))

(encapsulate
  ((f4 (x) t :transparent t)
   (f5 (x) t :transparent t))
  (local (defun f4 (x) x))
  (local (defun f5 (x) x))
  (defun f6 (x) (f4 x))
  (defthm f5-is-f6
    (implies (f6 x)
             (equal (f5 x) (f6 x)))
    :rule-classes nil))

; Error, since f6 is transparent and introduced in the same encapsulate
(defattach (f4 consp) (f5 consp))

(defattach (f4 consp) (f5 consp) (f6 consp :attach nil))

; I could also test clause-processor rules and meta-extract, but I think the
; above is enough, especially since there is alreay some such testing done by
; community books under books/projects/rp-rewriter/.

;;;;;;;;;;

; Check that in development of the extension of ACL2 for transparent functions,
; we didn't break ancestors checking in the non-transparent case.

(ubt 'f0)

; Error: g0 is ancestral in meta-fn2 and evl.
(progn
  (defstub g0 (x) t)
  (with-output :off :all ; avoid noisy output when perusing it
    (defevaluator evl evl-list
      ((g0 x))))
  (defun meta-fn2 (x)
    (if (g0 x)
        x
      x))
  (defattach g0 consp)
  (defthm thm2
    (equal (evl x a)
           (evl (meta-fn2 x) a))
    :rule-classes ((:meta :trigger-fns (nth))))
  )

; OK; removed the defattach.
(progn
  (defstub g0 (x) t)
  (with-output :off :all ; avoid noisy output when perusing it
    (defevaluator evl evl-list
      ((g0 x))))
  (defun meta-fn2 (x)
    (if (g0 x)
        x
      x))
  (defthm thm2
    (equal (evl x a)
           (evl (meta-fn2 x) a))
    :rule-classes ((:meta :trigger-fns (nth))))
  )

; Error: Illegal just as before except this time defattach is after the meta
; rule.
(defattach g0 consp)

;;;;;;;;;;

; This variant of the example above attaches to a sibling g1 of g0 (in the
; sense that g1 and g0 are introduced in the same encapsulate).  At one stage
; of development of the extension of ACL2 for transparent functions, the
; defattach for g1 below did not cause an error.

(ubt 'g0)

(encapsulate
  ((g0 (x) t)
   (g1 (x) t))
  (local (defun g0 (x) x))
  (local (defun g1 (x) x)))

(progn
  (with-output :off :all ; avoid noisy output when perusing it
    (defevaluator evl evl-list
      ((g0 x))))
  (defun meta-fn2 (x)
    (if (g0 x)
        x
      x))
  (defthm thm2
    (equal (evl x a)
           (evl (meta-fn2 x) a))
    :rule-classes ((:meta :trigger-fns (nth))))
  )

; Both of these cause errors: Illegal just as before except this time defattach
; is after the meta rule.  Note that g0 is canonical and g1 is not, so we test
; both.
(defattach g0 consp)
(defattach g1 consp)

;;;;;;;;;

; The non-trivial encapsulate below contains a meta rule.  But we can't know
; the ancestors of its meta-function, meta-fn2, at the time the rule is
; processed; in particular, g0 is not seen as a common ancestor of meta-fn2 and
; thm2, which would allow subsequent attachment to g0, a violation.  This is a
; fine argument for why :meta rules and :clause-processor rules are illegal
; inside non-trivial encapsulates!

(ubt 'g0)

(defstub g0 (x) t)

(with-output :off :all ; avoid noisy output when perusing it
  (defevaluator evl evl-list
    ((g0 x))))

; Error (see explanation above).
(encapsulate
  ((g1 (x) t)
   ((g2 *) => *)
   (meta-fn2 (x) t))
  (local (defun g1 (x) (g0 x)))
  (local (defun g2 (x) (g0 x)))
  (defthm g2-is-g1
    (implies (g0 x)
             (equal (g2 x) (g1 x)))
    :rule-classes nil)

  (local (defun meta-fn2 (x)
    (if (or (g2 x) (g0 x))
        x
      x)))

  (defthm thm2
    (equal (evl x a)
           (evl (meta-fn2 x) a))
    :rule-classes ((:meta :trigger-fns (nth)))))

; Error (see explanation above), this time with :transparent t.
(encapsulate
  ((g1 (x) t :transparent t)
   ((g2 *) => * :transparent t)
   (meta-fn2 (x) t :transparent t))
  (local (defun g1 (x) (g0 x)))
  (local (defun g2 (x) (g0 x)))
  (defthm g2-is-g1
    (implies (g0 x)
             (equal (g2 x) (g1 x)))
    :rule-classes nil)

  (local (defun meta-fn2 (x)
    (if (or (g2 x) (g0 x))
        x
      x)))

  (defthm thm2
    (equal (evl x a)
           (evl (meta-fn2 x) a))
    :rule-classes ((:meta :trigger-fns (nth)))))

;;;;;;;;;

; The book below (some parts commented out here) was certifiable in ACL2 8.5.
; It exhibits the soundness bug pertaining to the following from :DOC note-8-6.

#|
  Fixed a soundness bug based on rules of class :[meta] or
  :[clause-processor] that are local to an [encapsulate] event with a
  non-nil [signature] list.  A proof of nil in Version_8.5 may be
  found in the [community-books] file,
  books/system/tests/transparent-functions-input.lsp; search for this
  paragraph there.
|#

(ubt 'g0)

; (in-package "ACL2")

(defstub f () t)

(with-output :off :all ; avoid noisy output when perusing it
  (defevaluator evl evl-list
    ((f))))

; This now causes an error.  It was the source of the soundness bug
(encapsulate
  ((my-meta-fn (x) x))
  (local (defun my-meta-fn (x)
           (if (equal x '(f))
               (list 'quote (f))
             x)))
  (defthm my-meta-fn-correct
    (equal (evl x a)
           (evl (my-meta-fn x) a))
    :rule-classes ((:meta :trigger-fns (f)))))

#|

(defun my-meta-fn-impl (x)
  (declare (xargs :guard t))
  (if (equal x '(f))
      (list 'quote (f))
    x))

(defthm lemma-for-defattach
  (equal (evl (my-meta-fn-impl x) a)
         (evl x a))
  :hints (("Goal"
           :in-theory (disable (:e my-meta-fn-impl)
                               my-meta-fn-correct))))

(defattach my-meta-fn my-meta-fn-impl)

(defun constant-nil ()
  (declare (xargs :guard t))
  nil)

(defattach f constant-nil)

(defthm f-is-nil
; proved using my-meta-fn-correct
  (equal (f) nil)
  :rule-classes nil)

(defthm contradiction
  nil
  :hints (("Goal" :use ((:functional-instance
                         f-is-nil
                         (f (lambda () t))))))
  :rule-classes nil)

|#
