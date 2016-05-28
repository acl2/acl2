; Copyright (C) 2015, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Thanks to Mark Greenstreet, Dave Greve, Dmitry Nadezhin, Yan Peng for
; contributing to this book.

; This book defines a computed hint; see :doc hint-wrapper.  Evaluate the
; following in order to install hint-wrapper as a default hint (or, you can use
; this computed hint directly instead).

;    (add-default-hints '((hint-wrapper-hint clause)))

(in-package "ACL2")

(defun hint-wrapper (x)
  (declare (ignore x)
           (xargs :guard t))
  t)

(defthm hint-wrapper-forward
; Probably not needed when tau-system is active.
  (implies (not (hint-wrapper x))
           nil)
  :rule-classes :forward-chaining)

(in-theory (disable (:d hint-wrapper)
                    (:e hint-wrapper)
                    (:t hint-wrapper)))

; (not (hint-wrapper '(:in-theory ... : use ...)))
; (not (hint-wrapper (my-hint-keyword-alist)))

(program)

(defun extract-hint-wrapper (cl)

; Returns kwd-alist if cl contains a literal
;   (not (hint-wrapper (quote kwd-alist)))
; else nil.

  (cond ((endp cl) nil)
        (t (let ((lit (car cl)))
             (case-match lit
               (('not ('hint-wrapper ('quote kwd-alist)))
                kwd-alist)
               (& (extract-hint-wrapper (cdr cl))))))))

(defun hint-wrapper-hint (cl)
  (let ((kwd-alist (extract-hint-wrapper cl)))
    (cond (kwd-alist
           (mv-let (pre post)
             (split-keyword-alist :expand kwd-alist)
             (cond
              (post ; then there was already an :expand hint; splice one in
               (assert$ (eq (car post) :expand)
                        `(:computed-hint-replacement
                          t
                          ,@pre
                          :expand ,(cons `(hint-wrapper ',kwd-alist)
                                         (cadr post))
                          ,@post)))
              (t ; simply extend kwd-alist
                 `(:computed-hint-replacement
                   t
                   :expand (hint-wrapper ',kwd-alist)
                   ,@kwd-alist)))))
          (t nil))))

(logic)

(local (progn ; some tests

(defund foo (x)
  (cons x x))

(defthm test1
  (implies (hint-wrapper '(:in-theory (enable foo)))
           (equal (foo y) (cons y y)))
  :hints ((hint-wrapper-hint clause))
  :rule-classes nil)

(add-default-hints '((hint-wrapper-hint clause)))

(defthm test2 ; same as test1, but with default hint
  (implies (hint-wrapper '(:in-theory (enable foo)))
           (equal (foo y) (cons y y)))
  :rule-classes nil)

(defthm test3 ; same as above, with more hint-wrappers
  (implies (and (hint-wrapper '(:in-theory (enable mv-nth)))
                (hint-wrapper '(:in-theory (enable foo)))
                (hint-wrapper '(:in-theory (enable nth))))
           (equal (foo y) (cons y y)))
  :rule-classes nil)

(defthm test4 ; same as above (:expand hint isn't relevant)
  (implies (and (hint-wrapper '(:in-theory (enable mv-nth)))
                (hint-wrapper '(:in-theory (enable foo)))
                (hint-wrapper '(:in-theory (enable nth))))
           (equal (foo y) (cons y y)))
  :hints (("Goal" :expand ((append x y))))
  :rule-classes nil)

))

(include-book "xdoc/top" :dir :system)

(defxdoc hint-wrapper
  :parents (hints)
  :short "Supply hints in the statement of a theorem"
  :long "<p>Using the @(see computed-hints) mechanism, it is possible to place
 @(see hints) in the hypothesis of a theorem.  The @('hint-wrapper') utility
 implements this capability.  Simply do the following:</p>

 @({
 (include-book \"hints/hint-wrapper\" :dir :system)
 (add-default-hints '((hint-wrapper-hint clause)))
 })

 <p>The @(tsee include-book) above defines a function of one argument,
 @('hint-wrapper'), that always returns @('t') but has following special
 property.  When ACL2 attempts to prove a theorem with a hypothesis that is a
 call of @('hint-wrapper') on a quoted hint keyword alist &mdash; that is, a
 form @('(quote (:key1 val1 ... :keyn valn))') &mdash; then the hints @('(:key1
 val1 ... :keyn valn)') will be applied.</p>

 <p>The following example illustrates the use of this @('hint-wrapper')
 mechanism.  The form @('(add-default-hints '((hint-wrapper-hint clause)))')
 installs this mechanism as a default hint, arranging that the mechanism is
 applied automatically.  In this example, the final @('thm') succeeds because
 the default hint extracts the indicated @(':')@(tsee in-theory) hint from the
 @('hint-wrapper') call in the hypothesis.</p>

 @({
 (defund foo (x)
   (cons x x))

 (thm ; FAILS, because foo is disabled
   (equal (foo y) (cons y y)))

 (add-default-hints '((hint-wrapper-hint clause)))

 (thm ; SUCCEEDS, using hint-wrapper mechanism (default hint hint-wrapper-hint)
   (implies (hint-wrapper '(:in-theory (enable foo)))
            (equal (foo y) (cons y y))))
 })

 <p>The process described above is actually applied to the first suitable such
 hypothesis, which will be expanded away; on subsequent passes through the
 waterfall (see @(see hints-and-the-waterfall)) that process will be applied to
 the first remaining such hypothesis, and so on.  For the following example,
 assume that the above @(tsee defund) and @(tsee add-default-hints) calls have
 been evaluated.  Initially, the indicated (though useless) @(':expand') hint
 will be applied, since explicit hints on goals take priority over default
 hints.  (See @(see override-hints) for how to avoid this prioritization.)
 Next, the first @('hint-wrapper') call will be applied; it is, of course,
 useless, since @(tsee mv-nth) has nothing to do with this theorem.  That first
 @('hint-wrapper') call is expanded away, producing a subgoal, @('\"Goal'\"'),
 with the remaining two @('hint-wrapper') hypotheses.  The first of these two
 provides the hint to enable @('foo'), which completes the proof.</p>

 @({
 (thm
   (implies (and (hint-wrapper '(:in-theory (enable mv-nth)))
                 (hint-wrapper '(:in-theory (enable foo)))
                 (hint-wrapper '(:in-theory (enable nth))))
            (equal (foo y) (cons y y)))
   :hints ((\"Goal\" :expand ((append x y)))))
 })

 <p>This @('hint-wrapper') mechanism can actually be applied explicitly, rather
 than using a computed hint.  Even if we omit the call of @(tsee
 add-default-hints) displayed above, the following succeeds.</p>

 @({
 (thm
   (implies (hint-wrapper '(:in-theory (enable foo)))
            (equal (foo y) (cons y y)))
   :hints ((hint-wrapper-hint clause)))
 })

 <p>The implementation of the @('hint-wrapper') mechanism is rather
 straightforward, and could be useful for understanding @(see computed-hints)
 in general.  See community book @('hints/hint-wrapper.lisp').</p>")
