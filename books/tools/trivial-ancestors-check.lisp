; Trivial-ancestors-check: replace the ACL2 ancestors check heuristic with a
; simpler one

; Copyright (C) 2013 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

; Very lightly modified April 2013 by Matt K. to accommodate introduction of
; defrec for ancestors.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

; Sometimes the ACL2 ancestors-check heuristic prevents rules from applying
; when you think they should.  Fortunately it's an attachable function, so we
; can make it into a simple loop check without too much trouble.

; The constraint it needs to satisfy:

;; (defthmd ancestors-check-constraint
;;    (implies (and (pseudo-termp lit)
;;                  (ancestor-listp ancestors)
;;                  (true-listp tokens))
;;             (mv-let (on-ancestors assumed-true)
;;                     (ancestors-check lit ancestors tokens)
;;                     (implies (and on-ancestors
;;                                   assumed-true)
;;                              (member-equal-mod-commuting
;;                               lit
;;                               (strip-ancestor-literals ancestors)
;;                               nil))))
;;    :hints (("Goal" :use ancestors-check-builtin-property)))

(local (in-theory (disable mv-nth equal-mod-commuting)))

(defun check-assumed-true-or-false (lit lit-atm ancestors)
  (declare (xargs :guard (and (pseudo-termp lit)
                              (pseudo-termp lit-atm)
                              (ancestor-listp ancestors))))
  (cond ((endp ancestors) (mv nil nil))
        ((ancestor-binding-hyp-p (car ancestors))
         (check-assumed-true-or-false lit lit-atm (cdr ancestors)))
        ((equal-mod-commuting lit
                              (access ancestor (car ancestors) :lit) ;; first lit
                              nil)
         (mv t t))
        ((equal-mod-commuting lit-atm
                              (access ancestor (car ancestors) :atm) ;; atom of first lit
                              nil)
         (mv t nil))
        (t (check-assumed-true-or-false lit lit-atm (cdr ancestors)))))

(defthmd check-assumed-true-or-false-ok
  (mv-let (present true)
    (check-assumed-true-or-false lit lit-atm ancestors)
    (implies (and present true)
             (member-equal-mod-commuting
              lit (strip-ancestor-literals ancestors) nil))))

(in-theory (disable check-assumed-true-or-false))

(defun trivial-ancestors-check (lit ancestors tokens)
  (declare (xargs :guard (and (pseudo-termp lit)
                              (ancestor-listp ancestors)
                              (true-listp tokens)))
           (ignorable tokens))
  (cond ((endp ancestors)
         (mv nil nil))
        (t (mv-let (not-flg lit-atm)
             (strip-not lit)
             (declare (ignore not-flg))
             (check-assumed-true-or-false lit lit-atm ancestors)))))

(defthmd trivial-ancestors-check-ok
  (mv-let (present true)
    (trivial-ancestors-check lit ancestors tokens)
    (implies (and present true)
             (member-equal-mod-commuting
              lit (strip-ancestor-literals ancestors) nil)))
  :hints(("Goal" :in-theory (enable check-assumed-true-or-false-ok))))

(in-theory (disable trivial-ancestors-check))

;; test
(local (defattach (ancestors-check trivial-ancestors-check)
         :system-ok t
         :hints (("goal" :in-theory '(trivial-ancestors-check-ok)))))

;; This macro makes a local event, but you can also do
;; (local (include-book "centaur/misc/defeat-ancestors" :dir :system))
;; (local (use-trivial-ancestors-check))
;; if you want this book to be included only locally.
(defmacro use-trivial-ancestors-check ()
  '(local (defattach (ancestors-check trivial-ancestors-check)
            :system-ok t
            :hints (("goal" :in-theory '(trivial-ancestors-check-ok))))))


(defxdoc use-trivial-ancestors-check
  :short "Override ACL2's built-in ancestors check heuristic with a simpler and less surprising one."
  :parents (proof-automation) ;; ???
  :long "<p>Usage: as an embeddable event,</p>

@({
 (include-book \"tools/trivial-ancestors-check\" :dir :system)
 (use-trivial-ancestors-check)
 })
<p>or</p>
@({
 (local (include-book \"tools/trivial-ancestors-check\" :dir :system))
 (local (use-trivial-ancestors-check)).
 })

<p>(Note: @('use-trivial-ancestors-check') expands to a local event, but you
can still wrap it in local, in which case the trivial-ancestors-check book may
be included locally.)</p>

<p>ACL2 has a heuristic called @('ancestors-check') which it uses to
prevent loops in backchaining during rewriting.  The @('ancestors'), in this
context, are the sequence of hyps we have backchained to in order to get to the
one we are currently trying to relieve.  Among other things, ACL2's built in
ancestors check decides whether the current hyp is more complicated than any
ancestral hyp, and gives up on backchaining if so.  Occasionally this can cause
a rewriting strategy to mysteriously fail to work.  Fortunately, ACL2 allows
its default ancestors check to be replaced by an attachment.</p>

<p>Running @('(use-trivial-ancestors-check)') replaces the default ancestors
check with one that does much less: it only checks whether the current hyp
occurs, exactly or negated, in the ancestors, and doesn't try to prevent
backchaining to more complicated hyps.</p>

<p>This could cause rewriting to fail due to a chain of increasingly
complicated hyps.  But when we tried replacing ACL2's default heuristic with
this new one, we only found a couple of examples in the regression where this
was the case, and these were due to (in our view) bad rules.  So in practice,
this seems to be fairly undisruptive.</p>")

(defpointer trivial-ancestors-check use-trivial-ancestors-check)
