; equal-by-g.lisp -- theorem for pick-a-point proofs of record equality
; Copyright (C) 2011-2014 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "records")

; This book should generally not be included; most of the time you should
; instead include the book equal-by-g, instead.  See equal-by-g.lisp for
; general notes and usage information.
;
; This book contains the supporting definitions and theorems.  We only locally
; include these in equal-by-g.lisp.
;
; You might occasionally want to include this file directly, to get at the
; G-WORSEGUY function and the properties about it.


; We begin with a constructive witness that can find a mismatch between two
; well-formed records (i.e., between two valid rcdp's).  Our badguy says what
; kind of mismatch it has found.

(local (defthm rcdp-of-cdr
         (implies (rcdp x)
                  (rcdp (cdr x)))))


(defun g-badguy (x y)
  (cond ((atom x)
         (if (atom y)
             nil
           (cons :extra-in-y (car y))))
        ((atom y)
         (cons :extra-in-x (car x)))
        ((equal (car x) (car y))
         (g-badguy (cdr x) (cdr y)))
        ((<< (caar x) (caar y))
         (cons :extra-in-x (car x)))
        ((equal (caar x) (caar y))
         (cons :mismatch (car x)))
        (t
         (cons :extra-in-y (car y)))))


; Now we just have a bunch of cases to deal with the different kinds of
; problems that the g-badguy might have reported.

(encapsulate
  ()
  (local (defthm l0
           (implies (and (<< (cadr (g-badguy x y)) a)
                         (equal (car (g-badguy x y)) :extra-in-x)
                         (rcdp x)
                         (<< b (caar x)))
                    (not (<< a b)))))

  (defthm g-badguy-lookup-in-x-when-extra-in-x
    (implies (and (equal (car (g-badguy x y)) :extra-in-x)
                  (rcdp x)
                  (rcdp y))
             (g-aux (cadr (g-badguy x y)) x))
    :hints(("Goal" :do-not '(generalize fertilize)))))

(encapsulate
  ()
  (local (defthm l0
           (implies (and (equal (car (g-badguy x y)) :extra-in-x)
                         (<< a (caar x))
                         (<< (cadr (g-badguy x y)) a)
                         (rcdp x))
                    (not (<< a (caar y))))))

  (defthm g-badguy-lookup-in-y-when-extra-in-x
    (implies (and (equal (car (g-badguy x y)) :extra-in-x)
                  (rcdp x)
                  (rcdp y))
             (and (not (g-aux (cadr (g-badguy x y)) y))))
    :hints(("Goal" :do-not '(generalize fertilize)))))

(encapsulate
  ()
  (local (defthm l0
           (implies (and (<< (cadr (g-badguy x y)) a)
                         (equal (car (g-badguy x y)) :extra-in-y)
                         (<< b (caar x))
                         (rcdp y)
                         (<< b (caar y)))
                    (not (<< a b)))))

  (defthm g-badguy-lookup-in-y-when-extra-in-y
    (implies (and (equal (car (g-badguy x y)) :extra-in-y)
                  (rcdp x)
                  (rcdp y))
             (g-aux (cadr (g-badguy x y)) y))
    :hints(("Goal" :do-not '(generalize fertilize)))))

(encapsulate
  ()
  (local (defthm l0
           (implies (and (equal (car (g-badguy x y)) :extra-in-y)
                         (<< a (caar x))
                         (<< (cadr (g-badguy x y)) a)
                         (rcdp y))
                    (not (<< a (caar y))))))

  (defthm g-badguy-lookup-in-x-when-extra-in-y
    (implies (and (equal (car (g-badguy x y)) :extra-in-y)
                  (rcdp x)
                  (rcdp y))
             (not (g-aux (cadr (g-badguy x y)) x)))
    :hints(("Goal" :do-not '(generalize fertilize)))))

(encapsulate
  ()
  (local (defthm l0
           (implies (and (<< (cadr (g-badguy x y)) a)
                         (equal (car (g-badguy x y)) :mismatch)
                         (rcdp x)
                         (rcdp y)
                         (<< b (caar x))
                         (<< b (caar y)))
                    (not (<< a b)))))

  (local (defthm l1
           (implies (and (equal (car (g-badguy x y)) :mismatch)
                         (rcdp x)
                         (rcdp y)
                         (<< a (caar x))
                         (<< (cadr (g-badguy x y)) a))
                    (not (<< a (caar y))))))

  (defthm g-badguy-mismatch-when-mismatch
    (implies (and (equal (car (g-badguy x y)) :mismatch)
                  (rcdp x)
                  (rcdp y))
             (equal (equal (g-aux (cadr (g-badguy x y)) x)
                           (g-aux (cadr (g-badguy x y)) y))
                    nil))
    :hints(("goal" :do-not '(generalize fertilize)))))


; It's easy to see that these are the only cases, and hence it is clear that
; the g-badguy works and if it reports a mismatch, it really is a mismatch.

(defthm g-badguy-cases
  (or (not (g-badguy x y))
      (equal (car (g-badguy x y)) :mismatch)
      (equal (car (g-badguy x y)) :extra-in-x)
      (equal (car (g-badguy x y)) :extra-in-y))
  :rule-classes nil)

(defthm g-aux-of-g-badguy
  (implies (and (g-badguy x y)
                (rcdp x)
                (rcdp y))
           (not (equal (g-aux (cadr (g-badguy x y)) x)
                       (g-aux (cadr (g-badguy x y)) y))))
  :hints(("Goal"
          :do-not-induct t
          :do-not '(eliminate-destructors generalize fertilize)
          :use ((:instance g-badguy-cases)))))


; The other critical fact is that the g-badguy always finds a mismatch between
; any non-equal records.  This follows from its definition.

(defthm g-badguy-unless-equal
  (implies (and (not (equal x y))
                (rcdp x)
                (rcdp y))
           (g-badguy x y)))



; The g-badguy itself isn't sufficient because we need to deal with ill-formed
; records and the whole invertible mapping trick.  So, the "g-worseguy" is like
; the g-badguy but carries out the mapping if necessary.

(defun g-worseguy (x y)
  (g-badguy (acl2->rcd x)
            (acl2->rcd y)))

(defthm acl2->rcd-returns-rcdp
  (rcdp (acl2->rcd x))
  :hints(("Goal" :in-theory (enable acl2->rcd))))


; From the main proof about the g-badguy, it follows that if the g-worseguy says
; there is a mismatch, it's a true mismatch for G.

(defthm g-worseguy-finds-counterexample
  (implies (g-worseguy x y)
           (not (equal (g (cadr (g-worseguy x y)) x)
                       (g (cadr (g-worseguy x y)) y))))
  :hints(("Goal" :in-theory (enable g))))


; All that remains is to show that the g-worseguy always finds a mismatch for
; any non-equal objects.  We can approach this by cases.
;
; 1. Suppose X and Y are well-formed records, i.e., (not (IFRP X)) and (not (IFRP
; Y)).  Then they are both RCDP's, and the ACL2->RCD conversions are the
; identity, and so (g-worseguy x y) is just (g-badguy x y) and we're since we know
; that g-badguy finds a mismatch when given non-equal RCDP's.
;
; 2. Suppose X and Y are both ill-formed records, i.e., (IFRP X) and (IFRP Y).
; Then, the ACL2->RCD conversions will turn them both into RCDP's, in
; particular ((NIL . X)) and ((NIL . Y)).  Obviously these disagree about the
; value of the key NIL when X != Y, so we're done.
;
; 3. WLOG, suppose X is a well-formed record but Y is not.  Then, the ACL2->RCD
; conversion will leave X alone, but will turn Y into ((NIL . Y)).  We need to
; show that G-BADGUY will find a mismatch on these RCDP's.  Well, above we proved
; that that g-badguy always finds a mismatch between two RCDP's unless they're
; equal, so it would suffice to show that X is not equal to ((NIL . Y)).  And
; this is trivial: since Y is ill-formed, ((NIL . Y)) is ill-formed, and since
; above we assumed X was well-formed, this cannot be.

(encapsulate
  ()
  (local (defthm rcdp-unless-ifrp
           (implies (not (ifrp x))
                    (rcdp x))))

  (local (defthm main-lemma-for-case-3
           (implies (and (not (ifrp x)) ;; it therefore must be an rcdp.
                         (ifrp y))
                    (not (equal x (list (cons nil y)))))))

  (local (defthm corollary-for-case-3
           (implies (and (not (ifrp x)) ;; it therefore must be an rcdp.
                         (ifrp y))
                    (g-badguy x (list (cons nil y))))
           :hints(("Goal"
                   :in-theory (disable g-badguy-unless-equal)
                   :use ((:instance g-badguy-unless-equal
                                    (x x)
                                    (y (list (cons nil y)))))))))

  (defthm g-worseguy-unless-equal
    (implies (not (equal x y))
             (g-worseguy x y))
    :hints(("Goal"
            :in-theory (enable acl2->rcd ifrp)
            :do-not-induct t
            :do-not '(generalize fertilize)))))


