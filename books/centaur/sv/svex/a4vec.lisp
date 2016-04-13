; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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

(in-package "SV")
(include-book "4vec")
(include-book "centaur/gl/symbolic-arithmetic" :dir :system)
(local (std::add-default-post-define-hook :fix))
(local (xdoc::set-default-parents bit-blasting))


(define aig-list->s ((x   true-listp "AIG list to evaluate.")
                     (env "AIG environment to evaluate it under."))
  :parents (a4vec)
  :returns (ans integerp :rule-classes :type-prescription)
  :short "Evaluate an AIG list and interpret the resulting bits as a signed
  integer, as in @(see gl::bfr-list->s)."
  :enabled t
  :prepwork ((local (in-theory (enable bool->bit))))
  (b* (((mv first rest end) (gl::first/rest/end x)))
    (if end
        (gl::bool->sign (aig-eval first env))
      (logcons (bool->bit (aig-eval first env))
               (aig-list->s rest env)))))

(define aig-list->u ((x   true-listp "AIG list to evaluate.")
                     (env "AIG environment to evaluate it under."))
  :parents (a4vec)
  :returns (ans natp :rule-classes :type-prescription)
  :short "Evaluate an AIG list and interpret the resulting bits as an unsigned
  integer, as in @(see gl::bfr-list->u)."
  :enabled t
  (if (atom x)
      0
    (logcons (bool->bit (aig-eval (car x) env))
             (aig-list->u (cdr x) env))))


(defprod a4vec
  :short "A symbolic 4vec, with lists of AIGs for the upper and lower bits."
  ;; [Jared] might be switch to a regular :tree, but we rely on it being a cons
  ;; for a4veclist-nth, so better to just make it a proper cons.
  :layout :fulltree
  ((upper true-listp "List of AIGs for the upper bits.")
   (lower true-listp "List of AIGs for the lower bits."))
  :long "<p>See @(see a4vec-eval); the semantics are given by @(see
aig-list->s).</p>")


(deflist a4veclist
  :elt-type a4vec
  :true-listp t)


(define a4vec-eval ((x   a4vec-p "Symbolic 4vec to evaluate.")
                    (env         "Environment for @(see aig-eval)."))
  :returns (res 4vec-p "Value of @('x') as a @(see 4vec).")
  :short "Semantics of @(see a4vec)s."
  (b* (((a4vec x)))
    (4vec (aig-list->s x.upper env)
          (aig-list->s x.lower env)))
  ///
  (defthm a4vec-eval-of-a4vec
    (equal (a4vec-eval (a4vec upper lower) env)
           (4vec (aig-list->s upper env)
                 (aig-list->s lower env)))
    :hints(("Goal" :in-theory (enable aig-list->s))))

  (defthm a4vec-eval-of-const
    (implies (syntaxp (quotep x))
             (equal (a4vec-eval x env)
                    (4vec (aig-list->s (a4vec->upper x) env)
                          (aig-list->s (a4vec->lower x) env)))))

  (defthm a4vec-eval-of-var
    (implies (syntaxp (symbolp x))
             (equal (a4vec-eval x env)
                    (4vec (aig-list->s (a4vec->upper x) env)
                          (aig-list->s (a4vec->lower x) env))))))


(define a4veclist-eval ((x a4veclist-p) env)
  :short "Evaluate a list of @(see a4vec)s."
  :returns (vals 4veclist-p)
  (if (atom x)
      nil
    (cons (a4vec-eval (car x) env)
          (a4veclist-eval (cdr x) env)))
  ///
  (defthm len-of-a4veclist-eval
    (equal (len (a4veclist-eval x env))
           (len x))
    :hints(("Goal" :in-theory (enable a4veclist-eval)))))


(define a4vec-constantp ((x a4vec-p))
  (b* (((a4vec x)))
    (and (boolean-listp x.upper)
         (boolean-listp x.lower))))

