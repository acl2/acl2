; MV-NTH Meta Rule
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "ACL2")

(defevaluator eval-for-mv-nth eval-for-mv-nth-list
  ((mv-nth n x)
   (cons a b)))

(defn mv-nth-eval-rec (n x orig)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (case-match
        x
        (('cons a . &) a)
        (('quote (const . &) . &) (list 'quote const))
        (& orig))
    (case-match
      x
      (('cons & d . &) (mv-nth-eval-rec (1- n) d orig))
      (('quote const . &) (list 'quote (ec-call (nth n const))))
      (& orig))))

(defn mv-nth-eval-fn (x)
  (declare (xargs :guard t))
  (case-match
    x
    (('mv-nth ('quote n . &) rst . &)
     (if (natp n)
         (mv-nth-eval-rec n rst x)
       x))
    (& x)))

(defthm eval-for-mv-nth-rec-thm
  (implies (equal (eval-for-mv-nth x a)
                  (mv-nth n (eval-for-mv-nth term a)))
           (equal (eval-for-mv-nth (mv-nth-eval-rec n term x) a)
                  (mv-nth n (eval-for-mv-nth term a))))
  :hints (("Goal" :induct (mv-nth-eval-rec n term x))))

(defthm mv-nth-cons-meta
  (equal (eval-for-mv-nth x a)
         (eval-for-mv-nth (mv-nth-eval-fn x) a))
  :rule-classes ((:meta :trigger-fns (mv-nth))))

(defthm mv-nth-of-cons
  (implies (syntaxp (quotep n))
           (equal (mv-nth n (cons a b))
                  (if (zp n) a (mv-nth (1- n) b)))))

(in-theory (disable mv-nth mv-nth-cons-meta))
