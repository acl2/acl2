; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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

(in-package "FGL")

(include-book "def-gl-rewrite")
(include-book "syntax-bind")
(include-book "gl-object")


(local (in-theory (enable if!)))

(def-gl-branch-merge if-of-atomic-consts
  (implies (syntaxp (b* (((g-concrete then))
                         ((g-concrete else)))
                      (and (atom then.val)
                           (atom else.val)
                           (not (integerp then.val))
                           (not (integerp else.val))
                           (not (and (booleanp then.val) (booleanp else.val))))))
           (equal (if test (concrete then) (concrete else))
                  (if! test then else))))

(def-gl-branch-merge if-of-atomic-const/if
  (implies (syntaxp (and (atom (g-concrete->val then))
                         (gl-object-case else :g-ite)))
           (equal (if test (concrete then) else)
                  (if! test then else))))

(def-gl-branch-merge if-of-ifs
  (equal (if test (if test2 thenthen thenelse)
           (if test3 elsethen elseelse))
         (if! test
              (if! test2 thenthen thenelse)
              (if! test3 elsethen elseelse))))

(def-gl-rewrite equal-of-if
  (equal (equal (if test then else) x)
         (if test (equal then x)
           (equal else x))))

(def-gl-rewrite if-integer-nil
  (equal (if test (int then) nil)
         (if! test (int then) nil)))

(def-gl-branch-merge if-integer-nil-integer
  (equal (if test (if test2 (int then) nil) (int else))
         (if! (or (not test) test2) (if test (int then) (int else)) nil)))

(def-gl-branch-merge if-integer-nil-if-integer-nil
  (equal (if test (if test2 (int then) nil) (if test3 (int else) nil))
         (if! (if test test2 test3)
              (if test (int then) (int else))
              nil)))

(def-gl-rewrite intcar-of-if
  (equal (intcar (if test then else))
         (if test (intcar then) (intcar else))))

(def-gl-rewrite intcdr-of-if
  (equal (intcdr (if test then else))
         (if test (intcdr then) (intcdr else))))         
