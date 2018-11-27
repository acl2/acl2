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

(include-book "ihs/basic-definitions" :dir :system)
(include-book "std/basic/arith-equiv-defs" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/baselists" :dir :system)
(local (std::add-default-post-define-hook :fix))

(fty::deffixequiv acl2::bool->bit$inline :args ((x booleanp)))

;; Get the integer value of a bitvector represented as a Boolean list.  LSB first.
(define bools->int ((x boolean-listp))
  (mbe :logic (if (atom (cdr x))
                  (- (bool->bit (car x)))
                (logcons (bool->bit (car x))
                         (bools->int (cdr x))))
       :exec (cond ((atom x) 0)
                   ((atom (cdr x)) (- (bool->bit (car x))))
                   (t (logcons (bool->bit (car x))
                               (bools->int (cdr x))))))
  ///
  (local (in-theory (enable acl2::boolean-list-fix))))

;; Like logcons, but takes a Boolean as the first element rather than an
;; integer.  For convenience in creating rewrite rules.  Unify algorithm treats
;; this specially.
(define intcons ((b booleanp)
                 (x integerp))
  :returns (val)
  :enabled t
  (logcons (bool->bit b) x))


;; Same as intcons, but will unify with any integer as opposed to just ones
;; that (syntactically) appear to have more than 1 bit.
(define intcons* ((b booleanp)
                  (x integerp))
  :returns (val)
  :enabled t
  (logcons (bool->bit b) x))

;; Returns 0 or -1 depending on B.  Treated specially by the unification
;; algorithm, matching 0 and -1 as well as symbolic integers that syntactically
;; have only 1 bit.
(define endint ((b booleanp))
  :returns (val)
  :enabled t
  (- (bool->bit b)))


