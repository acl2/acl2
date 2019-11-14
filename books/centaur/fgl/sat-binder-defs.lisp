; FGL - A Symbolic Simulation Framework for ACL2
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

(include-book "arith-base")
(include-book "syntax-bind")
(include-book "def-fgl-rewrite")



(define sat-check-raw (ans config x)
  (declare (ignore config))
  (case ans
    (:sat :sat)
    (:unsat (if x :failed :unsat))
    (t :failed))
  ///
  (disable-definition sat-check-raw)
  (defthm sat-check-not-unsat
    (implies x
             (not (equal (sat-check-raw ans config x) :unsat))))

  (defmacro sat-check-raw! (&rest args)
    `(binder (sat-check-raw . ,args))))

(define sat-check-with-witness-raw (ans config x)
  (declare (ignore config))
  (b* (((mv status ctrex) (non-exec ans)))
    (case status
      (:sat (if (implies ctrex x)
                (mv :sat ctrex)
              (mv :failed nil)))
      (:unsat (mv (if x :failed :unsat) nil))
      (t (mv :failed nil))))
  ///
  (disable-definition sat-check-with-witness-raw)
  (defthm sat-check-with-witness-not-unsat
    (implies x
             (not (equal (mv-nth 0 (sat-check-with-witness-raw ans config x)) :unsat))))

  (defthm sat-check-with-witness-correct
    (implies (and (mv-nth 1 (sat-check-with-witness-raw ans config x))
                  (not x))
             (not (equal (mv-nth 0 (sat-check-with-witness-raw ans config x)) :sat))))

  (defmacro sat-check-with-witness-raw! (&rest args)
    `(binder (sat-check-with-witness-raw . ,args))))

(define sat-check (ans config x)
  :enabled t
  (sat-check-raw ans config x)
  ///
  (disable-definition sat-check)
  (defthm sat-check-impl
    (implies (equal ans (sat-check-raw! ans1 config (if x t nil)))
             (equal (sat-check ans config x) ans))
    :hints(("Goal" :in-theory (enable sat-check-raw)))
    :rule-classes nil)

  (add-fgl-brewrite sat-check-impl)

  (defmacro sat-check! (&rest args)
    `(binder (sat-check . ,args))))


(define sat-check-with-witness (ans config x)
  :enabled t
  (sat-check-with-witness-raw ans config x)
  ///
  (disable-definition sat-check-with-witness)
  (defthm sat-check-with-witness-impl
    (implies (equal ans (sat-check-with-witness-raw! ans1 config (if x t nil)))
             (equal (sat-check-with-witness ans config x) ans))
    :hints(("Goal" :in-theory (enable sat-check-with-witness-raw)))
    :rule-classes nil)

  (add-fgl-brewrite sat-check-with-witness-impl)

  (defmacro sat-check-with-witness! (&rest args)
    `(binder (sat-check-with-witness . ,args))))

(def-fgl-rewrite fgl-sat-check-impl
  (equal (fgl-sat-check config x)
         (b* ((xbool (if x t nil))
              (status (sat-check-raw! status config xbool)))
           (if (equal status :unsat) nil xbool)))
  :hints(("Goal" :in-theory (enable sat-check-raw fgl-sat-check))))
