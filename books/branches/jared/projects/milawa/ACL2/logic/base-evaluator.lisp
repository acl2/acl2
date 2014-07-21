; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "terms")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund logic.initial-arity-table ()
  ;; We create the arity table for the base functions.
  (declare (xargs :guard t))
  '((if . 3)
    (equal . 2)
    (consp . 1)
    (cons . 2)
    (car . 1)
    (cdr . 1)
    (symbolp . 1)
    (symbol-< . 2)
    (natp . 1)
    (< . 2)
    (+ . 2)
    (- . 2)
    ;(* . 2)
    ;(floor . 2)
    ;(mod . 2)
    ;(expt . 2)
    ;(bitwise-shl . 2)
    ;(bitwise-shr . 2)
    ;(bitwise-and . 2)
    ;(bitwise-or . 2)
    ;(bitwise-xor . 2)
    ;(bitwise-nth . 2)
    ))

(defthm logic.arity-tablep-of-logic.initial-arity-table
  (equal (logic.arity-tablep (logic.initial-arity-table))
         t))

(in-theory (disable (:executable-counterpart logic.initial-arity-table)))





(defund logic.base-evaluablep (x)
  ;; We decide if a term is of the form (f c1 ... cn), where f is one of the
  ;; base functions, c1...cn are constants, and the arity of f is n.
  (declare (xargs :guard (logic.termp x)))
  (and (logic.functionp x)
       (let ((fn   (logic.function-name x))
             (args (logic.function-args x)))
         (let ((entry (lookup fn (logic.initial-arity-table))))
           (and entry
                (logic.constant-listp args)
                (tuplep (cdr entry) args))))))

(defthm booleanp-of-logic.base-evaluablep
  (equal (booleanp (logic.base-evaluablep x))
         t)
  :hints(("Goal" :in-theory (e/d (logic.base-evaluablep)
                                 (forcing-lookup-of-logic.function-name
                                  forcing-true-listp-of-logic.function-args)))))

(defthm forcing-logic.functionp-when-logic.base-evaluablep
  (implies (and (logic.base-evaluablep x)
                (force (logic.termp x)))
           (equal (logic.functionp x)
                  t))
  :hints(("Goal" :in-theory (enable logic.base-evaluablep))))

(defthm logic.constant-listp-of-logic.function-args-when-logic.base-evaluablep
  (implies (and (logic.base-evaluablep x)
                (force (logic.termp x)))
           (equal (logic.constant-listp (logic.function-args x))
                  t))
  :hints(("Goal" :in-theory (enable logic.base-evaluablep logic.function-args))))

(defthm lookup-logic.function-name-in-logic.initial-arity-table-when-logic.base-evaluablep
  (implies (and (logic.base-evaluablep x)
                (force (logic.termp x)))
           (equal (lookup (logic.function-name x) (logic.initial-arity-table))
                  (cons (logic.function-name x)
                        (len (logic.function-args x)))))
  :hints(("Goal" :in-theory (e/d (logic.base-evaluablep)
                                 (forcing-lookup-of-logic.function-name)))))


(defthmd lemma-for-logic.term-atblp-when-logic.base-evaluablep
  (implies (and (logic.function-namep fn)
                (memberp fn (domain (logic.initial-arity-table)))
                (true-listp args)
                (logic.constant-listp args)
                (equal (len args) (cdr (lookup fn (logic.initial-arity-table)))))
           (equal (logic.term-atblp (logic.function fn args) (logic.initial-arity-table))
                  t)))

(defthm logic.term-atblp-when-logic.base-evaluablep
  (implies (and (logic.base-evaluablep term)
                (force (logic.termp term)))
           (equal (logic.term-atblp term (logic.initial-arity-table))
                  t))
  :hints(("Goal"
          :in-theory (enable logic.base-evaluablep
                             lemma-for-logic.term-atblp-when-logic.base-evaluablep)
          :use ((:instance lemma-for-logic.term-atblp-when-logic.base-evaluablep
                            (fn (logic.function-name term))
                            (args (logic.function-args term)))))))


(defthm logic.base-evaluablep-when-preliminary-fn-applied-to-constants
  (implies (and (logic.function-namep fn)
                (memberp fn (domain (logic.initial-arity-table)))
                (true-listp args)
                (logic.constant-listp args)
                (equal (len args) (cdr (lookup fn (logic.initial-arity-table)))))
           (equal (logic.base-evaluablep (logic.function fn args))
                  t))
  :hints(("Goal" :in-theory (enable logic.base-evaluablep))))

(defthm logic.base-evaluablep-of-logic.function-equal
  (equal (logic.base-evaluablep (logic.function 'equal args))
         (and (tuplep 2 args)
              (logic.constant-listp args)))
  :hints(("Goal" :in-theory (enable logic.base-evaluablep logic.initial-arity-table))))





(defund logic.base-evaluator (x)
  ;; We run a base function on its arguments and return the result as a quoted
  ;; constant (i.e., a logic.constantp).
  (declare (xargs :guard (and (logic.termp x)
                              (logic.base-evaluablep x))))
  (let ((fn   (logic.function-name x))
        (vals (logic.unquote-list (logic.function-args x))))
    (list 'quote
          (cond ((equal fn 'if)          (if (first vals) (second vals) (third vals)))
                ((equal fn 'equal)       (equal (first vals) (second vals)))
                ((equal fn 'consp)       (consp (first vals)))
                ((equal fn 'cons)        (cons (first vals) (second vals)))
                ((equal fn 'car)         (car (first vals)))
                ((equal fn 'cdr)         (cdr (first vals)))
                ((equal fn 'symbolp)     (symbolp (first vals)))
                ((equal fn 'symbol-<)    (symbol-< (first vals) (second vals)))
                ((equal fn 'natp)        (natp (first vals)))
                ((equal fn '<)           (< (first vals) (second vals)))
                ((equal fn '+)           (+ (first vals) (second vals)))
                ((equal fn '-)           (- (first vals) (second vals)))
                ;((equal fn '*)           (* (first vals) (second vals)))
                ;((equal fn 'expt)        (expt (first vals) (second vals)))
                ;((equal fn 'floor)       (floor (first vals) (second vals)))
                ;((equal fn 'mod)         (mod (first vals) (second vals)))
                ;((equal fn 'bitwise-shl) (bitwise-shl (first vals) (second vals)))
                ;((equal fn 'bitwise-shr) (bitwise-shr (first vals) (second vals)))
                ;((equal fn 'bitwise-and) (bitwise-and (first vals) (second vals)))
                ;((equal fn 'bitwise-or)  (bitwise-or (first vals) (second vals)))
                ;((equal fn 'bitwise-xor) (bitwise-xor (first vals) (second vals)))
                ;((equal fn 'bitwise-nth) (bitwise-xor (first vals) (second vals)))
                ))))

(defthm forcing-logic.constantp-of-logic.base-evaluator
  (equal (logic.constantp (logic.base-evaluator term))
         t)
  :hints(("Goal" :in-theory (enable logic.initial-arity-table logic.base-evaluator))))

(defthm forcing-logic.constantp-of-logic.base-evaluator-free
  ;; BOZO move to base evaluator
  (implies (equal free (logic.base-evaluator term))
           (equal (logic.constantp free)
                  t)))

(defthm logic.base-evaluator-of-logic.function-equal
  (equal (logic.base-evaluator (logic.function 'equal args))
         (list 'quote (equal (logic.unquote (first args))
                             (logic.unquote (second args)))))
  :hints(("Goal" :in-theory (enable logic.base-evaluator))))
