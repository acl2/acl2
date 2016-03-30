; Copyright (C) 2016, ForrestHunt, Inc.
; Written by Matt Kaufmann, January, 2016
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Thanks to David Rager for posing a problem for which this has provided a
; solution.  His problem was to prove equality of two very large terms that, in
; fact, were equal -- but not EQ.  David's idea was to use HONS-COPY on those
; terms so that indeed they are EQ.  Here we implement that idea using a meta
; rule.  David has used this meta rule successfully, but to date we don't have
; a small illustrative example -- documentation may come later if such an
; example is discovered.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defun hons-equal! (x y)
  (declare (xargs :guard t))
  (equal x y))

(defun hons-equal!-elim (x)
  (cond ((and (nvariablep x)
              (eq (ffn-symb x) 'hons-equal!))
         (cond ((hons-equal (hons-copy (fargn x 1))
                            (hons-copy (fargn x 2)))
                *t*)
               (t (list 'hide x))))
        (t x)))

(defevaluator evl evl-list
  ((equal x y) (hons-equal x y) (hons-equal! x y) (hide x)))

(defthm hons-equal!-elim-correct
  (equal (evl x a)
         (evl (hons-equal!-elim x) a))
  :hints (("Goal"
           :in-theory (enable hons-equal!)
           :expand ((:free (x) (hide x)))))
  :rule-classes ((:meta :trigger-fns (hons-equal!))))

(in-theory (disable hons-equal! (:e hons-equal!)))

