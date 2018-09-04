; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "GL")
(include-book "gtypes")


(defun general-booleanp (x)
  (declare (xargs :guard t))
  (or (booleanp x)
      (and (consp x)
           (or (eq (tag x) :g-boolean)
               (and (eq (tag x) :g-concrete)
                    (booleanp (g-concrete->obj x)))))))

(in-theory (disable (general-booleanp)))

(defund general-boolean-value (x)
  (declare (xargs :guard (general-booleanp x)))
  (if (atom x)
      x
    (cdr x)))






(defun general-concrete-atom (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
    (and (eq (tag x) :g-concrete)
         (atom (g-concrete->obj x)))))

(defun general-concrete-atom-val (x)
  (declare (xargs :guard (general-concrete-atom x)))
  (if (atom x) x (g-concrete->obj x)))

(in-theory (disable (general-concrete-atom)
                    (general-concrete-atom-val)))



(defn general-concretep (x)
  (if (gobject-hierarchy-lite x) t nil))


(defun general-concrete-obj (x)
  (declare (xargs :guard (general-concretep x)
                  :verify-guards nil))
  (cond ((atom x) x)
        ((g-concrete-p x) (g-concrete->obj x))
        ((concrete-gobjectp x) x)
        (t (cons (general-concrete-obj (car x))
                 (general-concrete-obj (cdr x))))))


(in-theory (disable (general-concrete-obj)))




(defn general-integerp (x)
  (declare (xargs :guard t))
  (or (integerp x)
      (and (consp x)
           (or (eq (tag x) :g-integer)
               (and (eq (tag x) :g-concrete)
                    (integerp (g-concrete->obj x)))))))

(in-theory (disable (general-integerp)))

(defthm general-integerp-of-atomic-constants
  (implies (and (syntaxp (quotep x))
                (atom x))
           (equal (general-integerp x)
                  (integerp x))))

(defn general-integer-bits (x)
  (declare (xargs :guard (general-integerp x)))
  (if (atom x)
      (i2v x)
    (if (eq (tag x) :g-concrete)
        (i2v (g-concrete->obj x))
      (acl2::list-fix (g-integer->bits x)))))


;; Note that, as in the case of general-number and general-boolean, it could
;; still be the case that x always represents a cons even if x is not a
;; general-consp.
(defun general-consp (x)
  (declare (xargs :guard t))
  (and (consp x)
       (if (eq (tag x) :g-concrete)
           (consp (g-concrete->obj x))
         (not (g-keyword-symbolp (tag x))))))

(in-theory (disable (general-consp)))



(defun general-consp-car (x)
  (declare (xargs :guard (general-consp x)))
  (if (eq (tag x) :g-concrete)
      (mk-g-concrete (car (g-concrete->obj x)))
    (car x)))


(defun general-consp-cdr (x)
  (declare (xargs :guard (general-consp x)))
  (if (eq (tag x) :g-concrete)
      (mk-g-concrete (cdr (g-concrete->obj x)))
    (cdr x)))

(in-theory (disable (general-consp-car)
                    (general-consp-cdr)))


(defun bool-cond-itep (x)
  (declare (xargs :guard t))
  (and (consp x)
       (eq (tag x) :g-ite)
       (general-booleanp (g-ite->test x))))

(defun bool-cond-itep-cond (x)
  (declare (xargs :guard (bool-cond-itep x)))
  (general-boolean-value (g-ite->test x)))


(defun bool-cond-itep-truebr (x)
  (declare (xargs :guard (bool-cond-itep x)))
  (g-ite->then x))



(defun bool-cond-itep-falsebr (x)
  (declare (xargs :guard (bool-cond-itep x)))
  (g-ite->else x))

(local (defthm acl2-count-cdr-weak
         (<= (acl2-count (cdr x))
             (acl2-count x))
         :rule-classes :linear))

(defthm bool-cond-itep-cond-measure
  (implies (bool-cond-itep x)
           (< (acl2-count (bool-cond-itep-cond x))
              (acl2-count x)))
  :hints(("Goal" :in-theory (enable bool-cond-itep
                                    bool-cond-itep-cond
                                    general-boolean-value
                                    general-booleanp)))
  :rule-classes :linear)

(in-theory (disable (bool-cond-itep)
                    (bool-cond-itep-cond)
                    (bool-cond-itep-truebr)
                    (bool-cond-itep-falsebr)))



(defund general-number-fix (x)
  (declare (xargs :guard t))
  (if (atom x)
      (fix x)
    (case (tag x)
      (:g-boolean 0)
      (:g-integer x)
      (:g-concrete (mk-g-concrete (fix (g-concrete->obj x))))
      (t 0))))
