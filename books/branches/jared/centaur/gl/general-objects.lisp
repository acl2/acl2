; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
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




(defn general-numberp (x)
  (declare (xargs :guard t))
  (or (acl2-numberp x)
      (and (consp x)
           (or (eq (tag x) :g-number)
               (and (eq (tag x) :g-concrete)
                    (acl2-numberp (g-concrete->obj x)))))))

(in-theory (disable (general-numberp)))

(defthm general-numberp-of-atomic-constants
  (implies (and (syntaxp (quotep x))
                (atom x))
           (equal (general-numberp x)
                  (acl2-numberp x))))


(defun number-to-components (n)
  (declare (xargs :guard (acl2-numberp n)))
  (let* ((real (realpart n))
         (rnum (numerator real))
         (rden (denominator real))
         (imag (imagpart n))
         (inum (numerator imag))
         (iden (denominator imag)))
    (mv (i2v rnum) (n2v rden) (i2v inum) (n2v iden))))


(defn general-number-components (x)
  (declare (xargs :guard (general-numberp x)
                  :guard-hints (("goal" :in-theory (enable general-numberp)))))
  (if (atom x)
      (number-to-components x)
    (if (eq (tag x) :g-concrete)
        (number-to-components (g-concrete->obj x))
      (break-g-number (g-number->num x)))))




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



