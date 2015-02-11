; ESIM Symbolic Hardware Simulator
; Copyright (C) 2008-2015 Centaur Technology
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
; Original authors: Bob Boyer and Warren Hunt
; Current maintainer of this file: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

;; BOZO find these acl2-count theorems a home.

(defthm acl2-count-car-linear-strong
  (implies (consp x)
           (< (acl2-count (car x)) (acl2-count x)))
  :rule-classes :linear)

(defthm acl2-count-car-linear-weak
  (<= (acl2-count (car x)) (acl2-count x))
  :rule-classes :linear)

(defthm acl2-count-cdr-linear-strong
  (implies (consp x)
           (< (acl2-count (cdr x)) (acl2-count x)))
  :rule-classes :linear)

(defthm acl2-count-cdr-linear-weak
  (<= (acl2-count (cdr x)) (acl2-count x))
  :rule-classes :linear)

(defthm atom-when-acl2-count-zero
  (implies (equal (acl2-count x) 0)
           (atom x))
  :rule-classes :forward-chaining)

(in-theory (disable acl2-count))


(defn gpl (key pl)
  (declare (xargs :guard (symbolp key)))
  "Suppose KEY is a keyword and PL is a plist.  (GPL key pl) means
  'the value for KEY in PL'.  GPL is short for 'get from property
  list.'

  See also PLISTP and GPL-TAIL."


  (cond ((or (atom pl)
             (atom (cdr pl))) ; permits the following EQ
         nil)
        ((eq key (car pl)) (cadr pl))
        (t (gpl key (cddr pl)))))

(local
 (defthm gpl-implies-consp
   (implies (gpl k1 x) (consp x))))

(defthm acl2-count-gpl-linear-strong
  (implies (consp x)
           (< (acl2-count (gpl key x)) (acl2-count x)))
  :rule-classes :linear)

(defthm acl2-count-gpl-linear-strong1
  (implies (gpl k1 x)
           (< (acl2-count (gpl key x)) (acl2-count x)))
  :rule-classes :linear)

(defthm acl2-count-gpl-linear-weak
  (<= (acl2-count (gpl key x)) (acl2-count x))
  :rule-classes :linear)

(defun rempl (key pl)
  (declare (xargs :guard (symbolp key)))
  (cond ((or (atom pl) (atom (cdr pl))) pl)
        ((eq key (car pl)) (rempl key (cddr pl)))
        (t (list* (car pl) (cadr pl) (rempl key (cddr pl))))))

(defthm gpl-of-rempl
  (equal (gpl j (rempl k pl))
         (and (not (equal j k))
              (gpl j pl)))
  :hints(("Goal" :in-theory (enable gpl))))


(defun chgpl (key val pl)
  (declare (xargs :guard (symbolp key)))
  (list* key val (rempl key pl)))

(defthm gpl-of-chgpl
  (equal (gpl j (chgpl k v pl))
         (if (equal j k)
             v
           (gpl j pl))))




(defun rempl* (keys pl)
  (declare (Xargs :guard (symbol-listp keys)))
  (cond ((or (atom pl) (atom (cdr pl)))
         pl)
        ((member-eq (car pl) keys)
         (rempl* keys (cddr pl)))
        (t
         (list* (car pl)
                (cadr pl)
                (rempl* keys (cddr pl))))))

(defthm gpl-of-rempl*
  (equal (gpl k (rempl* ks pl))
         (and (not (member-equal k ks))
              (gpl k pl))))

(defun pl-keys (pl)
  (declare (xargs :guard t))
  (if (or (atom pl)
          (atom (cdr pl)))
      nil
    (cons (car pl)
          (pl-keys (cddr pl)))))

(defun append-pl (pl1 pl2)
  (declare (xargs :guard t))
  (cond ((or (atom pl1)
             (atom (cdr pl1)))
         pl2)
        (t
         (list* (car pl1)
                (cadr pl1)
                (append-pl (cddr pl1) pl2)))))

(defthm gpl-of-append-pl
  (equal (gpl k (append-pl pl1 pl2))
         (if (member-equal k (pl-keys pl1))
             (gpl k pl1)
           (gpl k pl2))))


(defun chgpl* (new pl)
  (declare (xargs :guard (and (symbol-listp (pl-keys new))
                              (true-listp new))))
  (append-pl new (rempl* (pl-keys new) pl)))

(defthm gpl-of-chgpl*
  (equal (gpl k (chgpl* new pl))
         (if (member-equal k (pl-keys new))
             (gpl k new)
           (gpl k pl))))

(in-theory (disable gpl chgpl rempl chgpl* rempl*))
