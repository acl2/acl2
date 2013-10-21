; CUTIL - Centaur Basic Utilities
; Copyright (C) 2008-2011 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>
;
; Additional copyright notice:
;
; This file is adapted from Milawa, which is also released under the GPL.

(in-package "STD")
(include-book "deflist")
(include-book "str/top" :dir :system)
(include-book "misc/assert" :dir :system)

(make-event
 (prog2$
  (cw "~%~%~%WARNING!  PRINTER ON FIRE!~%You are loading ~
       std/util/deflist-tests! Don't do that!~%~%")
  '(value-triple :invisible))
 :check-expansion t)



(in-theory
 ;; This is awful and you should generally never do it.  But here, the idea is
 ;; to show that all of these deflists will succeed even in a crippled theory.
 nil)

(encapsulate
  (((foop *) => *))
  (local (defun foop (x) (consp x)))
  (defthm booleanp-of-foop
    (or (equal (foop x) t)
        (equal (foop x) nil))
    :rule-classes :type-prescription))

(encapsulate
  (((barp *) => *))
  (local (defun barp (x) (atom x)))
  (local (in-theory (enable booleanp booleanp-compound-recognizer)))
  (defthm booleanp-of-barp
    (or (equal (barp x) t)
        (equal (barp x) nil))
    :rule-classes :type-prescription)
  (defthm barp-of-nil
    (barp nil)))

(encapsulate
  (((bazp *) => *))
  (local (defun bazp (x) (consp x)))
  (defthm booleanp-of-bazp
    (or (equal (bazp x) t)
        (equal (bazp x) nil))
    :rule-classes :type-prescription)
  (defthm bazp-of-nil
    (not (bazp nil))))


;; Basic tests to make sure the macro has all its theorems set up with the
;; right polarity for the different cases of elementp-of-nil and negatedp...

(deflist foolist1p (x)
  (foop x))

(deflist foolist2p (x)
  (foop x)
  :true-listp t)

(deflist nfoolist1p (x)
  (foop x)
  :negatedp t)

(deflist nfoolist2p (x)
  (foop x)
  :negatedp t
  :true-listp t)


(deflist barlist1p (x)
   (barp x)
   :elementp-of-nil t)

(deflist barlist2p (x)
   (barp x)
   :elementp-of-nil t
   :true-listp t)

(deflist nbarlist1p (x)
  (barp x)
  :elementp-of-nil t
  :negatedp t)

(deflist nbarlist2p (x)
  (barp x)
  :elementp-of-nil t
  :negatedp t
  :true-listp t)


(deflist bazlist1p (x)
   (bazp x)
   :elementp-of-nil nil)

(deflist bazlist2p (x)
   (bazp x)
   :elementp-of-nil nil
   :true-listp t)

(deflist nbazlist1p (x)
   (bazp x)
   :elementp-of-nil nil
   :negatedp t)

(deflist nbazlist2p (x)
   (bazp x)
   :elementp-of-nil nil
   :negatedp t
   :true-listp t)


;; Make sure everything still works for basic types instead of just constrained
;; functions, since ACL2 knows too much about these in some cases...

(deflist intlist1p (x)
   (integerp x))

(deflist intlist2p (x)
   (integerp x)
   :elementp-of-nil nil)


(deflist symlist1p (x)
   (symbolp x))

(deflist symlist2p (x)
   (symbolp x)
   :elementp-of-nil t)


;; Because of type-prescription reasoning, normalization, etc., there can be
;; problems with trivial recognizers that are always true or always false.

(encapsulate
  (((alwaystrue *) => *))
  (local (defun alwaystrue (x) (equal x x)))
  (defthm type-of-alwaystrue
    (equal (alwaystrue x) t)
    :rule-classes :type-prescription))

(encapsulate
  (((alwaysfalse *) => *))
  (local (defun alwaysfalse (x) (not (equal x x))))
  (defthm type-of-alwaysfalse
    (equal (alwaysfalse x) nil)
    :rule-classes :type-prescription))

(deflist alt-truelistp (x)
  (alwaystrue x)
  :guard t)




;; Other packages, program mode, documentation stuff

#!ACL2
(std::deflist int-listp (x)
  (integerp x))

(deflist testlist1 (x)
  (integerp x)
  :mode :program)

(deflist testlist2 (x)
  (integerp x)
  :short "Foo")

(deflist testlist3 (x)
  (integerp x)
  :long "Foo")

(deflist testlist4 (x)
  (integerp x)
  :parents (whatever))


;; Guards

(local (in-theory (enable (:type-prescription evenp))))

(deflist evenlist1p (x)
  (evenp x)
  :guard (integer-listp x)
  :guard-hints(("Goal" :in-theory (enable integer-listp))))

(deflist evenlist2p (x)
  (evenp x)
  :guard (atom-listp x)
  :verify-guards nil)



;; Additional arguments

(deflist biglist1p (min x)
  (> min x)
  :guard (and (integerp min)
              (integer-listp x))
  :guard-hints(("Goal" :in-theory (enable integer-listp))))

(defun blah-p (min x)
  (declare (xargs :guard (integerp min)))
  (or (not x)
      (and (integerp x)
           (> min x))))

(deflist blahlist1p (min x)
  (blah-p min x)
  :guard (integerp min)
  :elementp-of-nil t)

(deflist nblahlist1p (min x)
  (blah-p min x)
  :guard (integerp min)
  :negatedp t
  :elementp-of-nil t)

(deflist blahlist2p (min x)
  (blah-p min x)
  :guard (integerp min)
  :true-listp t)


;; rest stuff

(local (in-theory (enable rational-listp)))

(deflist ratlist (x)
  (rationalp x)
  :true-listp t
  :guard t
  :parents (rationalp)
  :rest
  ((defthm ratlist-is-rational-listp
     (equal (ratlist x)
            (rational-listp x)))))

(assert!
 ;; make sure it got included in the docs...
 (b* ((topic (xdoc::find-topic 'ratlist (xdoc::get-xdoc-table (w state)))))
   (str::isubstrp "@(def |STD|::|RATLIST-IS-RATIONAL-LISTP|)"
                  (cdr (assoc :long topic)))))




;; Hard cases for elementp stuff 

(local (in-theory (theory 'minimal-theory)))

(local (defun anyp (x)
         (declare (ignore x)
                  (xargs :guard t))
         t))

(local (defun nonep (x)
         (declare (ignore x)
                  (xargs :guard t))
         nil))

(local (encapsulate ()
         (local (deflist any-listp (x)
                  (anyp x)))))

(local (encapsulate ()
         (local (deflist none-listp (x)
                  (nonep x)))))

(local (encapsulate ()
         (local (deflist not-listp (x)
                  (not x)))))

(local (encapsulate ()
         (local (deflist null-listp (x)
                  (null x)))))


(local (encapsulate ()
         (local (deflist any-listp2 (x)
                  (anyp x)
                  :elementp-of-nil t))))

(local (encapsulate ()
         (local (deflist none-listp (x)
                  (nonep x)
                  :elementp-of-nil nil))))

(local (encapsulate ()
         (local (deflist not-listp (x)
                  (not x)
                  :elementp-of-nil t))))

(local (encapsulate ()
         (local (deflist null-listp (x)
                  (null x)
                  :elementp-of-nil t))))




(deflist atom-listp (acl2::x)
  ;; This is an especially hard case because ACL2 knows so much about
  ;; ATOM and CONSP.
  (atom acl2::x)
  :true-listp t
  :elementp-of-nil t
  :already-definedp t)

(deflist alistp (acl2::x)
  ;; This is an especially hard case because ACL2 knows so much about
  ;; ATOM and CONSP.
  (consp acl2::x)
  :true-listp t
  :elementp-of-nil nil
  :already-definedp t)






(deflist m0 (x)
  (consp x))

(assert! (let ((topic (xdoc::find-topic 'm0 (xdoc::get-xdoc-table (w state)))))
           (and topic
                (equal (cdr (assoc :parents topic))
                       '(acl2::undocumented)))))

(xdoc::set-default-parents foo bar)

(deflist m1 (x)
  (consp x))

(assert! (let ((topic (xdoc::find-topic 'm1 (xdoc::get-xdoc-table (w state)))))
           (and topic
                (equal (cdr (assoc :parents topic))
                       '(foo bar)))))

(deflist m2 (x)
  (consp x)
  :parents (bar))

(assert! (let ((topic (xdoc::find-topic 'm2 (xdoc::get-xdoc-table (w state)))))
           (and topic
                (equal (cdr (assoc :parents topic))
                       '(bar)))))

(deflist m3 (x)
  (consp x)
  :parents nil)

(assert! (let ((topic (xdoc::find-topic 'm3 (xdoc::get-xdoc-table (w state)))))
           (not topic)))




