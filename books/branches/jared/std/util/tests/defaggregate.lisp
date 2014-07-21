; Standard Utilities Library
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
; Original author: Jared Davis <jared@centtech.com>

; Tests for defaggregate utility.  Consider moving tests from the bottom of
; defaggregate.lisp into this file.

(in-package "STD")

(include-book "../defaggregate")
(include-book "../deflist")
(include-book "misc/assert" :dir :system)

(encapsulate
 ()
 (defun foof-p (x)
   (declare (xargs :guard t))
   (keywordp x))

 (defmacro foom-p (x)
   `(keywordp ,x))

 (defaggregate containerf
   (thing)
   :require ((foof-p-of-containerf->thing
              (foof-p thing)))
   :tag :containerf)

 (defaggregate containerm
   (thing)
   :require ((foom-p-of-containerm->thing
              (foom-p thing)))
   :tag :containerm))

(mutual-recursion
 (DEFUND FOO-P (X)
   (DECLARE (XARGS :GUARD T))
   (AND (CONSP X)
        (EQ (CAR X) :FOO)
        (ALISTP (CDR X))
        (CONSP (CDR X))
        (LET ((BAR (CDR (ASSOC 'BAR (CDR X)))))
             (DECLARE (IGNORABLE BAR))
             (AND (FOO-LIST-P BAR)))))

 (DEFUND FOO-LIST-P (X)
   (DECLARE (XARGS :GUARD T
                   :NORMALIZE NIL
                   :VERIFY-GUARDS T
                   :GUARD-DEBUG NIL
                   :GUARD-HINTS NIL))
   (IF (CONSP X)
       (AND (FOO-P (CAR X))
            (FOO-LIST-P (CDR X)))
       (NULL X))))

(std::defaggregate foo
  (bar)
  :require ((foo-list-p-of-foo->bar
             (foo-list-p bar)))
  :already-definedp t
  :tag :foo)

(std::deflist foo-list-p (x)
  (foo-p x)
  :elementp-of-nil nil
  :already-definedp t
  :true-listp t)

(std::defaggregate pair-o-ints
  ((left integerp "Left part of pair")
   (right integerp "Right part of pair"))
  :tag :pair-o-ints)

(defund sum-a-pair (x)
  (declare (xargs :guard (pair-o-ints-p x)))
  (b* (((pair-o-ints x) x)
       (- (cw "left is ~x0~%" x.left))
       (- (cw "right is ~x0~%" x.right)))
    (+ x.left x.right)))

(assert! (equal (sum-a-pair (make-pair-o-ints :left 4 :right 5)) 9))

#||

(logic)

(defaggregate taco
    (shell meat cheese lettuce sauce)
    :legiblep :ordered
    :tag :taco
    :require ((integerp-of-taco->shell (integerp shell)
                                       :rule-classes ((:rewrite) (:type-prescription))))
    :long "<p>Additional documentation</p>"
    )

(defaggregate htaco
    (shell meat cheese lettuce sauce)
    :tag :taco
    :hons t
    :require ((integerp-of-htaco->shell (integerp shell)))
    :long "<p>Additional documentation</p>"
    )

(defaggregate untagged-taco
    (shell meat cheese lettuce sauce)
    :tag nil
    :hons t
    :require ((integerp-of-untagged-taco->shell (integerp shell)))
    :long "<p>Additional documentation</p>"
    )


;;  Basic binding tests

(b* ((?my-taco (make-taco :shell 5
                          :meat 'beef
                          :cheese 'swiss
                          :lettuce 'iceberg
                          :sauce 'green))
     ((taco x) my-taco)
     (five (+ 2 3)))
    (list :shell x.shell
          :lettuce x.lettuce
          :five five
          :my-taco my-taco))


;; I'd like something like this, but it looks like the b* machinery wants
;; at least one form.
;;
;; (b* ((?my-taco (make-taco :shell 5
;;                           :meat 'beef
;;                           :cheese 'swiss
;;                           :lettuce 'iceberg
;;                           :sauce 'green))
;;      ((taco my-taco))
;;      (five (+ 2 3)))
;;     (list :my-taco.shell my-taco.shell
;;           :my-taco.lettuce my-taco.lettuce
;;           :five five
;;           :my-taco my-taco))

(b* (((taco x)
      (make-taco :shell 5
                 :meat 'beef
                 :cheese 'swiss
                 :lettuce 'iceberg
                 :sauce 'green))
     (five (+ 2 3)))
    (list :x.shell x.shell
          :x.lettuce x.lettuce
          :five five))

;; Improper binding... fails nicely
(b* (((taco x y)
      (make-taco :shell 5
                 :meat 'beef
                 :cheese 'swiss
                 :lettuce 'iceberg
                 :sauce 'green))
     (five (+ 2 3)))
    (list :x.shell x.shell
          :x.lettuce x.lettuce
          :five five))

;; Unused binding collapses to nothing.  warning noted.
(b* (((taco x) (make-taco :shell 5
                          :meat 'beef
                          :cheese 'swiss
                          :lettuce 'iceberg
                          :sauce 'green))
     (five (+ 2 3)))
    five)

;; Good, inadvertent capture is detected
(b* ((foo (make-taco :shell 5
                     :meat 'beef
                     :cheese 'swiss
                     :lettuce 'iceberg
                     :sauce 'green))
     ((taco x) (identity foo))
     (bad      ACL2::|(IDENTITY FOO)|)
     (five     (+ 2 3)))
    (list :x.shell x.shell
          :x.lettuce x.lettuce
          :five five
          :bad bad))

||#

(defaggregate employee
  :tag :employee
  ((name stringp "some documentation")
   (salary natp :rule-classes :type-prescription :default 25))
  :legiblep nil
  :short "Hello!")

(assert! (b* ((emp (make-employee :name "foo")))
           (and (equal (employee->name emp) "foo")
                (equal (employee->salary emp) 25))))

;; Shouldn't give a bind-warning
(assert! (b* ((emp (make-employee :name "foo"))
              ((employee emp) emp))
           (and (equal emp.name "foo")
                (equal emp.salary 25))))

;; No warning -- same name.
(assert! (b* ((emp (make-employee :name "foo"))
              ((employee emp) emp))
           (and (equal emp.name "foo")
                (equal emp.salary 25)
                emp)))








(defaggregate m0 (a b c))

(assert! (let ((topic (xdoc::find-topic 'm0-p (xdoc::get-xdoc-table (w state)))))
           (and topic
                (equal (cdr (assoc :parents topic))
                       '(acl2::undocumented)))))

(xdoc::set-default-parents foo bar)

(defaggregate m1 (a b c))

(assert! (let ((topic (xdoc::find-topic 'm1-p (xdoc::get-xdoc-table (w state)))))
           (and topic
                (equal (cdr (assoc :parents topic))
                       '(foo bar)))))

(defaggregate m2 (a b c) :parents (bar))

(assert! (let ((topic (xdoc::find-topic 'm2-p (xdoc::get-xdoc-table (w state)))))
           (and topic
                (equal (cdr (assoc :parents topic))
                       '(bar)))))



(defaggregate pancake
  :tag :pancake
  ((syrup  booleanp)
   (butter booleanp))
  :verbosep t)
