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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "STD")
(include-book "../defines")
(include-book "../deflist")
(include-book "utils")
(include-book "std/testing/assert" :dir :system)

(defun foo (x)
  (declare (xargs :guard (natp x) :mode :logic))
  x)

(defun bar (x)
  (declare (xargs :guard (natp x)))
  x)


(defines basic
  :parents (hi)
  :short "some dumb thing"
  (define my-evenp ((x natp))
    :short "it's just evenp"
    (if (zp x)
        t
      (my-oddp (- x 1))))
  (define my-oddp (x)
    :guard (natp x)
    (if (zp x)
        nil
      (my-evenp (- x 1)))))

(assert-disabled my-evenp)
(assert-disabled my-oddp)
(assert-logic-mode my-evenp)
(assert-logic-mode my-oddp)

(defines basic2
  :parents (hi)
  :short "some dumb thing"
  (define bool-evenp ((x natp))
    :parents (append)
    :short "Woohoo!"
    :returns (evenp booleanp)
    (if (zp x)
        t
      (bool-oddp (- x 1))))
  (define bool-oddp (x)
    :guard (natp x)
    (if (zp x)
        nil
      (bool-evenp (- x 1)))))

(local (xdoc::set-default-parents foo))

(defines basic3
  :verbosep t
;  :parents (hi)
  :short "some dumb thing"
  (define basic3 ((x natp))
    :long "<p>goofy merged docs</p>"
    :returns (evenp booleanp)
    (if (zp x)
        t
      (basic3-oddp (- x 1))))
  (define basic3-oddp (x)
    :guard (natp x)
    (if (zp x)
        nil
      (basic3 (- x 1)))))

(defines spurious3
  (define my-oddp3 (x)
    :guard (natp x)
    (if (zp x)
        nil
      (my-evenp3 (- x 1))))
  (define my-evenp3 (x)
    :guard (natp x)
    (if (zp x)
        t
      (if (eql x 1)
          nil
        (my-evenp3 (- x 2))))))

(defines bogus-test
  :bogus-ok t
  (define my-oddp4 (x)
    :guard (natp x)
    (if (zp x)
        nil
      (evenp (- x 1))))
  (define my-evenp4 (x)
    :guard (natp x)
    (if (zp x)
        t
      (if (eql x 1)
          nil
        (my-evenp4 (- x 2))))))

(defines xarg-test
  :verify-guards nil
  :bogus-ok t
  (define my-oddp5 (x)
    :guard (consp x) ;; not valid
    (if (zp x)
        nil
      (evenp (- x 1))))
  (define my-evenp5 (x)
    :guard (natp x)
    (if (zp x)
        t
      (if (eql x 1)
          nil
        (my-evenp5 (- x 2))))))

(defines my-termp

  (define my-termp (x)
    (if (atom x)
        (natp x)
      (and (symbolp (car x))
           (my-term-listp (cdr x))))
    ///
    (defthm natp-when-my-termp
      (implies (atom x)
               (equal (my-termp x)
                      (natp x))))

    (defthm my-termp-of-cons
      (equal (my-termp (cons fn args))
             (and (symbolp fn)
                  (my-term-listp args)))))

  (define my-term-listp (x)
    (if (atom x)
        t
      (and (my-termp (car x))
           (my-term-listp (cdr x))))
    ///
    (deflist my-term-listp (x)
      (my-termp x)
      :already-definedp t)))

(defines my-flatten-term
  :returns-no-induct t
  (define my-flatten-term ((x my-termp))
    :flag term
    :returns (numbers true-listp :rule-classes :type-prescription)
    (if (atom x)
        (list x)
      (my-flatten-term-list (cdr x))))

  (define my-flatten-term-list ((x my-term-listp))
    :flag list
    :returns (numbers true-listp :rule-classes :type-prescription)
    (if (atom x)
        nil
      (append (my-flatten-term (car x))
              (my-flatten-term-list (cdr x)))))
  ///
  (defthm-my-flatten-term-flag
    (defthm nat-listp-of-my-flatten-term
      (implies (my-termp x)
               (nat-listp (my-flatten-term x)))
      :flag term)
    (defthm nat-listp-of-my-flatten-term-list
      (implies (my-term-listp x)
               (nat-listp (my-flatten-term-list x)))
      :flag list)))

(defines my-flatten-term2
  :returns-hints (("goal" :in-theory (disable nat-listp)))
  (define my-flatten-term2 ((x my-termp))
    :flag term
    :returns (numbers nat-listp :hyp :guard
                      :hints ((and stable-under-simplificationp
                                   '(:in-theory (enable nat-listp)))))
    (if (atom x)
        (list x)
      (my-flatten-term2-list (cdr x))))

  (define my-flatten-term2-list ((x my-term-listp))
    :flag list
    :returns (numbers nat-listp :hyp :guard
                      :hints ((and stable-under-simplificationp
                                   '(:in-theory (enable nat-listp)))))
    (if (atom x)
        nil
      (append (my-flatten-term2 (car x))
              (my-flatten-term2-list (cdr x))))))


(defines doc-test
  :short "Test of local stuff."
  :returns-hints (("goal" :in-theory (disable nat-listp)))
  (define doc-test ((x my-termp))
    :flag term
    :returns (numbers nat-listp :hyp :guard
                      :hints ((and stable-under-simplificationp
                                   '(:in-theory (enable nat-listp)))))
    (if (atom x)
        (list x)
      (doc-test-list (cdr x)))
    ///
    (local (defthm local1 (integerp (len x))))
    (defthm global1 (integerp (len x))))

  (define doc-test-list ((x my-term-listp))
    :flag list
    :returns (numbers nat-listp :hyp :guard
                      :hints ((and stable-under-simplificationp
                                   '(:in-theory (enable nat-listp)))))
    (if (atom x)
        nil
      (append (doc-test (car x))
              (doc-test-list (cdr x)))))

  ///
  (local (defthm local2 (integerp (len x))))
  (defthm global2 (integerp (len x))))

(include-book "std/strings/substrp" :dir :system)
(include-book "std/testing/assert" :dir :system)

(assert!
 (let ((long (cdr (assoc :long (xdoc::find-topic 'doc-test (xdoc::get-xdoc-table (w state)))))))
   (and (or (str::substrp "GLOBAL1" long)
            (er hard? 'doc-test "Missing global1"))
        (or (str::substrp "GLOBAL2" long)
            (er hard? 'doc-test "Missing global2"))
        (or (not (str::substrp "LOCAL1" long))
            (er hard? 'doc-test "Accidentally have local1"))
        (or (not (str::substrp "LOCAL2" long))
            (er hard? 'doc-test "Accidentally have local2")))))



;; BOZO this isn't really working yet

;; (defines doc-test2
;;   :short "Test of local stuff."
;;   :returns-hints (("goal" :in-theory (disable nat-listp)))
;;   (define doc-test2-term ((x my-termp))
;;     :flag term
;;     :returns (numbers nat-listp :hyp :guard
;;                       :hints ((and stable-under-simplificationp
;;                                    '(:in-theory (enable nat-listp)))))
;;     (if (atom x)
;;         (list x)
;;       (doc-test2-list (cdr x)))
;;     ///
;;     (local (defthm local1 (integerp (len x))))
;;     (defthm global1 (integerp (len x))))

;;   (define doc-test2-list ((x my-term-listp))
;;     :flag list
;;     :returns (numbers nat-listp :hyp :guard
;;                       :hints ((and stable-under-simplificationp
;;                                    '(:in-theory (enable nat-listp)))))
;;     (if (atom x)
;;         nil
;;       (append (doc-test2-term (car x))
;;               (doc-test2-list (cdr x)))))

;;   ///
;;   (local (defthm local2 (integerp (len x))))
;;   (defthm global2 (integerp (len x))))


(defines program-mode-test-1
  :mode :program
  (define program-f1 (x) (if (atom x) nil (program-g1 x)))
  (define program-g1 (x) (program-h1 x))
  (define program-h1 (x) (program-f1 x)))

(assert-program-mode program-f1)
(assert-program-mode program-g1)
(assert-program-mode program-h1)


(encapsulate
  ()
  (program)
  (defines program-mode-test-2
    (define program-f2 (x) (if (atom x) nil (program-g2 x)))
    (define program-g2 (x) (program-h2 x))
    (define program-h2 (x) (program-f2 x))))

(assert-program-mode program-f2)
(assert-program-mode program-g2)
(assert-program-mode program-h2)
