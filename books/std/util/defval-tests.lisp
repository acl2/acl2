; CUTIL - Centaur Basic Utilities
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "ACL2")
(include-book "defval")
(include-book "misc/assert" :dir :system)

(defxdoc test-par1 :parents (defval))
(defxdoc test-par2 :parents (defval))

(defval *parent-test1*
  :parents (test-par1)
  :short "test1 short"
  :long "<p>test1 long</p>"
  :showdef t
  :showval t
  (make-list 10))

(defval *parent-test2*
  :showdef nil
  :showval nil
  (make-list 100))

(local (xdoc::set-default-parents (test-par2)))

(defval *parent-test3*
  :showval t
  (make-list 123))

(assert!
 (b* ((topic (xdoc::find-topic '*parent-test1* (xdoc::get-xdoc-table (w state))))
      (parents (cdr (assoc :parents topic))))
   (equal parents '(test-par1))))

(assert!
 (b* ((topic   (xdoc::find-topic '*parent-test2* (xdoc::get-xdoc-table (w state))))
      (parents (cdr (assoc :parents topic))))
   (equal parents '(acl2::undocumented))))

(assert!
 (b* ((topic   (xdoc::find-topic '*parent-test3* (xdoc::get-xdoc-table (w state))))
      (parents (cdr (assoc :parents topic))))
   (equal parents '(test-par2))))

(assert! (equal *parent-test1* (make-list 10)))
(assert! (equal *parent-test2* (make-list 100)))
(assert! (equal *parent-test3* (make-list 123)))



;; There's no actual testing here, but we can manually inspect these to make
;; sure things are getting injected properly

(defval *demo1*
  (make-list 100))

(defval *demo2*
  ;; Should be the same
  :showdef t
  :showval nil
  (make-list 100))

(defval *demo3*
  :showdef t
  :showval t
  (make-list 100))

(defval *demo4*
  :showdef nil
  :showval t
  (make-list 100))

(defval *demo5*
  :showdef nil
  :showval nil
  (make-list 100))

(assert! (equal *demo1* (make-list 100)))
(assert! (equal *demo2* (make-list 100)))
(assert! (equal *demo3* (make-list 100)))
(assert! (equal *demo4* (make-list 100)))
(assert! (equal *demo5* (make-list 100)))

#||
(xdoc '*demo1*) ;; should show defconst
(xdoc '*demo2*) ;; identical to demo1
(xdoc '*demo3*) ;; should show defconst and value
(xdoc '*demo4*) ;; should show value only
(xdoc '*demo5*) ;; should show nothing
||#


;; Test to make sure a keyword works.

(defval *test-kwd* :foo)
(assert! (equal *test-kwd* :foo))

(defval *test-int* 3)
(assert! (equal *test-int* 3))

(defval *test-kwd2*
  :foo
  :parents (parent-test1)
  :short "Blah")

(defval *test-kwd3*
  :parents (parent-test1)
  :foo
  :short "Blah")

(defval *test-kwd4*
  :parents (parent-test1)
  :short "Blah"
  :foo)

(assert! (equal *test-kwd2* :foo))
(assert! (equal *test-kwd3* :foo))
(assert! (equal *test-kwd4* :foo))


;; arguably this sort of thing shouldn't work, but at least we have full
;; backwards compatibility with defconst this way

(defval *test-kwd5* :short)

(assert! (equal *test-kwd5* :short))


;; test some other events

(defval *event-test1*
  17
  ///
  (defthm int-of-event-test1
    (integerp *event-test1*)
    :rule-classes nil))

(defval *event-test2*
  :foo
  ///
  (defthm keywordp-event-test2
    (keywordp *event-test2*)
    :rule-classes nil))

(assert! (equal *test-kwd5* :short))


