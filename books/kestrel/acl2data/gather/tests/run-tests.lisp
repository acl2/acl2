; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; For dependency generation:
#|

(include-book "../patch-book")
(include-book "../patch-book-advice")

(include-book "../patch-diff")

; chk-all-test-files.lsp (via run-tests.sh):
(include-book "acl2data-files-agree")

; test2a.lisp:
; test2b.lisp:
(include-book "tools/rulesets" :dir :system)

; test3.lisp:
; test3a.lisp:
(include-book "arithmetic-5/lib/floor-mod/floor-mod-basic" :dir :system)
(include-book "arithmetic-5/lib/basic-ops/arithmetic-theory" :dir :system)

; test5.lisp:
(include-book "arithmetic/top-with-meta" :dir :system)
(include-book "arithmetic/binomial" :dir :system)
(include-book "clause-processors/autohide" :dir :system)

; test6.lisp:
(include-book "arithmetic-5/top" :dir :system)

; test9.lisp:
(include-book "std/util/define" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
(include-book "std/util/def-bound-theorems" :dir :system)
|#

(defttag t)

(make-event
 (prog2$ (sys-call (concatenate 'string (cbd) "run-tests.sh") nil)
         (mv-let (status state)
           (sys-call-status state)
           (value `(defconst *run-tests-status* ,status)))))

(make-event
 (if (equal *run-tests-status* 0)
     '(value-triple :success)
   (er hard 'run-tests
       "Failed!  See file~|chk-all-test-files.lsp.out~|in directory~|~s0"
       (cbd))))

            
