; System Utilities -- Paired Names -- Tests
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "paired-names")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (get-paired-name-separator (w state))
              *default-paired-name-separator*)

(must-succeed*
 (set-paired-name-separator "<->")
 (assert-equal (get-paired-name-separator (w state)) "<->"))

(must-succeed*
 (set-paired-name-separator "-IS-")
 (assert-equal (get-paired-name-separator (w state)) "-IS-"))

(must-fail (set-paired-name-separator ""))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (make-paired-name 'one 'two 1 (w state))
              'one-~>-two)

(assert-equal (make-paired-name 'one 'two 2 (w state))
              'one-~>-two)

(assert-equal (make-paired-name 'acl2::abc 'std::xyz 1 (w state))
              'acl2::abc-~>-xyz)

(assert-equal (make-paired-name 'acl2::abc 'std::xyz 2 (w state))
              'std::abc-~>-xyz)

(assert-equal (make-paired-name 'std::abc 'acl2::xyz 1 (w state))
              'std::abc-~>-xyz)

(assert-equal (make-paired-name 'std::abc 'acl2::xyz 2 (w state))
              'acl2::abc-~>-xyz)

(must-succeed*
 (set-paired-name-separator "-SEPARATOR-")
 (assert-equal (make-paired-name 'one 'two 1 (w state))
               'one-separator-two))

(must-succeed*
 (set-paired-name-separator "-SEPARATOR-")
 (assert-equal (make-paired-name 'one 'two 2 (w state))
               'one-separator-two))

(must-succeed*
 (set-paired-name-separator "<<--->>")
 (assert-equal (make-paired-name 'std::one 'acl2::two 1 (w state))
               'std::one<<--->>two))

(must-succeed*
 (set-paired-name-separator "<<--->>")
 (assert-equal (make-paired-name 'std::one 'acl2::two 2 (w state))
               'acl2::one<<--->>two))

(assert-equal (make-paired-name :a :b 1 (w state))
              :a-~>-b)

(assert-equal (make-paired-name :a :b 2 (w state))
              :a-~>-b)
