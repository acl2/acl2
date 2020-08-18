; Error Checking Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "ensure-symbol-is-fresh-event-name")

(include-book "std/testing/must-eval-to-t" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er updated-event-names-to-avoid)
       (ensure-symbol-is-fresh-event-name 'newnewnew
                                          "This"
                                          'function
                                          nil ; other-event-names-to-avoid
                                          t
                                          nil
                                          'test
                                          state)))
   (value (equal updated-event-names-to-avoid '(newnewnew)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er updated-event-names-to-avoid)
       (ensure-symbol-is-fresh-event-name 'newnewnew
                                          "This"
                                          'function
                                          '(new newnew)
                                          t
                                          nil
                                          'test
                                          state)))
   (value (equal updated-event-names-to-avoid '(newnewnew new newnew)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
 (ensure-symbol-is-fresh-event-name 'newnewnew
                                    "This"
                                    'function
                                    '(newnewnew more)
                                    t
                                    nil
                                    'test
                                    state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
 (ensure-symbol-is-fresh-event-name ':kw
                                    "This"
                                    'macro
                                    nil ; other-event-names-to-avoid
                                    t
                                    nil
                                    'test
                                    state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
 (ensure-symbol-is-fresh-event-name 'len
                                    "This"
                                    'const
                                    nil ; other-event-names-to-avoid
                                    t
                                    nil
                                    'test
                                    state)
 :with-output-off nil)
