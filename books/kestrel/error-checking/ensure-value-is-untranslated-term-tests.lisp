; Error Checking Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "ensure-value-is-untranslated-term")

(include-book "std/testing/must-eval-to-t" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-value-is-untranslated-term 'v
                                                 "This"
                                                 t
                                                 nil
                                                 'test
                                                 state)))
   (value (and (equal (nth 0 x) 'v)
               (equal (nth 1 x) '(nil))))))

(must-eval-to-t
 (b* (((er x) (ensure-value-is-untranslated-term 5/4
                                                 "This"
                                                 t
                                                 nil
                                                 'test
                                                 state)))
   (value (and (equal (nth 0 x) ''5/4)
               (equal (nth 1 x) '(nil))))))

(must-eval-to-t
 (b* (((er x) (ensure-value-is-untranslated-term '(* x 4)
                                                 "This"
                                                 t
                                                 nil
                                                 'test
                                                 state)))
   (value (and (equal (nth 0 x) '(binary-* x '4))
               (equal (nth 1 x) '(nil))))))

(must-eval-to-t
 (b* (((er x) (ensure-value-is-untranslated-term '(mv state 33)
                                                 "This"
                                                 t
                                                 nil
                                                 'test
                                                 state)))
   (value (and (equal (nth 0 x) '(cons state (cons '33 'nil)))
               (equal (nth 1 x) '(state nil))))))

(must-fail
 (ensure-value-is-untranslated-term '(binary-* x y z)
                                    "This"
                                    t
                                    nil
                                    'test
                                    state)
 :with-output-off nil)
