; APT Utilities -- Print Specifiers -- Tests
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "print-specifiers")
(include-book "kestrel/utilities/testing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (canonical-print-specifier-p nil))

(assert! (canonical-print-specifier-p '(:expand)))

(assert! (canonical-print-specifier-p '(:submit)))

(assert! (canonical-print-specifier-p '(:result)))

(assert! (canonical-print-specifier-p '(:submit :expand)))

(assert! (canonical-print-specifier-p '(:result :submit)))

(assert! (canonical-print-specifier-p '(:expand :submit :result)))

(assert! (canonical-print-specifier-p '(:result :expand :submit)))

(assert! (not (canonical-print-specifier-p t)))

(assert! (not (canonical-print-specifier-p :expand)))

(assert! (not (canonical-print-specifier-p :submit)))

(assert! (not (canonical-print-specifier-p :result)))

(assert! (not (canonical-print-specifier-p #\c)))

(assert! (not (canonical-print-specifier-p 55/3)))

(assert! (not (canonical-print-specifier-p '(1 2 3))))

(assert! (not (canonical-print-specifier-p '(expand))))

(assert! (not (canonical-print-specifier-p '(:submit :submit))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (print-specifier-p nil))

(assert! (print-specifier-p '(:expand)))

(assert! (print-specifier-p '(:submit)))

(assert! (print-specifier-p '(:result)))

(assert! (print-specifier-p '(:submit :expand)))

(assert! (print-specifier-p '(:result :submit)))

(assert! (print-specifier-p '(:expand :submit :result)))

(assert! (print-specifier-p '(:result :expand :submit)))

(assert! (print-specifier-p t))

(assert! (print-specifier-p :expand))

(assert! (print-specifier-p :submit))

(assert! (print-specifier-p :result))

(assert! (not (print-specifier-p #\c)))

(assert! (not (print-specifier-p 55/3)))

(assert! (not (print-specifier-p '(1 2 3))))

(assert! (not (print-specifier-p '(expand))))

(assert! (not (print-specifier-p '(:submit :submit))))

(assert! (not (print-specifier-p 'submit)))

(assert! (not (print-specifier-p "result")))

(assert! (not (print-specifier-p "t")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (canonicalize-print-specifier t) '(:expand :submit :result))

(assert-equal (canonicalize-print-specifier :expand) '(:expand))

(assert-equal (canonicalize-print-specifier :submit) '(:submit))

(assert-equal (canonicalize-print-specifier :result) '(:result))

(assert-equal (canonicalize-print-specifier '(:submit :expand))
              '(:submit :expand))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
 (ensure-is-print-specifier 6/7 "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-is-print-specifier "submit" "This" t nil 'test state)
 :with-output-off nil)

(must-eval-to-t
 (b* (((er x) (ensure-is-print-specifier nil "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-is-print-specifier t "This" t nil 'test state)))
   (value (equal x '(:expand :submit :result)))))

(must-eval-to-t
 (b* (((er x) (ensure-is-print-specifier :result "This" t nil 'test state)))
   (value (equal x '(:result)))))

(must-eval-to-t
 (b* (((er x) (ensure-is-print-specifier '(:result :expand)
                                         "This" t nil 'test state)))
   (value (equal x '(:result :expand)))))
