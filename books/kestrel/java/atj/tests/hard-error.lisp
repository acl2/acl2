; Java Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../atj" :ttags ((:open-output-channel!) (:oslib) (:quicklisp) :quicklisp.osicat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A function that may throw a hard error.

(defun error-if-nil (x)
  (declare (xargs :guard t))
  (if x :okay (hard-error 'some-context "some message" nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We do not use ATJ's test generation facility
; because that facility does not handle the throwing of exceptions,
; and hard errors are implemented by throwing exceptions.

(java::atj error-if-nil
           :deep t
           :guards nil
           :java-class "HardErrorDeepUnguarded")

(java::atj error-if-nil
           :deep t
           :guards t
           :java-class "HardErrorDeepGuarded")

(java::atj error-if-nil
           :deep nil
           :guards nil
           :java-class "HardErrorShallowUnguarded")

(java::atj error-if-nil
           :deep nil
           :guards t
           :java-class "HardErrorShallowGuarded")
