; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "parser-interface")
(include-book "type-checking")
(include-book "evaluation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-eval-prog (code)
  `(assert-event
    (b* ((code ,code)
         (ast (parse-from-string code))
         (tast (check-program ast))
         (prog (type+prog->prog tast))
         (val (eval-prog prog 1000000)))
      (and (not (cw "~x0~%" val))
           (not (reserrp val))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-eval-prog "3")

(test-eval-prog
 "(let ((val x 4)) x)")

(test-eval-prog
 "(let ((val x 10) (val y 20)) (+ x y))")
