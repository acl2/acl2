; Common material for Formal Unit Testers
;
; Copyright (C) 2021-2022 Kestrel Technology, LLC
; Copyright (C) 2023-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/rational-printing" :dir :system)

;; TODO: Print OK if expected, otherwise ERROR
(defund print-test-summary-aux (result-alist)
  (declare (xargs :guard (alistp result-alist)))
  (if (endp result-alist)
      nil
    (prog2$
     (let* ((entry (first result-alist))
            (name (car entry)) ; a string
            (val (cdr entry)))
       (if (not (and (stringp name)
                     (= 3 (len val))))
           (er hard? 'print-test-summary-aux "Bad entry in result-alist: ~x0." entry)
         (let* ((result (first val)) ; either :pass or :fail
                (expected-result (second val)) ; :pass or :fail or :any
                (elapsed (third val))
                (elapsed (if (and (rationalp elapsed)
                                  (<= 0 elapsed))
                             elapsed
                           (prog2$ (er hard? 'print-test-summary-aux "Bad elapsed time: ~x0." elapsed)
                                   0)))
                (result-string (if (eq :pass result) "pass" "fail"))
                (numspaces (nfix (- 40 (len (coerce name 'list)))))
                )
           (if (equal result expected-result)
               (progn$ (cw "Test ~s0:~_1 OK (~s2)   " name numspaces result-string)
                       (print-to-hundredths elapsed)
                       (cw "s.~%"))
             (if (eq :any expected-result)
                 ;; In this case, we don't know whether the test is supposed to pass:
                 (progn$ (cw "Test ~s0:~_1 ?? (~s2)   " name numspaces result-string)
                         (print-to-hundredths elapsed)
                         (cw "s.~%"))
               (progn$ (cw "Test ~s0:~_1 ERROR (~s2, but we expected ~s3).  " name numspaces result-string (if (eq :pass expected-result) "pass" "fail"))
                       (print-to-hundredths elapsed)
                       (cw "s~%")))))))
     (print-test-summary-aux (rest result-alist)))))

(defund print-test-summary (result-alist executable-path)
  (declare (xargs :guard (and (alistp result-alist)
                              (stringp executable-path))))
  (progn$ (cw"~%========================================~%")
          (cw "SUMMARY OF RESULTS for ~x0:~%" executable-path)
          (print-test-summary-aux result-alist)
          (cw"========================================~%")))

(defun any-result-unexpectedp (result-alist)
  (declare (xargs :guard (alistp result-alist)))
  (if (endp result-alist)
      nil
    (let* ((entry (first result-alist))
           ;; (name (car entry)) ; a string
           (val (cdr entry)))
      (if (not (and ;; (stringp name)
                (= 3 (len val))))
          (er hard? 'any-result-unexpectedp "Bad entry in result-alist: ~x0." entry)
        (let* ((result (first val))           ; either :pass or :fail
               (expected-result (second val))  ; :pass or :fail or :any
               (expectedp (or (eq :any expected-result)
                              (equal result expected-result))))
          (or (not expectedp)
              (any-result-unexpectedp (rest result-alist))))))))
