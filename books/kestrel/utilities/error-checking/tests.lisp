; Error Checking -- Tests
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "top")
(include-book "kestrel/utilities/testing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-nil nil "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-nil '(1 2 3) "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-boolean t "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-boolean nil "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-boolean "nil" "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-symbol 'abc "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-symbol t "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-symbol :xyz "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-symbol #\a "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-string "" "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-string "XYZ" "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-string 88 "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-string-or-nil "string" "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-string-or-nil nil "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-string-or-nil "abc" "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-string-or-nil #\c "This" t nil 'test state))

(must-fail
 (ensure-string-or-nil '("a") "This" t nil 'test state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-symbol-list nil "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-symbol-list '(a b c) "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-symbol-list #\Space "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-symbol-list '(a 1 b) "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-symbol-alist nil "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x)
       (ensure-symbol-alist '((a . 2) (b 1 2)) "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-symbol-alist 'a "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-symbol-alist '((a . 2) (#\b 1 2)) "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-symbol-truelist-alist nil "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x)
       (ensure-symbol-truelist-alist
        '((x . nil) (y 5 6)) "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-symbol-truelist-alist 88 "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-symbol-truelist-alist '((x . 8) (y . (1 2))) "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x)
       (ensure-symbol-different 'one 'two "that" "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-symbol-different 'zero 'zero "that" "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-list-no-duplicates nil "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-list-no-duplicates '(1 2 3) "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-list-no-duplicates '(1 2 2) "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-list-subset nil nil "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-list-subset nil '(a b c) "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-list-subset '(b c) '(a b c) "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x)
       (ensure-list-subset '(b c c c) '(a b c) "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-list-subset '(a z) '(a b c) "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-list-subset '(a z z z z) '(a b c) "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-list-subset '(a z y z c) '(a b c) "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-list-subset '(a x y z c) '(a b c) "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-doublet-list nil "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-doublet-list '((a 4)) "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x)
       (ensure-doublet-list
        '((a 4) ((2 4) #\a) ("x" 2)) "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-doublet-list 55 "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-doublet-list '((a . x) (b . y)) "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-doublet-list '((a x) (b . y)) "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-keyword-value-list nil "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x)
       (ensure-keyword-value-list '(:a 1 :b 2) "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-keyword-value-list "zzz" "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-keyword-value-list '((:a 1) (:b 2)) "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-keyword-value-list '((:a . 1) (:b . 2)) "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-member-of-list
               4 '(2 4 88) "in the list" "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-member-of-list
               "a" '(:a "a" (1 2)) "in the list" "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-member-of-list 4 nil "in the list" "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-member-of-list 4 '("tt" t 41) "in the list" "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-not-member-of-list
               4 nil "not in the list" "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-not-member-of-list
               4 '(55 #\c (4)) "not in the list" "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-not-member-of-list 4 '(4) "not in the list" "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-not-member-of-list 4 '(5 4) "not in the list" "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-symbol-not-keyword 'a "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-symbol-not-keyword 'std::a "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-symbol-not-keyword :xx "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-symbol-not-keyword keyword::sym "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-tuple '(36 #\y "aw" '(2 9)) 4 "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-tuple nil 0 "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-tuple '(1 2 3) 8 "This" t nil 'test state))

(must-fail
 (ensure-tuple '(1 2 3) 0 "This" t nil 'test state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-defun-mode :logic "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-defun-mode :program "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-defun-mode 'program "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-defun-mode 3 "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-defun-mode-or-auto :logic "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-defun-mode-or-auto :program "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-defun-mode-or-auto :auto "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-defun-mode-or-auto 'auto "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-defun-mode-or-auto :aauto "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-defun-mode-or-auto 3/4 "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-boolean-or-auto t "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-boolean-or-auto nil "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-boolean-or-auto :auto "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-boolean-or-auto "T" "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-boolean-or-auto '(1 5 0) "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x)
       (ensure-boolean-or-auto-and-return-boolean
        t t "This" t nil 'test state)))
   (value (equal x t))))

(must-eval-to-t
 (b* (((er x)
       (ensure-boolean-or-auto-and-return-boolean
        t nil "This" t nil 'test state)))
   (value (equal x t))))

(must-eval-to-t
 (b* (((er x)
       (ensure-boolean-or-auto-and-return-boolean
        nil t "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x)
       (ensure-boolean-or-auto-and-return-boolean
        nil nil "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x)
       (ensure-boolean-or-auto-and-return-boolean
        :auto t "This" t nil 'test state)))
   (value (equal x t))))

(must-eval-to-t
 (b* (((er x)
       (ensure-boolean-or-auto-and-return-boolean
        :auto nil "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-boolean-or-auto-and-return-boolean 33 t "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-boolean-or-auto-and-return-boolean
  '(#\1 #\c) t "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-variable-name 'x "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-variable-name 'acl2-user::var "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-variable-name t "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-variable-name nil "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-variable-name :x "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-variable-name 67 "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-constant-name '*c* "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-constant-name 'acl2-user::*d* "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-constant-name 'c "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-constant-name #\N "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-symbol-not-stobj 'x "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-symbol-not-stobj 'state "This" t nil 'test state)
 :with-output-off nil)

(must-succeed*
 (defstobj st)
 (must-fail
  (ensure-symbol-not-stobj 'st "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-symbol-function 'cons "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-symbol-function 'len "This" t nil 'test state)))
   (value (equal x nil))))

(must-succeed*
 (defun f (x) x)
 (must-eval-to-t
  (b* (((er x) (ensure-symbol-function 'f "This" t nil 'test state)))
    (value (equal x nil)))))

(must-fail
 (ensure-symbol-function 'fffffff "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-symbol-function 'car-cdr-elim "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-symbol-function :aaa "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x)
       (ensure-symbol-new-event-name 'newnewnew "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-symbol-new-event-name 'cons "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-symbol-new-event-name :kw "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-symbol-new-event-name 'len "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-function-name 'cons "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-function-name 'len "This" t nil 'test state)))
   (value (equal x nil))))

(must-succeed*
 (defun g (x) x)
 (must-eval-to-t
  (b* (((er x) (ensure-function-name 'g "This" t nil 'test state)))
    (value (equal x nil)))))

(must-fail
 (ensure-function-name #\w "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function-name 'lenn "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function-name 'car-cdr-elim "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-function-name-list nil "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-function-name-list '(cons) "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-function-name-list '(cons len) "This" t nil 'test state)))
   (value (equal x nil))))

(must-succeed*
 (defun g (x) x)
 (must-eval-to-t
  (b* (((er x)
        (ensure-function-name-list '(binary-+ g) "This" t nil 'test state)))
    (value (equal x nil)))))

(must-fail
 (ensure-function-name-list 55 "This" t nil 'test state))

(must-fail
 (ensure-function-name-list '(binary-+ car-cdr-elim) "This" t nil 'test state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-list-functions nil "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-list-functions '(cons) "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-list-functions '(cons len) "This" t nil 'test state)))
   (value (equal x nil))))

(must-succeed*
 (defun g (x) x)
 (must-eval-to-t
  (b* (((er x)
        (ensure-list-functions '(binary-+ g) "This" t nil 'test state)))
    (value (equal x nil)))))

(must-fail
 (ensure-list-functions '(1 2 3) "This" t nil 'test state))

(must-fail
 (ensure-list-functions '(binary-+ car-cdr-elim) "This" t nil 'test state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x)
       (ensure-function-name-or-numbered-wildcard
        'cons "This" t nil 'test state)))
   (value (equal x 'cons))))

(must-eval-to-t
 (b* (((er x)
       (ensure-function-name-or-numbered-wildcard
        'len "This" t nil 'test state)))
   (value (equal x 'len))))

(must-succeed*
 (defun g (x) x)
 (must-eval-to-t
  (b* (((er x)
        (ensure-function-name-or-numbered-wildcard
         'g "This" t nil 'test state)))
    (value (equal x 'g)))))

(must-succeed*
 (set-numbered-name-index-start "{")
 (set-numbered-name-index-end "}")
 (set-numbered-name-index-wildcard "*")
 (defun f{4} (x) x)
 (add-numbered-name-in-use f{4})
 (defun f{2} (x) x)
 (add-numbered-name-in-use f{2})
 (must-eval-to-t
  (b* (((er x)
        (ensure-function-name-or-numbered-wildcard
         'f{*} "This" t nil 'test state)))
    (value (equal x 'f{4})))))

(must-fail
 (ensure-function-name-or-numbered-wildcard 33 "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function-name-or-numbered-wildcard
  'car-cdr-elim "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function-name-or-numbered-wildcard
  'h{55} "This" t nil 'test state)
 :with-output-off nil)

(must-succeed*
 (set-numbered-name-index-start "{")
 (set-numbered-name-index-end "}")
 (set-numbered-name-index-wildcard "*")
 (add-numbered-name-in-use f{4})
 (add-numbered-name-in-use f{2})
 (must-fail
  (ensure-function-name-or-numbered-wildcard 'f{*} "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-function/macro/lambda 'cons "This" t nil 'test state))
      (- (cw "~@0~%" (nth 3 x))))
   (value (and (equal (nth 0 x) 'cons)
               (equal (nth 1 x) '(nil nil))
               (equal (nth 2 x) '(nil))))))

(must-eval-to-t
 (b* (((er x) (ensure-function/macro/lambda 'len "This" t nil 'test state))
      (- (cw "~@0~%" (nth 3 x))))
   (value (and (equal (nth 0 x) 'len)
               (equal (nth 1 x) '(nil))
               (equal (nth 2 x) '(nil))))))

(must-succeed*
 (defun f (state n) (declare (xargs :stobjs state)) (mv n state))
 (must-eval-to-t
  (b* (((er x) (ensure-function/macro/lambda 'f "This" t nil 'test state))
       (- (cw "~@0~%" (nth 3 x))))
    (value (and (equal (nth 0 x) 'f)
                (equal (nth 1 x) '(state nil))
                (equal (nth 2 x) '(nil state)))))))

(must-succeed*
 (defmacro m (y) `(list ,y))
 (must-eval-to-t
  (b* (((er x) (ensure-function/macro/lambda 'm "This" t nil 'test state))
       (- (cw "~@0~%" (nth 3 x))))
    (value (and (equal (nth 0 x) '(lambda (y) (cons y 'nil)))
                (equal (nth 1 x) '(nil))
                (equal (nth 2 x) '(nil)))))))

(must-eval-to-t
 (b* (((er x) (ensure-function/macro/lambda
               '(lambda (a b) (+ a b)) "This" t nil 'test state))
      (- (cw "~@0~%" (nth 3 x))))
   (value (and (equal (nth 0 x) '(lambda (a b) (binary-+ a b)))
               (equal (nth 1 x) '(nil nil))
               (equal (nth 2 x) '(nil))))))

(must-eval-to-t
 (b* (((er x) (ensure-function/macro/lambda
               '(lambda (a state b) (mv (+ a b) state))
               "This" t nil 'test state))
      (- (cw "~@0~%" (nth 3 x))))
   (value (and (equal (nth 0 x) '(lambda (a state b)
                                   (cons (binary-+ a b) (cons state 'nil))))
               (equal (nth 1 x) '(nil state nil))
               (equal (nth 2 x) '(nil state))))))

(must-fail
 (ensure-function/macro/lambda 55 "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function/macro/lambda '(1 2 3) "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function/macro/lambda '(lambda 2 3) "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function/macro/lambda '(lambda (q w) (f 3)) "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function/macro/lambda 'sym "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function/macro/lambda 'car-cdr-elim "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-term 'v "This" t nil 'test state)))
   (value (and (equal (nth 0 x) 'v)
               (equal (nth 1 x) '(nil))))))

(must-eval-to-t
 (b* (((er x) (ensure-term 5/4 "This" t nil 'test state)))
   (value (and (equal (nth 0 x) ''5/4)
               (equal (nth 1 x) '(nil))))))

(must-eval-to-t
 (b* (((er x) (ensure-term '(* x 4) "This" t nil 'test state)))
   (value (and (equal (nth 0 x) '(binary-* x '4))
               (equal (nth 1 x) '(nil))))))

(must-eval-to-t
 (b* (((er x) (ensure-term '(mv state 33) "This" t nil 'test state)))
   (value (and (equal (nth 0 x) '(cons state (cons '33 'nil)))
               (equal (nth 1 x) '(state nil))))))

(must-fail
 (ensure-term '(binary-* x y z) "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-function-logic-mode 'cons "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-function-logic-mode 'len "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-function-logic-mode 'untranslate "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-function-program-mode 'fmt "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-function-program-mode 'prove "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-function-program-mode 'len "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-function-defined 'len "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-function-defined 'cons "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-function-non-recursive 'cons "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-function-non-recursive 'atom "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-function-non-recursive 'len "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function-non-recursive 'pseudo-termp "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-function-recursive 'len "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x)
       (ensure-function-recursive 'pseudo-termp "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-function-recursive 'cons "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function-recursive 'atom "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-function-singly-recursive 'len "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-function-singly-recursive 'pseudo-termp "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function-singly-recursive 'consp "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function-singly-recursive 'atom "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-function-known-measure 'len "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x)
       (ensure-function-known-measure 'pseudo-termp "This" t nil 'test state)))
   (value (equal x nil))))

(must-succeed*
 (encapsulate
   ()
   (local
    (defun f (n)
      (declare (xargs :guard (natp n)))
      (if (zp n) nil (f (1- n)))))
   (defun f (n)
     (declare (xargs :guard (natp n) :measure (:? n)))
     (if (zp n) nil (f (1- n)))))
 (must-fail
  (ensure-function-known-measure 'f "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x)
       (ensure-function-not-in-termination-thm 'len "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-function-not-in-termination-thm 'pseudo-termp "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-function-no-stobjs 'cons "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-function-no-stobjs 'len "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-function-no-stobjs 'error1 "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-function-arity 'cons 2 "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-function-arity 'len 1 "This" t nil 'test state)))
   (value (equal x nil))))

(must-succeed*
 (defun c () nil)
 (must-eval-to-t
  (b* (((er x) (ensure-function-arity 'c 0 "This" t nil 'test state)))
    (value (equal x nil)))))

(must-fail
 (ensure-function-arity 'cons 33 "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function-arity 'cons 1 "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function-arity 'cons 0 "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-function-has-args 'cons "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-function-has-args 'len "This" t nil 'test state)))
   (value (equal x nil))))

(must-succeed*
 (defun c () nil)
 (must-fail
  (ensure-function-has-args 'c "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x)
       (ensure-function-number-of-results 'cons 1 "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x)
       (ensure-function-number-of-results 'len 1 "This" t nil 'test state)))
   (value (equal x nil))))

(must-succeed*
 (defun c () nil)
 (must-eval-to-t
  (b* (((er x)
        (ensure-function-number-of-results 'c 1 "This" t nil 'test state)))
    (value (equal x nil)))))

(must-eval-to-t
 (b* (((er x)
       (ensure-function-number-of-results 'error1 3 "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-function-number-of-results 'error1 1 "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function-number-of-results 'error1 7 "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-function-guard-verified 'cons "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-function-guard-verified 'len "This" t nil 'test state)))
   (value (equal x nil))))

(must-succeed*
 (defun h (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (ensure-function-guard-verified 'h "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-term-logic-mode
               '(binary-+ (cons x '3) yy) "This" t nil 'test state)))
   (value (equal x nil))))

(must-succeed*
 (defun f (x) (declare (xargs :mode :program)) x)
 (must-fail
  (ensure-term-logic-mode '(cons (f x) '1) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

(must-succeed*
 (defun f (x) (declare (xargs :mode :program)) x)
 (defun g (x) (declare (xargs :mode :program)) x)
 (must-fail
  (ensure-term-logic-mode '(cons (f x) (g y)) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

(must-succeed*
 (defun f (x) (declare (xargs :mode :program)) x)
 (defun g (x) (declare (xargs :mode :program)) x)
 (defun h (x) (declare (xargs :mode :program)) x)
 (must-fail
  (ensure-term-logic-mode '(cons (f (h x)) (g y)) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-term-free-vars-subset
               '(binary-+ (cons x '3) yy) '(x yy a b)
               "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-term-free-vars-subset
  '(binary-+ (cons x '3) yy) '(x a b) "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-term-free-vars-subset
  '(binary-+ (cons x '3) yy) '(xx a b) "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-term-free-vars-subset
  '(binary-+ (cons (cons x z) '3) yy) '(xx a b) "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-term-ground
               '(binary-+ (cons '1 '3) '4/5) "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-term-ground
               '((lambda (x) (cons x x)) (cons '2 '3))
               "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-term-ground 'x "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-term-ground '(cons x '2) "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-term-ground '(cons x y) "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-term-ground '(cons x (cons y z)) "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-term-no-stobjs '(nil nil nil) "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-term-no-stobjs '(nil state) "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-term-guard-verified-fns
               '(len (cons z '2)) "This" t nil 'test state)))
   (value (equal x nil))))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (ensure-term-guard-verified-fns '(cons (f x) '1) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (ensure-term-guard-verified-fns '(cons (f (g x)) '1) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (defun h (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (ensure-term-guard-verified-fns
   '(cons (f (g x)) (h z)) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-term-guard-verified-exec-fns
               '(len (cons z '2)) "This" t nil 'test state)))
   (value (equal x nil))))

(must-succeed*
 (defun mycar (x) (declare (xargs :verify-guards nil)) (car x))
 (defun f (x) (mbe :logic (mycar x) :exec (if (consp x) (car x) nil)))
 (must-eval-to-t
  (b* (((er x) (ensure-term-guard-verified-exec-fns
                (ubody 'f (w state)) "This" t nil 'test state)))
    (value (equal x nil)))))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (ensure-term-guard-verified-exec-fns
   '(cons (f x) '1) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (ensure-term-guard-verified-exec-fns
   '(cons (f (g x)) '1) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (defun h (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (ensure-term-guard-verified-exec-fns
   '(cons (f (g x)) (h z)) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-term-does-not-call
               '(len (cons z '2)) 'atom "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-term-does-not-call 'zz 'atom "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-term-does-not-call '(len (cons z '2)) 'len "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-term-does-not-call '(len (cons z '2)) 'cons "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-term-if-call '(if a b c) "This" t nil 'test state)))
   (value (equal x (list 'a 'b 'c)))))

(must-eval-to-t
 (b* (((er x) (ensure-term-if-call '(if q) "This" t nil 'test state)))
   (value (equal x (list 'q nil nil)))))

(must-fail
 (ensure-term-if-call '(len x) "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-term-if-call '(len (if e t u)) "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-term-not-call-of 'var 'f "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-term-not-call-of ''44 'f "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-term-not-call-of '(car a) 'f "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-term-not-call-of '(f '1) 'f "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-term-not-call-of '(fgh '1) 'fgh "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-lambda-logic-mode
               '(lambda (x y z) (cons x (len y))) "This" t nil 'test state)))
   (value (equal x nil))))

(must-succeed*
 (defun f (x) (declare (xargs :mode :program)) x)
 (must-fail
  (ensure-lambda-logic-mode
   '(lambda (x y z) (cons (f x) (cons y z))) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

(must-succeed*
 (defun f (x) (declare (xargs :mode :program)) x)
 (defun g (x) (declare (xargs :mode :program)) x)
 (must-fail
  (ensure-lambda-logic-mode
   '(lambda (x y z) (cons (f x) (cons (g y) z))) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

(must-succeed*
 (defun f (x) (declare (xargs :mode :program)) x)
 (defun g (x) (declare (xargs :mode :program)) x)
 (defun h (x) (declare (xargs :mode :program)) x)
 (must-fail
  (ensure-lambda-logic-mode
   '(lambda (x y z) (cons (f x) (cons (g y) (h z)))) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-lambda-arity
               '(lambda (x y z) (cons x (len y))) 3 "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-lambda-arity
               '(lambda (x y) (cons x (len y))) 2 "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-lambda-arity
               '(lambda (x) (cons x (len x))) 1 "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-lambda-arity '(lambda () '3) 0 "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-lambda-arity '(lambda (x y) (cons x y)) 0 "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-lambda-arity '(lambda (x y) (cons x y)) 1 "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-lambda-arity '(lambda (x y) (cons x y)) 8 "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-lambda-guard-verified-fns
               '(lambda (z) (len (cons z '2))) "This" t nil 'test state)))
   (value (equal x nil))))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (ensure-lambda-guard-verified-fns
   '(lambda (x) (cons (f x) '1)) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (ensure-lambda-guard-verified-fns
   '(lambda (x) (cons (f (g x)) '1)) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (defun h (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (ensure-lambda-guard-verified-fns
   '(lambda (x z) (cons (f (g x)) (h z))) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-lambda-guard-verified-exec-fns
               '(lambda (z) (len (cons z '2))) "This" t nil 'test state)))
   (value (equal x nil))))

(must-succeed*
 (defun mycar (x) (declare (xargs :verify-guards nil)) (car x))
 (defun f (x) (mbe :logic (mycar x) :exec (if (consp x) (car x) nil)))
 (must-eval-to-t
  (b* (((er x) (ensure-lambda-guard-verified-exec-fns
                `(lambda (x) ,(ubody 'f (w state))) "This" t nil 'test state)))
    (value (equal x nil)))))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (ensure-lambda-guard-verified-exec-fns
   '(lambda (x) (cons (f x) '1)) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (ensure-lambda-guard-verified-exec-fns
   '(lambda (x) (cons (f (g x)) '1)) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (defun h (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (ensure-lambda-guard-verified-exec-fns
   '(lambda (x z) (cons (f (g x)) (h z))) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-lambda-closed
               '(lambda (x) (cons x (len x))) "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-lambda-closed '(lambda (x) (cons x y)) "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-lambda-closed
  '(lambda (x) (cons x (cons y z))) "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x)
       (ensure-function/lambda-arity '(nil nil) 2 "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x)
       (ensure-function/lambda-arity '(state) 1 "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-function/lambda-arity '(nil state nil) 4 "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function/lambda-arity '(nil state nil) 1 "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function/lambda-arity '(nil state nil) 0 "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-function/lambda-no-stobjs
               '(nil nil nil) '(nil nil) "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-function/lambda-no-stobjs
  '(nil state) '(nil nil) "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function/lambda-no-stobjs '(nil) '(nil state) "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function/lambda-no-stobjs '(state) '(state) "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x)
       (ensure-function/lambda-logic-mode 'cons "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x)
       (ensure-function/lambda-logic-mode 'len "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-function/lambda-logic-mode
               '(lambda (x y z) (cons x (len y))) "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-function/lambda-logic-mode 'untranslate "This" t nil 'test state)
 :with-output-off nil)

(must-succeed*
 (defun f (x) (declare (xargs :mode :program)) x)
 (must-fail
  (ensure-function/lambda-logic-mode
   '(lambda (x y z) (cons (f x) (cons y z))) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

(must-succeed*
 (defun f (x) (declare (xargs :mode :program)) x)
 (defun g (x) (declare (xargs :mode :program)) x)
 (must-fail
  (ensure-function/lambda-logic-mode
   '(lambda (x y z) (cons (f x) (cons (g y) z))) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

(must-succeed*
 (defun f (x) (declare (xargs :mode :program)) x)
 (defun g (x) (declare (xargs :mode :program)) x)
 (defun h (x) (declare (xargs :mode :program)) x)
 (must-fail
  (ensure-function/lambda-logic-mode
   '(lambda (x y z) (cons (f x) (cons (g y) (h z)))) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-function/lambda-guard-verified-fns
               'cons "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-function/lambda-guard-verified-fns
               'len "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-function/lambda-guard-verified-fns
               '(lambda (z) (len (cons z '2))) "This" t nil 'test state)))
   (value (equal x nil))))

(must-succeed*
 (defun h (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (ensure-function/lambda-guard-verified-fns 'h "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (ensure-function/lambda-guard-verified-fns
   '(lambda (x) (cons (f x) '1)) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (ensure-function/lambda-guard-verified-fns
   '(lambda (x) (cons (f (g x)) '1)) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (defun h (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (ensure-function/lambda-guard-verified-fns
   '(lambda (x z) (cons (f (g x)) (h z))) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-function/lambda-guard-verified-exec-fns
               'cons "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-function/lambda-guard-verified-exec-fns
               'len "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-function/lambda-guard-verified-exec-fns
               '(lambda (z) (len (cons z '2))) "This" t nil 'test state)))
   (value (equal x nil))))

(must-succeed*
 (defun mycar (x) (declare (xargs :verify-guards nil)) (car x))
 (defun f (x) (mbe :logic (mycar x) :exec (if (consp x) (car x) nil)))
 (must-eval-to-t
  (b* (((er x) (ensure-function/lambda-guard-verified-exec-fns
                `(lambda (x) ,(ubody 'f (w state))) "This" t nil 'test state)))
    (value (equal x nil)))))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (ensure-function/lambda-guard-verified-exec-fns
   '(lambda (x) (cons (f x) '1)) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (ensure-function/lambda-guard-verified-exec-fns
   '(lambda (x) (cons (f (g x)) '1)) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards nil)) x)
 (defun h (x) (declare (xargs :verify-guards nil)) x)
 (must-fail
  (ensure-function/lambda-guard-verified-exec-fns
   '(lambda (x z) (cons (f (g x)) (h z))) "This" t nil 'test state)
  :with-output-off nil)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-function/lambda-closed 'cons "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-function/lambda-closed
               '(lambda (x) (cons x (len x))) "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-function/lambda-closed
  '(lambda (x) (cons x y)) "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function/lambda-closed
  '(lambda (x) (cons x (cons y z))) "This" t nil 'test state)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-eval-to-t
 (b* (((er x) (ensure-function/lambda/term-number-of-results
               '(nil) 1 "This" t nil 'test state)))
   (value (equal x nil))))

(must-eval-to-t
 (b* (((er x) (ensure-function/lambda/term-number-of-results
               '(nil state) 2 "This" t nil 'test state)))
   (value (equal x nil))))

(must-fail
 (ensure-function/lambda/term-number-of-results
  '(nil state) 1 "This" t nil 'test state)
 :with-output-off nil)

(must-fail
 (ensure-function/lambda/term-number-of-results
  '(nil state) 5 "This" t nil 'test state)
 :with-output-off nil)
