; Standard Utilities Library
; Copyright (C) 2014, Oracle and/or its affiliates. All rights reserved.
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: David L. Rager <david.rager@oracle.com>

(in-package "STD")

(local
 (defthm character-listp-of-explode-nonnegative-integer
   (implies (character-listp ans)
            (character-listp
             (explode-nonnegative-integer n print-base ans)))))

(defn string/symbol/integer-list-p (x)
  (cond ((atom x)
         (null x))
        (t
         (and (or (stringp (car x))
                  (symbolp (car x))
                  (integerp (car x)))
              (string/symbol/integer-list-p (cdr x))))))


(defun generate-symbol-fn1 (lst)
  (declare (xargs :guard (string/symbol/integer-list-p lst)))
  (cond ((atom lst)
         nil)
        (t
         (let ((curr (car lst))
               (rest (cdr lst)))
           (cond ((stringp curr)
                  (cons curr
                        (generate-symbol-fn1 rest)))
                 ((symbolp curr)
                  (cons (symbol-name curr)
                        (generate-symbol-fn1 rest)))
                 ((integerp curr)
                  (cons (coerce (explode-atom curr 10)
                                'string)
                        (generate-symbol-fn1 rest)))
                 (t (er hard 'generate-symbol-fn1
                        "Guards are violated")))))))

;; We could include the definition of generate-symbol, but I don't really like
;; its interface.  The lack of a need to quote the provided list is the main
;; objection. E.g.,:

;;; (generate-symbol ("HI" 3 4) "ACL2")

;; (defmacro generate-symbol (string/symbol/decimal-list package-name)
;;   (declare (xargs :guard (string/symbol/integer-list-p string/symbol/decimal-list)))
;;   `(intern ,(string-append-lst (generate-symbol-fn1 string/symbol/decimal-list))
;;            ,package-name))

(defun generate-symbol-in-package-of-symbol (string/symbol/decimal-list symbol)
  (declare (xargs :guard (and (string/symbol/integer-list-p string/symbol/decimal-list)
                              (symbolp symbol))))
  (intern-in-package-of-symbol (string-append-lst (generate-symbol-fn1 string/symbol/decimal-list))
                               symbol))
