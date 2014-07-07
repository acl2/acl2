; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "ACL2")

;; We introduce the function half-translate, which expands away any ACL2 macros
;; we don't know how to handle, but leaves in tact the Milawa-supported macros
;; such as let, let*, and, or, etc.
;;
;; We do this in a stupid and straightforward way.
;;
;;  1. We rewrite the macros we recognize into "wrappers" that ACL2 will not touch.
;;  2. We use ACL2's translator to get rid of ACL2-specific macros
;;  3. We finally unrewrite the "wrappers" back into their macro form.
;;
;; Gaa, we need to try to do this using trans1 instead and iterating.

(defun tuplep (n x)
  (declare (xargs :mode :program))
  (if (zp n)
      (equal x nil)
    (and (consp x)
         (tuplep (- n 1) (cdr x)))))

(defun tuple-listp (n x)
  (declare (xargs :mode :program))
  (if (consp x)
      (and (tuplep n (car x))
           (tuple-listp n (cdr x)))
    t))

(defun list2-list (x y)
  (declare (xargs :mode :program))
  (if (consp x)
      (cons (list (car x) (car y))
            (list2-list (cdr x) (cdr y)))
    nil))

(defun and-wrapper (x) x)
(defun or-wrapper (x) x)
(defun list-wrapper (x) x)
(defun cond-wrapper (x y) (list x y))
(defun let-wrapper (a b c d) (list a b c d))
(defun let*-wrapper (a b c d) (list a b c d))
(defun first-wrapper (x) x)
(defun second-wrapper (x) x)
(defun third-wrapper (x) x)
(defun fourth-wrapper (x) x)
(defun fifth-wrapper (x) x)


(mutual-recursion

 (defun half-translate-rw (x)
   (declare (xargs :mode :program))
   (if (consp x)
       (cond ((equal (car x) 'quote)
              ;; Don't descend into quoted terms
              x)
             ((equal (car x) 'MILAWA::first)
              `(first-wrapper ,(half-translate-rw (second x))))
             ((equal (car x) 'MILAWA::second)
              `(second-wrapper ,(half-translate-rw (second x))))
             ((equal (car x) 'MILAWA::third)
              `(third-wrapper ,(half-translate-rw (second x))))
             ((equal (car x) 'MILAWA::fourth)
              `(fourth-wrapper ,(half-translate-rw (second x))))
             ((equal (car x) 'MILAWA::fifth)
              `(fifth-wrapper ,(half-translate-rw (second x))))
             ((equal (car x) 'and)
              `(and-wrapper (list ,@(half-translate-rw-list (cdr x)))))
             ((equal (car x) 'or)
              `(or-wrapper (list ,@(half-translate-rw-list (cdr x)))))
             ((equal (car x) 'list)
              `(list-wrapper (list ,@(half-translate-rw-list (cdr x)))))
             ((and (equal (car x) 'cond)
                   (tuple-listp 2 (cdr x)))
              (let ((tests (strip-cars (cdr x)))
                    (bodies (strip-cadrs (cdr x))))
                `(cond-wrapper (list ,@(half-translate-rw-list tests))
                               (list ,@(half-translate-rw-list bodies)))))
             ((or (equal (car x) 'let)
                  (equal (car x) 'let*))
              (let* ((wrapper   (if (equal (car x) 'let) 'let-wrapper 'let*-wrapper))
                     (let-pairs (second x))
                     (vars      (strip-cars let-pairs))
                     (vals      (strip-cadrs let-pairs))
                     (decl      (if (equal (len x) 4) (third x) nil))
                     (body      (if (equal (len x) 4) (fourth x) (third x))))
                `(,wrapper (quote ,vars)
                           (list ,@(half-translate-rw-list vals))
                           (quote ,decl)
                           ,(half-translate-rw body))))
             ;; BOZO add support for lambdas case
             (t
              ;; Not one of our macros to protect, descend through it
              (cons (car x)
                    (half-translate-rw-list (cdr x)))))
     x))

 (defun half-translate-rw-list (x)
   (declare (xargs :mode :program))
   (if (consp x)
       (cons (half-translate-rw (car x))
             (half-translate-rw-list (cdr x)))
     nil)))

(defun unzip-cons-list (x)
  ;; X is a list like (cons a (cons b 'nil))
  ;; We need to extract (a b).
  (if (and (consp x)
           (equal (car x) 'cons))
      (cons (second x)
            (unzip-cons-list (third x)))
    nil))

(mutual-recursion

 (defun half-translate-unrewrite (x)
   (declare (xargs :mode :program))
   (if (consp x)
       (cond ((equal (car x) 'quote)
              (if (or (natp (second x))
                      (equal (second x) t)
                      (equal (second x) nil))
                  ;; Unquote values which don't need quotes
                  (second x)
                x))
             ((equal (car x) 'first-wrapper)
              `(MILAWA::first ,(half-translate-unrewrite (second x))))
             ((equal (car x) 'second-wrapper)
              `(MILAWA::second ,(half-translate-unrewrite (second x))))
             ((equal (car x) 'third-wrapper)
              `(MILAWA::third ,(half-translate-unrewrite (second x))))
             ((equal (car x) 'fourth-wrapper)
              `(MILAWA::fourth ,(half-translate-unrewrite (second x))))
             ((equal (car x) 'fifth-wrapper)
              `(MILAWA::fifth ,(half-translate-unrewrite (second x))))
             ((equal (car x) 'and-wrapper)
              ;; (and-wrapper (cons a (cons b (cons c nil)))) ==> (and a b c)
              `(and ,@(half-translate-unrewrite-list (unzip-cons-list (second x)))))
             ((equal (car x) 'or-wrapper)
              `(or ,@(half-translate-unrewrite-list (unzip-cons-list (second x)))))
             ((equal (car x) 'list-wrapper)
              `(list ,@(half-translate-unrewrite-list (unzip-cons-list (second x)))))
             ((equal (car x) 'cond-wrapper)
              `(cond ,@(list2-list (half-translate-unrewrite-list (unzip-cons-list (second x)))
                                   (half-translate-unrewrite-list (unzip-cons-list (third x))))))
             ((or (equal (car x) 'let*-wrapper)
                  (equal (car x) 'let-wrapper))
              (let ((form (if (equal (car x) 'let*-wrapper) 'let* 'let))
                    (vars (second (second x))) ;; (second x) = (quote ,vars)
                    (vals (half-translate-unrewrite-list (unzip-cons-list (third x))))
                    ;(decl (second (fourth x))) ;; (fourth x) = (quote [(declare ...)])
                    (body (half-translate-unrewrite (fifth x))))
                `(,form ,(list2-list vars vals)
                        ;,@(if decl (list decl) nil)
                        ,body)))
             (t
              (cons (car x)
                    (half-translate-unrewrite-list (cdr x)))))
     x))

 (defun half-translate-unrewrite-list (x)
   (declare (xargs :mode :program))
   (if (consp x)
       (cons (half-translate-unrewrite (car x))
             (half-translate-unrewrite-list (cdr x)))
     nil)))


(defun half-translate (x state)
  (declare (xargs :mode :program :stobjs state))
  (mv-let (erp val state)
          (translate (half-translate-rw x) nil nil nil 'half-translate (w state) state)
          (if erp
              (mv erp val state)
            (mv nil (half-translate-unrewrite val) state))))

;; Here's some test code:
#|
; (include-book "../utilities/primitives" :ttags :all)
(let ((term '(append (let* ((a (+ 1 '(2 . 5)))
                            (b (or (MILAWA::first x) (MILAWA::second y)))
                            (c (* a b)))
                       (list a b c))
                     (let ((a (+ 1 2))
                           (b (or 'foo y))
                           (c (* a b)))
                       (list a b c))
                     (cond ((equal (MILAWA::third x) (or 1 a))
                            (and y z))
                           ((equal x 2)
                            (or y z))
                           (t
                            (list a b c))))))
  (half-translate term state))
|#







