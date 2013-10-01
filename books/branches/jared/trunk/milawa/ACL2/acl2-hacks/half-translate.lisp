;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
(defun lambda-wrapper (x y z) (list x y z))
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
             ((and (consp (car x))
                   (equal (caar x) 'lambda))
              (let ((formals (second (car x)))
                    (body    (third (car x)))
                    (actuals (cdr x)))
                `(lambda-wrapper (quote ,formals)
                                 ,(half-translate-rw body)
                                 (list ,@(half-translate-rw-list actuals)))))
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
             ((equal (car x) 'lambda-wrapper)
              (let ((formals (second (second x))) ;; (second x) = (quote formals)
                    (body    (half-translate-unrewrite (third x)))
                    (actuals (half-translate-unrewrite-list (unzip-cons-list (fourth x)))))
                `((lambda ,formals ,body) ,@actuals)))
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
                            ((lambda (x y z) (+ x (or y z))) 1 2 (and 3 4 5)))
                           (t
                            (list a b c))))))
  (half-translate term state))
|#


