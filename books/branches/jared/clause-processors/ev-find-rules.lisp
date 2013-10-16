;; ef-find-rule
;; Copyright (C) 2012 Centaur Technology
;;
;; Contact:
;;   Centaur Technology Formal Verification Group
;;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;;   http://www.centtech.com/
;;
;; This program is free software; you can redistribute it and/or modify it under
;; the terms of the GNU General Public License as published by the Free Software
;; Foundation; either version 2 of the License, or (at your option) any later
;; version.  This program is distributed in the hope that it will be useful but
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;; more details.  You should have received a copy of the GNU General Public
;; License along with this program; if not, write to the Free Software
;; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;;
;; Original authors: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

;; Provides a way of finding certain rules about evaluators.  Not 100%
;; foolproof, but should be fairly reliable.

;; This is useful for defining evaluator-related utilities that work whether
;; the evaluator was defined with defevaluator or defevaluator-fast,
;; with :namedp t or nil, etc.

;; If this doesn't work as expected, it's because it's looking for certain
;; theorems in the world, and either:
;; -- it found one that seems to match, but wasn't the one you were thinking
;; of.  This could happen because a theorem was proved that was sufficiently
;; similar to the original that our matching was fooled.
;; -- it didn't find any.  This could happen if, say, the exact phrasing of the
;; evaluator theorems is changed.

;; find the ev-lst function given the ev function or vice versa.  Should be its
;; only sibling.
(defun find-ev-counterpart (ev world)
  (car (remove ev (fgetprop ev 'siblings nil world))))


;; Rewrite-rule fields are: 
;; rune nume hyps equiv lhs rhs subclass heuristic-info backchain-limit-lst
;; var-info match-free
(defun find-matching-rule (hyps equiv lhs rhs lemmas)
  (if (atom lemmas)
      nil
    (or (let* ((rune  (access rewrite-rule (car lemmas) :rune))
               (rhyps  (access rewrite-rule (car lemmas) :hyps))
               (rlhs   (access rewrite-rule (car lemmas) :lhs))
               (rrhs   (access rewrite-rule (car lemmas) :rhs))
               (requiv (access rewrite-rule (car lemmas) :equiv)))
          (and (or (eq hyps :dont-care)  (equal rhyps hyps))
               (or (eq lhs :dont-care)   (equal rlhs lhs))
               (or (eq rhs :dont-care)   (equal rrhs rhs))
               (or (eq equiv :dont-care) (equal requiv equiv))
               rune))
        (find-matching-rule hyps equiv lhs rhs (cdr lemmas)))))

(defun ev-find-fncall-rule-in-lemmas (ev fn lemmas)
  (find-matching-rule
   `((consp x) (equal (car x) ',fn))        ;; hyps
   'equal
   `(,ev x a)                               ;; lhs
   :dont-care
   lemmas))

(defun ev-find-fncall-rule (ev fn world)
  (find-matching-rule
   `((consp x) (equal (car x) ',fn))        ;; hyps
   'equal
   `(,ev x a)                               ;; lhs
   :dont-care ;; could construct it but this seems basically specific enough
   (fgetprop ev 'lemmas nil world)))

(defun ev-find-fncall-generic-rule (ev world)
  (let ((ev-lst (find-ev-counterpart ev world)))
    (find-matching-rule
     '((consp x)
       (synp 'nil '(syntaxp (not (equal a ''nil)))
             '(if (not (equal a ''nil)) 't 'nil))
       (not (equal (car x) 'quote)))
     'equal
     `(,ev x a)
     `(,ev (cons (car x) (kwote-lst (,ev-lst (cdr x) a))) 'nil)
     (fgetprop ev 'lemmas nil world))))

(defun ev-find-variable-rule (ev world)
  (find-matching-rule
   '((symbolp x))
   'equal
   `(,ev x a)
   '(if x (cdr (assoc-equal x a)) 'nil)
   (fgetprop ev 'lemmas nil world)))

(defun ev-find-quote-rule (ev world)
  (find-matching-rule
   '((consp x) (equal (car x) 'quote))
   'equal
   `(,ev x a)
   '(car (cdr x))
   (fgetprop ev 'lemmas nil world)))

(defun ev-find-lambda-rule (ev world)
  (let ((ev-lst (find-ev-counterpart ev world)))
    (find-matching-rule
     '((consp x) (consp (car x)))
     'equal
     `(,ev x a)
     `(,ev (car (cdr (cdr (car x))))
           (pairlis$ (car (cdr (car x)))
                     (,ev-lst (cdr x) a)))
     (fgetprop ev 'lemmas nil world))))

(defun ev-lst-find-atom-rule (ev-lst world)
  (find-matching-rule
   '((not (consp x-lst)))
   'equal
   `(,ev-lst x-lst a)
   ''nil
   (fgetprop ev-lst 'lemmas nil world)))

(defun ev-lst-find-cons-rule (ev-lst world)
  (let ((ev (find-ev-counterpart ev-lst world)))
    (find-matching-rule
     '((consp x-lst))
     'equal
     `(,ev-lst x-lst a)
     `(cons (,ev (car x-lst) a)
            (,ev-lst (cdr x-lst) a))
     (fgetprop ev-lst 'lemmas nil world))))
