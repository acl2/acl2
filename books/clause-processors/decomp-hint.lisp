; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Sol Swords <sswords@centtech.com>


(in-package "ACL2")

;; This book introduces computed hints useful for when one wants to
;; systematically open up a cons structure and relieve proof
;; obligations about local properties.

;; At each step of the proof, the computed hint has a particular term
;; it is concentrating on. It will first delete any literals in the
;; current clause which do not mention that term.  It will then open
;; up any function which has that term as an argument.  When all such
;; functions have been expanded, it will heuristically choose to next
;; concentrate on either the CAR or CDR of that term based on (first)
;; which appears in the conclusion, and (if neither) which appear in
;; the rest of the clause.

;; We include two versions of the computed hint.  The first, which can
;; be invoked as (STRUCTURAL-DECOMP X) where X is the term to begin
;; decomposing, may lead to proof failure if at some point it
;; heuristically chooses the wrong term to concentrate on.  The
;; second, (STRUCTURAL-DECOMP-CAREFUL X), instead generates OR hints
;; at each heuristic decision, first trying the heuristic best guess,
;; then the other possible guess, and finally giving up.


(include-book "join-thms")

(include-book "std/util/bstar" :dir :system)



(mutual-recursion
 (defun find-expands-for-arg-term (x arg world def-alist exclude)
   (b* (((when (atom x)) (mv nil nil))
        ((when (eq (car x) 'quote)) (mv nil nil))
        ((mv expands found)
         (find-expands-for-arg-list
          (cdr x) arg world def-alist exclude))
        ;; If expansion is found in the args, don't expand x yet.
        ((when expands) (mv expands found))
        ((unless (or found (member-equal arg (cdr x))))
         (mv nil nil))
        ;; check that x is expandable.
        ((when (or (member (car x) exclude)
                   (consp (car x))
                   (member (car x) '(not car cdr))))
         (mv nil nil))
        (look (assoc (car x) def-alist))
        ((when look)
         (mv `((:with ,(cdr look) ,x)) nil))
        ((when (fgetprop (car x) 'def-bodies nil world))
         (mv (list x) nil)))
     (mv nil t)))
 (defun find-expands-for-arg-list (x arg world def-alist exclude)
   (if (atom x)
       (mv nil nil)
     (b* (((mv car-ex car-f)
           (find-expands-for-arg-term (car x) arg world def-alist exclude))
          ((mv cdr-ex cdr-f)
           (find-expands-for-arg-list (cdr x) arg world def-alist exclude)))
       (mv (union-equal car-ex cdr-ex)
           (or car-f cdr-f))))))

(defun find-expands-for-arg-clause (x arg world def-alist exclude)
  (mv-let (expands found)
    (find-expands-for-arg-list x arg world def-alist exclude)
    (declare (ignore found))
    expands))

(mutual-recursion
 (defun present-in-term (x subt)
   (cond ((equal x subt) t)
         ((atom x) nil)
         ((eq (car x) 'quote) nil)
         (t (present-in-term-list (cdr x) subt))))
 (defun present-in-term-list (x subt)
   (and (consp x)
        (or (present-in-term (car x) subt)
            (present-in-term-list (cdr x) subt)))))

(defun structure-decompose (x)
  (declare (ignore x)) t)

(in-theory (disable structure-decompose
                    (structure-decompose)
                    (:type-prescription structure-decompose)))

(defevaluator strdec-ev strdec-ev-lst
  ((if x y z) (structure-decompose x) (not x)))

(def-join-thms strdec-ev)

(defun consed-subterms (term)
  (case-match term
    (('cons a b . &)
     (union-equal (consed-subterms a)
                  (consed-subterms b)))
    (& (list term))))

(defun consed-subterm-present-in-term (term consed)
  (if (atom consed)
      nil
    (or (present-in-term term (car consed))
        (consed-subterm-present-in-term term (cdr consed)))))

(defun remove-terms-without-present (clause subterms)
  (if (atom clause)
      clause
    (let ((rest (remove-terms-without-present (cdr clause) subterms)))
      (if (consed-subterm-present-in-term (car clause) subterms)
          (if (equal rest (cdr clause))
              clause
            (cons (car clause) rest))
        rest))))

(defthm strdec-ev-remove-terms-without-present
  (implies (strdec-ev (disjoin (remove-terms-without-present
                                clause struct))
                      alist)
           (strdec-ev (disjoin clause) alist)))

(defun select-expand-substruct (clause substruct)
  (list (cons `(not (structure-decompose ,substruct))
              (remove-terms-without-present
               clause (consed-subterms substruct)))))

(defun remove-irrel-cp (clause substruct)
  (list (remove-terms-without-present
         clause (consed-subterms substruct))))

(defthm select-expand-substruct-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (strdec-ev (conjoin-clauses
                            (select-expand-substruct
                             clause substruct))
                           a))
           (strdec-ev (disjoin clause) a))
  :hints (("goal" :in-theory
           (e/d (structure-decompose)
                (consed-subterms
                 consed-subterm-present-in-term))))
  :rule-classes :clause-processor)


(defthm remove-irrel-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (strdec-ev (conjoin-clauses
                            (remove-irrel-cp
                             clause substruct))
                           a))
           (strdec-ev (disjoin clause) a))
  :hints (("goal" :in-theory
           (e/d (structure-decompose)
                (consed-subterms
                 consed-subterm-present-in-term))))
  :rule-classes :clause-processor)

(defun structural-decomp-hint-careful (clause arg stablep state def-alist exclude)
  (declare (xargs :stobjs state
                  :mode :program))
  (b* (((unless stablep) (value nil))
       (world (w state))
       ((er arg) (translate arg t nil nil 'structural-decomp-hint-careful
                            world state))
       (expands
        (find-expands-for-arg-clause clause arg world def-alist exclude))
       ((when expands)
        (value
         `(:computed-hint-replacement
           ((structural-decomp-hint-careful
             clause ',arg stable-under-simplificationp state ',def-alist ',exclude))
           :expand ,expands)))
       ;; Heuristically decide based on presence in the conclusion
       ;; or in rest of clause whether to prefer expanding
       ;; (car arg) or (cdr arg)
       (car `(car ,arg))
       (cdr `(cdr ,arg))
       (concl (car (last clause)))
       ((mv 1st 2nd give-up)
        (cond ((present-in-term concl car) (mv car cdr nil))
              ((present-in-term concl cdr) (mv cdr car nil))
              ((present-in-term-list clause car)
               (mv car cdr nil))
              ((present-in-term-list clause cdr)
               (mv cdr car nil))
              (t (mv car cdr t)))))
    (if give-up
        (prog2$ (cw "Giving up on structural expansion~%")
                (value '(:no-op t)))
      (value `(:computed-hint-replacement
               ((after-select-substruct-hint
                 clause stable-under-simplificationp state ',def-alist ',exclude))
               :or ((:clause-processor
                     (select-expand-substruct clause ',1st))
                    (:clause-processor
                     (select-expand-substruct clause ',2nd))
                    (:no-op t)))))))

(defun after-select-substruct-hint (clause stablep state def-alist exclude)
  (declare (xargs :stobjs state
                  :mode :program))
  ;; (prog2$ (cw "Running after-select-substruct-hint~%")
  (let ((term (car clause)))
    (case-match term
      (('not ('structure-decompose arg))
       (structural-decomp-hint-careful clause arg stablep state def-alist exclude))
      (& (prog2$ (cw "After-select-substruct-hint didn't find the
chosen structure to decompose. Clause: ~x0~%" clause)
                 (value '(:no-op t)))))))

(defun structural-decomp-hint-fast (clause arg stablep state def-alist exclude)
  (declare (xargs :stobjs state
                  :mode :program))
  (b* (((unless stablep) (value nil))
       (world (w state))
       ((er arg) (translate arg t nil nil 'structural-decomp-hint-fast
                            world state))
       (expands (find-expands-for-arg-clause clause arg world def-alist exclude))
       ((when expands)
        (value `(:computed-hint-replacement
                 ((structural-decomp-hint-fast
                   clause ',arg stable-under-simplificationp state
                   ',def-alist ',exclude))
                 :expand ,expands)))
       ;; Heuristically decide based on presence in the conclusion
       ;; or in rest of clause whether to prefer expanding
       ;; (car arg) or (cdr arg)
       (car (if (and (consp arg) (eq (car arg) 'cons)) (cadr arg) `(car ,arg)))
       (cdr (if (and (consp arg) (eq (car arg) 'cons)) (caddr arg) `(cdr ,arg)))
       (concl (car (last clause)))
       ((mv 1st give-up)
        (cond ((present-in-term concl car) (mv car nil))
              ((present-in-term concl cdr) (mv cdr nil))
              ((present-in-term-list clause car)
               (mv car nil))
              ((present-in-term-list clause cdr)
               (mv cdr nil))
              (t (mv car t)))))
    (if give-up
        (prog2$ (cw "Giving up on structural expansion~%")
                (value '(:no-op t)))
      (value `(:computed-hint-replacement
               ((structural-decomp-hint-fast
                 clause ',1st stable-under-simplificationp state ',def-alist ',exclude))
               :clause-processor
               (remove-irrel-cp clause ',1st))))))


(defmacro structural-decomp (arg &key do-not-expand def-alist)
  `(structural-decomp-hint-fast
    clause ',arg stable-under-simplificationp state
    (append ',def-alist (table-alist 'structural-decomp-defs (w state)))
    ,do-not-expand))

(defmacro structural-decomp-careful (arg &key do-not-expand def-alist)
  `(structural-decomp-hint-careful
    clause ',arg stable-under-simplificationp state
    (append ',def-alist (table-alist 'structural-decomp-defs (w state)))
    ,do-not-expand))

