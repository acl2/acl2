; GL - A Symbolic Simulation Framework for ACL2
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

(in-package "GL")
(include-book "gl-util")
(include-book "std/util/bstar" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "misc/hons-help2" :dir :system)
(include-book "clause-processors/join-thms" :dir :system)
(include-book "centaur/misc/hons-sets" :dir :system)


(defevaluator apply-cond-ev apply-cond-ev-lst
  ((if a b c) (eq a b) (equal a b)))

(acl2::def-join-thms apply-cond-ev)

(defun collect-conds-and-default (x)
  (case-match x
    (('if test then else)
     (mv-let (default conds)
       (collect-conds-and-default else)
       (mv default (hons-acons test then conds))))
    (& (mv x nil))))

(defun eval-conds (conds al)
  (if (atom conds)
      (mv nil nil)
    (if (apply-cond-ev (caar conds) al)
        (mv t (apply-cond-ev (cdar conds) al))
      (eval-conds (cdr conds) al))))

(defthm collect-conds-and-default-eval-conds
  (mv-let (default conds)
    (collect-conds-and-default x)
    (mv-let (matched res)
      (eval-conds conds al)
      (equal (if matched res (apply-cond-ev default al))
             (apply-cond-ev x al))))
  :rule-classes nil)

(defun no-conds-with-same-fn (fn conds)
  (or (atom conds)
      (let* ((pair (car conds))
             (test (car pair)))
        (case-match test
          (('if ('eq 'f ('quote fn2)) & ''nil)
           (and (not (equal fn fn2))
                (no-conds-with-same-fn fn (cdr conds))))
          (& nil)))))

(defun no-duplicate-condsp (conds)
  (or (atom conds)
      (let* ((pair (car conds))
             (test (car pair)))
        (case-match test
          (('if ('eq 'f ('quote fn)) & ''nil)
           (and (no-conds-with-same-fn fn (cdr conds))
                (no-duplicate-condsp (cdr conds))))
          (& nil)))))

(defun alist-no-cond-fns (al conds)
  (or (atom conds)
      (let* ((pair (car conds))
             (test (car pair)))
        (case-match test
          (('if ('eq 'f ('quote fn)) & ''nil)
           (and (not (hons-get fn al))
                (alist-no-cond-fns al (cdr conds))))
          (& nil)))))

(defun exclusive-condsp (conds acc)
  (if (atom conds)
      (prog2$ (flush-hons-get-hash-table-link acc) t)
    (let* ((pair (car conds))
           (test (car pair)))
      (case-match test
        (('if ('eq 'f ('quote fn)) & ''nil)
         (if (hons-get fn acc)
             (cw "Exclusive-condsp: repeat function: ~x0~%" fn)
           (exclusive-condsp (cdr conds) (hons-acons fn t acc))))
        (& (cw "Exclusive-condsp: bad test: ~x0~%" test))))))

(defun remove-assoc (x al)
  (if (atom al)
      al
    (if (and (consp (car al))
             (equal x (caar al)))
        (remove-assoc x (cdr al))
      (cons (car al) (remove-assoc x (cdr al))))))

(defthm hons-assoc-equal-remove-assoc
  (equal (hons-assoc-equal x (remove-assoc y al))
         (and (not (equal x y))
              (hons-assoc-equal x al)))
  :hints(("Goal" :in-theory (enable hons-assoc-equal))))

(defthm exclusive-condsp-acons1
  (implies (no-conds-with-same-fn k conds)
           (equal (exclusive-condsp conds (remove-assoc k al))
                  (exclusive-condsp conds al))))

(defthm remove-assoc-when-not-hons-assoc-equal
  (implies (not (hons-assoc-equal k al))
           (equal (remove-assoc k al) al))
  :hints(("Goal" :in-theory (enable hons-assoc-equal))))

(defthm exclusive-condsp-acons
  (implies (and (no-conds-with-same-fn k conds)
                (not (hons-assoc-equal k al)))
           (equal (exclusive-condsp conds (cons (cons k v) al))
                  (exclusive-condsp conds al)))
  :hints (("goal" :use ((:instance exclusive-condsp-acons1
                                   (al (cons (cons k v) al))))
           :in-theory (disable exclusive-condsp-acons1))))

(defthm exclusive-condsp-is-no-duplicate-condsp1
  (equal (exclusive-condsp conds al)
         (and (alist-no-cond-fns al conds)
              (no-duplicate-condsp conds)))
  :hints (("goal" :induct (exclusive-condsp conds al)
           :in-theory (enable hons-assoc-equal))))

(defthm exclusive-condsp-is-no-duplicate-condsp
  (equal (exclusive-condsp conds nil)
         (no-duplicate-condsp conds)))

(defthm diff-fn-conds-not-both-true
  (implies (case-match a
             (('if ('eq 'f ('quote fna)) & ''nil)
              (case-match b
                (('if ('eq 'f ('quote fnb)) & ''nil)
                 (not (equal fna fnb))))))
           (not (and (apply-cond-ev a al)
                     (apply-cond-ev b al))))
  :rule-classes nil)

(defthm assoc-no-duplicate-conds-implies-match
  (implies (and (hons-assoc-equal a conds)
                (no-duplicate-condsp conds))
           (case-match a
             (('if ('eq 'f ('quote &)) & ''nil) t)))
  :rule-classes nil)


(defthm hons-assoc-equal-true-cond-eval-conds
  (implies (and (hons-assoc-equal cond lst)
                (apply-cond-ev cond al))
           (mv-nth 0 (eval-conds lst al))))

(defthm no-conds-with-same-fn-and-hons-assoc-equal
  (implies (and (no-conds-with-same-fn fn lst)
                (hons-assoc-equal cond lst))
           (case-match cond
             (('if ('eq 'f ('quote fn2)) & ''nil)
              (not (equal fn2 fn)))))
  :rule-classes nil)

(encapsulate
  ()
  (local (defthm l0
           (implies (and (no-conds-with-same-fn (cdr (assoc-equal 'f al)) (cdr lst))
                         (hons-assoc-equal cond (cdr lst))
                         (apply-cond-ev cond al))
                    (equal (apply-cond-ev (cdar lst) al)
                           (apply-cond-ev (cdr (hons-assoc-equal cond (cdr lst))) al)))
           :hints(("Goal"
                   :use ((:instance no-conds-with-same-fn-and-hons-assoc-equal
                                    (fn (cdr (assoc-eq 'f al)))
                                    (lst (cdr lst))))))))

  (defthm apply-cond-of-assoc-is-eval-conds
    (implies (and (no-duplicate-condsp lst)
                  (hons-assoc-equal cond lst)
                  (apply-cond-ev cond al))
             (equal (mv-nth 1 (eval-conds lst al))
                    (apply-cond-ev (cdr (hons-assoc-equal cond lst))
                                   al)))))

(defun hons-alist-keys-subset (lst1 lst2)
  (or (atom lst1)
      (if (consp (car lst1))
          (and (hons-get (caar lst1) lst2)
               (hons-alist-keys-subset (cdr lst1) lst2))
        (hons-alist-keys-subset (cdr lst1) lst2))))



(defthm hons-alist-keys-subset-impl-eval-conds
  (implies (and (hons-alist-keys-subset lst1 lst2)
                (mv-nth 0 (eval-conds lst1 al)))
           (mv-nth 0 (eval-conds lst2 al))))

(defun conds-match (lst1 lst2)
  (if (atom lst1)
      (mv t nil)
    (if (consp (car lst1))
        (let ((lk (hons-get (caar lst1) lst2)))
          (if lk
              (mv-let (ok rest)
                (conds-match (cdr lst1) lst2)
                (if (equal (cdr lk) (cdar lst1))
                    (mv ok rest)
                  (mv ok (cons `((equal ,(cdr lk) ,(cdar lst1)))
                               rest))))
            (mv nil nil)))
      (conds-match (cdr lst1) lst2))))

(defthm conds-match-impl-eval-conds
  (implies (and (mv-nth 0 (conds-match lst1 lst2))
                (mv-nth 0 (eval-conds lst1 al)))
           (mv-nth 0 (eval-conds lst2 al))))

(defthm conds-match-and-no-duplicate-conds
  (implies (and (mv-nth 0 (conds-match lst1 lst2))
                (no-duplicate-condsp lst1)
                (no-duplicate-condsp lst2)
                (mv-nth 0 (eval-conds lst1 al))
                (apply-cond-ev
                 (conjoin-clauses
                  (mv-nth 1 (conds-match lst1 lst2)))
                 al))
           (equal (mv-nth 1 (eval-conds lst2 al))
                  (mv-nth 1 (eval-conds lst1 al))))
  :hints(("Goal" :in-theory (enable conjoin-clauses))))

(defun apply-cond-terms-equal (term1 term2)
  (b* (((mv def1 conds1)
        (collect-conds-and-default term1))
       ((mv def2 conds2)
        (collect-conds-and-default term2))
       ((mv match equivs)
        (conds-match conds1 conds2))
       (okp-list (list match
                       (exclusive-condsp conds1 nil)
                       (exclusive-condsp conds2 nil)
                       (hons-alist-keys-subset conds2 conds1)))
       (okp (acl2::and-list okp-list))
       (- (flush-hons-get-hash-table-link conds1))
       (- (flush-hons-get-hash-table-link conds2)))
    (if okp
        (if (equal def1 def2)
            equivs
          (cons `((equal ,def1 ,def2)) equivs))
      (prog2$ (cw "cond cp fail: ~x0~%details: ~x1~%"
                  okp-list
                  (acl2::hons-set-diff (strip-cars conds2)
                                       (strip-cars conds1)))
              (list `((equal ,term1 ,term2)))))))

(defthm apply-cond-terms-equal-correct
  (implies (apply-cond-ev
            (conjoin-clauses
             (apply-cond-terms-equal term1 term2))
            al)
           (equal (equal (apply-cond-ev term1 al)
                         (apply-cond-ev term2 al))
                  t))
  :hints (("goal" :use ((:instance
                         collect-conds-and-default-eval-conds
                         (x term1))
                        (:instance
                         collect-conds-and-default-eval-conds
                         (x term2)))
           :in-theory (e/d (conjoin-clauses)
                           (no-duplicate-condsp
                            default-car
                            default-cdr
                            eval-conds
                            conds-match)))))


(defun apply-cond-cp (clause)
  (if (consp clause)
      (let ((term (car (last clause))))
        (case-match term
          (('equal term1 term2)
           (apply-cond-terms-equal term1 term2))
          (& (list clause))))
    (list clause)))

(defthm last-impl-disjoin
  (implies (and (consp clause)
                (apply-cond-ev (car (last clause)) al))
           (apply-cond-ev (disjoin clause) al))
  :hints(("Goal" :in-theory (e/d ()
                                 (disjoin last))
          :induct (len clause)
          :expand ((disjoin clause)
                   (last clause)))))

(defthm apply-cond-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp al)
                (apply-cond-ev
                 (conjoin-clauses
                  (apply-cond-cp clause))
                 al))
           (apply-cond-ev (disjoin clause) al))
  :hints(("Goal" :in-theory (e/d (conjoin-clauses)
                                 (disjoin
                                  last
                                  last-impl-disjoin
                                  apply-cond-terms-equal))
          :use ((:instance last-impl-disjoin ))
          :do-not-induct t))
  :rule-classes :clause-processor)
