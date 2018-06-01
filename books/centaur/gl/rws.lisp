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
(include-book "clause-processors/use-by-hint" :dir :system)
(include-book "clause-processors/multi-env-trick" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "tools/flag" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "misc/hons-help" :dir :system)
(include-book "clause-processors/join-thms" :dir :system)
(local (include-book "centaur/misc/equal-sets" :dir :system))
(local (include-book "centaur/misc/alist-equiv" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/util/support" :dir :System))

;;; What does 'rws' abbreviate, in anything, asks Boyer???

(defevaluator dumb-ev dumb-ev-lst ((equal a b) (if a b c) (use-by-hint x) (not x)
                                   (implies x y)))

(defun dumb-ev-ind (flg x a)
  (declare (xargs :verify-guards nil
                  :measure (acl2-count x)
                  :well-founded-relation o<
                  :mode :logic))
  (if flg
      (cond ((symbolp x)
             (and x (cdr (assoc-eq x a))))
            ((atom x) nil)
            ((eq (car x) 'quote) (car (cdr x)))
            ((consp (car x))
             (cons (dumb-ev-ind nil (cdr x) a)
                   (dumb-ev-ind t (car (cdr (cdr (car x))))
                           (pairlis$ (car (cdr (car x)))
                                     (dumb-ev-lst (cdr x) a)))))
            (t (dumb-ev-ind nil (cdr x) a)))
    (cond ((endp x) nil)
          (t (cons (dumb-ev-ind t (car x) a)
                   (dumb-ev-ind nil (cdr x) a))))))

(acl2::def-join-thms dumb-ev)

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm assoc-eq-is-assoc-equal
;   (equal (assoc-eq x al)
;          (assoc-equal x al)))

(mutual-recursion
 (defun term-subst (x al)
   (declare (xargs :guard (and (pseudo-termp x) (alistp al))))
   (cond ((eq x nil) nil)
         ((atom x) (cdr (assoc-eq x al)))
         ((eq (car x) 'quote) x)
         (t (hons (car x) (term-subst-list (cdr x) al)))))
 (defun term-subst-list (x al)
   (declare (xargs :guard (and (pseudo-term-listp x) (alistp al))))
   (if (endp x)
       nil
     (hons (term-subst (car x) al)
           (term-subst-list (cdr x) al)))))

(defun term-alistp (al)
  (if (atom al)
      (eq al nil)
    (and (consp (car al))
         (symbolp (caar al))
         (pseudo-termp (cdar al))
         (term-alistp (cdr al)))))

(flag::make-flag term-subst-ind term-subst)

(defthm term-alistp-assoc-equal
  (implies (term-alistp al)
           (pseudo-termp (cdr (assoc-equal x al)))))

(defthm len-term-subst-list
  (equal (len (term-subst-list x al))
         (len x)))

(defthm-term-subst-ind pseudo-termp-term-subst
  (term-subst
   (implies (and (pseudo-termp x)
                 (term-alistp al))
            (pseudo-termp (term-subst x al))))
  (term-subst-list
   (implies (and (pseudo-term-listp x)
                 (term-alistp al))
            (pseudo-term-listp (term-subst-list x al))))
  :hints (("goal" :induct (term-subst-ind flag x al)
           :in-theory (disable (:definition pseudo-termp)
                               (:definition pseudo-term-listp)
                               (:definition term-subst)
                               (:definition term-subst-list))
           :expand ((pseudo-termp x)
                    (pseudo-term-listp x)
                    (term-subst x al)
                    (term-subst-list x al)
                    (term-subst nil al)
                    (term-subst-list nil al)))
          (and stable-under-simplificationp
               (flag::expand-calls-computed-hint
                clause '(pseudo-termp pseudo-term-listp)))))


(defun dumb-ev-al (al a)
  (pairlis$ (strip-cars al)
            (dumb-ev-lst (strip-cdrs al) a)))

;; (defthm assoc-equalual-append
;;   (implies (alistp a)
;;            (equal (assoc-equalual v (append a b))
;;                   (or (assoc-equalual v a)
;;                       (assoc-equalual v b)))))

(defthm alistp-pairlis
  (alistp (pairlis$ a b)))

(defthm dumb-ev-al-assoc
  (implies (alistp al)
           (equal (assoc-equal v (dumb-ev-al al a))
                  (and (assoc-equal v al)
                       (cons v (dumb-ev (cdr (assoc-equal v al)) a)))))
  :hints (("goal" :induct (assoc-equal v al))))

(in-theory (disable dumb-ev-al))


(defthm term-subst-correct-lemma
  (if flag
      (implies (and (pseudo-termp x)
                    (alistp al))
               (equal (dumb-ev (term-subst x al) a)
                      (dumb-ev x (dumb-ev-al al a))))
    (implies (and (pseudo-term-listp x)
                  (alistp al))
             (equal (dumb-ev-lst (term-subst-list x al) a)
                    (dumb-ev-lst x (dumb-ev-al al a)))))
  :hints (("goal" :induct (dumb-ev-ind flag x a))
          ("Subgoal *1/6" :in-theory (enable dumb-ev-constraint-0)))
  :rule-classes nil)

(defthm term-subst-correct-rw
  (implies (and (pseudo-termp x)
                (alistp al))
           (equal (dumb-ev (term-subst x al) a)
                  (dumb-ev x (dumb-ev-al al a))))
  :hints (("goal" :use ((:instance term-subst-correct-lemma
                                   (flag t))))))


(memoize 'term-subst)



(mutual-recursion
 (defun beta-reduce-term (x)
   (declare (xargs :guard (pseudo-termp x)
                   :verify-guards nil))
   (cond ((atom x) x)
         ((eq (car x) 'quote) x)
         ((atom (car x))
          (hons (car x) (beta-reduce-list (cdr x))))
         (t (let ((ans (term-subst (beta-reduce-term (caddar x))
                                   (pairlis$ (cadar x)
                                             (beta-reduce-list (cdr x))))))
              (prog2$ (clear-memoize-table 'term-subst)
                      ans)))))
 (defun beta-reduce-list (x)
   (declare (xargs :guard (pseudo-term-listp x)))
   (if (atom x)
       nil
     (hons (beta-reduce-term (car x))
           (beta-reduce-list (cdr x))))))


(flag::make-flag beta-reduce-flag beta-reduce-term)


(defthm pseudo-term-listp-pairlis-term-alistp
  (implies (and (symbol-listp a)
                (pseudo-term-listp x))
           (term-alistp (pairlis$ a x)))
  :hints(("Goal" :in-theory (enable pairlis$))))

(defthm-beta-reduce-flag pseudo-termp-beta-reduce
  (beta-reduce-term
   (implies (pseudo-termp x)
            (pseudo-termp (beta-reduce-term x))))
  (beta-reduce-list
   (implies (pseudo-term-listp x)
            (pseudo-term-listp (beta-reduce-list x))))
  :hints (("goal" :in-theory (disable (:definition beta-reduce-term)
                                      (:definition beta-reduce-list)
                                      term-subst)
           :induct (beta-reduce-flag flag x)
           :expand ((beta-reduce-term x)
                    (beta-reduce-list x)))))

(defthm true-listp-beta-reduce-list
  (true-listp (beta-reduce-list x))
  :hints (("goal" :induct (len x))))

(defthm len-beta-reduce-list
  (equal (len (beta-reduce-list x)) (len x))
  :hints (("goal" :induct (len x))))



(verify-guards beta-reduce-term)

(memoize 'beta-reduce-term :condition '(consp x))

(defthm strip-cars-pairlis
  (implies (and (equal (len a) (len b))
                (true-listp a))
           (equal (strip-cars (pairlis$ a b))
                  a)))

(defthm strip-cdrs-pairlis
  (implies (and (equal (len a) (len b))
                (true-listp b))
           (equal (strip-cdrs (pairlis$ a b))
                  b)))

(defthm beta-reduce-correct-lemma
  (if flg
      (implies (and (pseudo-termp x)
                    (alistp a))
               (equal (dumb-ev (beta-reduce-term x) a)
                      (dumb-ev x a)))
    (implies (and (pseudo-term-listp x)
                  (alistp a))
             (equal (dumb-ev-lst (beta-reduce-list x) a)
                    (dumb-ev-lst x a))))
  :hints (("goal" :in-theory (e/d (pairlis$)
                                  ((:definition beta-reduce-term)
                                   (:definition beta-reduce-list)
                                   term-subst))
           :induct (dumb-ev-ind flg x a)
           :expand ((beta-reduce-term x)
                    (beta-reduce-list x)))
          ("Subgoal *1/6" :in-theory (enable dumb-ev-constraint-0))
          ("Subgoal *1/5" :in-theory (enable dumb-ev-al)))
  :rule-classes nil)

(defthm beta-reduce-correct-rw
  (implies (and (pseudo-termp x)
                (alistp a))
           (equal (dumb-ev (beta-reduce-term x) a)
                  (dumb-ev x a)))
  :hints (("goal" :use ((:instance beta-reduce-correct-lemma
                                   (flg t))))))

(defun beta-reduce-cp (x)
  (declare (xargs :guard (pseudo-term-listp x)))
  (let ((ans (list (beta-reduce-list (hons-copy x)))))
    (prog2$ (clear-memoize-table 'beta-reduce-term)
            ans)))
(defthm beta-reduce-cp-correct
  (implies (and (pseudo-term-listp x)
                (alistp a)
                (dumb-ev (conjoin-clauses (beta-reduce-cp x)) a))
           (dumb-ev (disjoin x) a))
  :hints (("goal" :induct (len x)))
  :rule-classes :clause-processor)

(defun reduce-trivial-equality-cp (x)
  (declare (xargs :guard t))
  (case-match x
    ((('equal a b) . &)
      (if (hons-equal a b)
          nil
        (list x)))
    (& (list x))))

(defthm reduce-trivial-equality-cp-correct
  (implies (and (pseudo-term-listp x)
                (alistp a)
                (dumb-ev (conjoin-clauses (reduce-trivial-equality-cp x)) a))
           (dumb-ev (disjoin x) a))
  :rule-classes :clause-processor)


(defun nonnil-symbol-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (symbolp (car x))
         (car x)
         (nonnil-symbol-listp (cdr x)))))

(defthm nonnil-symbol-listp-symbol-listp
  (implies (nonnil-symbol-listp x)
           (symbol-listp x)))

(defthm nonnil-symbol-listp-true-listp
  (implies (nonnil-symbol-listp x)
           (true-listp x)))

(defthm nonnil-symbol-listp-pseudo-term-listp
  (implies (nonnil-symbol-listp x)
           (pseudo-term-listp x)))

(defun rewrite-listp (rws)
  (declare (xargs :guard t))
  (or (atom rws)
      (and (consp (car rws))
           (consp (caar rws))
           (consp (cdar rws))
           (nonnil-symbol-listp (caar rws))
           (no-duplicatesp (cdaar rws))
           (not (member (caaar rws) '(quote if)))
           (pseudo-termp (cadar rws))
           (rewrite-listp (cdr rws)))))


(defun fncall-rewrite (x rws)
  (declare (xargs :guard (and (pseudo-termp x)
                              (consp x)
                              (atom (car x))
                              (rewrite-listp rws))))
  (if (atom rws)
      (mv x nil)
    (if (and (eq (car x) (caaar rws))
             (eql (length (cdr x)) (length (cdaar rws))))
        (let ((newx (term-subst (cadar rws) (pairlis$ (cdaar rws) (cdr x)))))
          (prog2$ (clear-memoize-table 'term-subst)
                  (mv newx
                      `((not (use-by-hint ',(cddar rws)))
                        (equal ,(caar rws) ,(cadar rws))))))
      (fncall-rewrite x (cdr rws)))))

(defun fncall-rewrite-alist (x rws a)
  (if (atom rws)
      nil
    (if (and (eq (car x) (caaar rws))
             (eql (length (cdr x)) (length (cdaar rws))))
        (dumb-ev-al (pairlis$ (cdaar rws) (cdr x)) a)
      (fncall-rewrite-alist x (cdr rws) a))))



(defthm pseudo-termp-fncall-rewrite
  (implies (and (rewrite-listp rws)
                (pseudo-termp x)
                (pseudo-term-listp (cdr x)))
           (pseudo-termp (mv-nth 0 (fncall-rewrite x rws)))))

(defthm pseudo-termp-fncall-rewrite1
  (implies (and (rewrite-listp rws)
                (pseudo-termp x)
                (pseudo-term-listp (cdr x)))
           (pseudo-term-listp (mv-nth 1 (fncall-rewrite x rws)))))





(defthm nonmember-ev-lst
  (implies (and (nonnil-symbol-listp y)
                (not (member z y)))
           (equal (dumb-ev-lst y
                               (cons (cons z v) al))
                  (dumb-ev-lst y al))))

(defun cdr-both (x y)
  (declare (xargs :measure (+ (len x) (len y))))
  (if (and (atom x) (atom y))
      x
    (cdr-both (cdr x) (cdr y))))

(defthm dumb-ev-lst-of-dumb-ev-al
  (implies (and (pseudo-term-listp x)
                (nonnil-symbol-listp y)
                (no-duplicatesp y)
                (equal (len x) (len y)))
           (equal (dumb-ev-lst y (dumb-ev-al (pairlis$ y x) a))
                  (dumb-ev-lst x a)))
  :hints(("Goal" :in-theory (enable dumb-ev-al)
          :induct (cdr-both x y))))



(defthm fncall-rewrite-correct
  (mv-let (newx rule)
    (fncall-rewrite x rws)
    (implies (and (consp x)
                  (symbolp (car x))
                  (rewrite-listp rws)
                  (pseudo-term-listp (cdr x))
                  (implies rule
                           (dumb-ev (disjoin rule)
                                    (fncall-rewrite-alist x rws a))))
             (equal (dumb-ev newx a)
                    (dumb-ev x a))))
  :hints (("goal" :induct (fncall-rewrite x rws)
           :expand ((fncall-rewrite x rws)
                    (fncall-rewrite-alist x rws a)
                    (rewrite-listp rws)
                    (use-by-hint (cddar rws))))
           ("Subgoal *1/2" :in-theory (enable dumb-ev-constraint-0))))

(defthm fncall-rewrite-fail
  (implies (not (mv-nth 1 (fncall-rewrite x rws)))
           (equal (mv-nth 0 (fncall-rewrite x rws)) x)))



(defun term-rw-mem-wfp (mem)
  (declare (xargs :guard t))
  (or (atom mem)
      (and (consp (car mem))
           (pseudo-termp (cdar mem))
           (term-rw-mem-wfp (cdr mem)))))

(mutual-recursion
 (defun term-rw (x rws mem used)
   (declare (xargs :guard (and (pseudo-termp x)
                               (term-rw-mem-wfp mem)
                               (rewrite-listp rws))
                   :verify-guards nil))
   (if (or (atom x) (eq (car X) 'quote))
       (mv x mem used)
     (let ((look (hons-get x mem)))
       (if look
           (mv (cdr look) mem used)
         (if (consp (car x))
             (b* (((mv args mem used) (term-rw-lst (cdr x) rws mem used))
                  (ans (hons (car x) args)))
               (mv ans (hons-acons x ans mem) used))
           (b* (((mv args mem used) (term-rw-lst (cdr x) rws mem used))
                ((mv ans rule) (fncall-rewrite (hons (car x) args) rws))
                (used (if (or (not rule) (hons-get rule used))
                          used
                        (hons-acons rule t used))))
             (mv ans (hons-acons x ans mem) used)))))))

 (defun term-rw-lst (x rws mem used)
   (declare (xargs :guard (and (pseudo-term-listp x)
                               (term-rw-mem-wfp mem)
                               (rewrite-listp rws))))
   (if (endp x)
       (mv nil mem used)
     (b* (((mv a mem used) (term-rw (car x) rws mem used))
          ((mv d mem used) (term-rw-lst (cdr x) rws mem used)))
       (mv (hons a d) mem used)))))

(flag::make-flag term-rw-ind term-rw)

(mutual-recursion
 (defun term-rw-indep-ind (x rws mem used)
   (declare (xargs :guard (and (pseudo-termp x)
                               (term-rw-mem-wfp mem)
                               (rewrite-listp rws))
                   :verify-guards nil))
   (if (or (atom x) (eq (car X) 'quote))
       (mv x mem used)
     (let ((look (hons-get x mem)))
       (if look
           (mv (cdr look) mem used)
         (if (consp (car x))
             (b* (((mv args mem used) (term-rw-lst-indep-ind (cdr x) rws mem used))
                  (ans (hons (car x) args)))
               (mv ans (hons-acons x ans mem) used))
           (b* (((mv args mem used) (term-rw-lst-indep-ind (cdr x) rws mem used))
                ((mv ans rule) (fncall-rewrite (cons (car x) args) rws))
                (used (if (hons-get rule used) used (hons-acons rule t used))))
             (mv ans (hons-acons x ans mem) used)))))))

 (defun term-rw-lst-indep-ind (x rws mem used)
   (declare (xargs :guard (and (pseudo-term-listp x)
                               (term-rw-mem-wfp mem)
                               (rewrite-listp rws))))
   (if (endp x)
       (mv nil mem used)
     (b* (((mv ?a ?mem0 used0) (term-rw (car x) rws mem used))
          ((mv ?a ?mem1 used1) (term-rw (car x) rws mem nil))
          ((mv & & &) (term-rw-indep-ind (car x) rws mem used))
          ((mv d mem used) (term-rw-lst-indep-ind (cdr x) rws mem0 used0))
          ((mv & & &) (term-rw-lst-indep-ind (cdr x) rws mem1 used1)))
       (mv (cons a d) mem used)))))

(flag::make-flag term-rw-indep-ind-flg term-rw-indep-ind)

(defthm-term-rw-indep-ind-flg term-rw-indep-of-used
  (term-rw-indep-ind
   (implies (syntaxp (not (equal used ''nil)))
            (and (equal (mv-nth 0 (term-rw x rws mem used))
                        (mv-nth 0 (term-rw x rws mem nil)))
                 (equal (mv-nth 1 (term-rw x rws mem used))
                        (mv-nth 1 (term-rw x rws mem nil))))))
  (term-rw-lst-indep-ind
   (implies (syntaxp (not (equal used ''nil)))
            (and (equal (mv-nth 0 (term-rw-lst x rws mem used))
                        (mv-nth 0 (term-rw-lst x rws mem nil)))
                 (equal (mv-nth 1 (term-rw-lst x rws mem used))
                        (mv-nth 1 (term-rw-lst x rws mem nil))))))
  :hints (("goal" :induct (term-rw-indep-ind-flg flag x rws mem used)
           :expand ((term-rw-lst x rws mem used)
                    (term-rw-lst x rws mem nil)
                    (term-rw x rws mem used)
                    (term-rw x rws mem nil))
           :in-theory (disable term-rw-lst term-rw))))


(defthm hons-assoc-equal-term-rw-mem-wfp
  (implies (and (term-rw-mem-wfp mem)
                (hons-assoc-equal x mem))
           (pseudo-termp (cdr (hons-assoc-equal x mem)))))


(defthm-term-rw-ind len-term-rw-lst1
  (term-rw t :skip t)
  (term-rw-lst
   (equal (len (mv-nth 0 (term-rw-lst x rws mem used)))
          (len x))
   :name len-term-rw-lst)
  :hints (("goal" :induct (term-rw-ind flag x rws mem used)
           :expand ((len x)
                    (term-rw-lst x rws mem used)))))

(defthm-term-rw-ind true-listp-term-rw-lst1
  (term-rw t :skip t)
  (term-rw-lst
   (true-listp (mv-nth 0 (term-rw-lst x rws mem used)))
   :name true-listp-term-rw-lst)
  :hints (("goal" :induct (term-rw-ind flag x rws mem used))))


(defthm-term-rw-ind pseudo-termp-term-rw
  (term-rw
   (implies (and (pseudo-termp x)
                 (term-rw-mem-wfp mem)
                 (rewrite-listp rws))
            (and (pseudo-termp (mv-nth 0 (term-rw x rws mem used)))
                 (term-rw-mem-wfp (mv-nth 1 (term-rw x rws mem used))))))
  (term-rw-lst
   (implies (and (pseudo-term-listp x)
                 (term-rw-mem-wfp mem)
                 (rewrite-listp rws))
            (and (pseudo-term-listp (mv-nth 0 (term-rw-lst x rws mem used)))
                 (term-rw-mem-wfp (mv-nth 1 (term-rw-lst x rws mem used))))))
  :hints (("goal" :induct (term-rw-ind flag x rws mem used))))

(defun pseudo-term-list-key-alistp (x)
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (pseudo-term-listp (caar x))
         (pseudo-term-list-key-alistp (cdr x)))))


(defthm-term-rw-ind pseudo-term-list-key-alistp-term-rw-2
  (term-rw
   (implies (and (pseudo-termp x)
                 (rewrite-listp rws)
                 (term-rw-mem-wfp mem)
                 (pseudo-term-list-key-alistp used))
            (pseudo-term-list-key-alistp (mv-nth 2 (term-rw x rws mem used)))))
  (term-rw-lst
   (implies (and (pseudo-term-listp x)
                 (rewrite-listp rws)
                 (term-rw-mem-wfp mem)
                 (pseudo-term-list-key-alistp used))
            (pseudo-term-list-key-alistp (mv-nth 2 (term-rw-lst x rws mem used)))))
  :hints (("goal" :induct (term-rw-ind flag x rws mem used))))

(verify-guards term-rw)




(defthm-term-rw-ind used-correct-implies-prev-correct1
  (term-rw
   (implies (dumb-ev (conjoin (disjoin-lst (mv-nth 2 (term-rw x rws mem used)))) a)
            (dumb-ev (conjoin (disjoin-lst used)) a)))
  (term-rw-lst
   (implies (dumb-ev (conjoin (disjoin-lst
                               (mv-nth 2 (term-rw-lst x rws mem used)))) a)
            (dumb-ev (conjoin (disjoin-lst used)) a)))
  :hints (("goal" :induct (term-rw-ind flag x rws mem used))))




(mutual-recursion
 (defun term-rw-alist (x rws mem used a)
   (cond ((or (atom x) (eq (car x) 'quote)) (mv x mem used))
         ((hons-get x mem) (mv (cdr (hons-get x mem)) mem used))
         ((consp (car x))
          (b* (((mv args mem used)
                (term-rw-alist-lst (cdr x) rws mem used a))
               (ans (cons (car x) args)))
            (mv ans (hons-acons x ans mem) used)))
         (t (b* (((mv args mem used)
                  (term-rw-alist-lst (cdr x) rws mem used a))
                 ((mv newx rule) (fncall-rewrite (cons (car x) args) rws))
                 (al (fncall-rewrite-alist (cons (car x) args) rws a))
                 (used (if rule
                           (hons-acons
                            rule (cons al (cdr (hons-get rule used))) used)
                         used)))
              (mv newx (hons-acons x newx mem) used)))))
 (defun term-rw-alist-lst (x rws mem used a)
   (if (endp x)
       (mv nil mem used)
     (b* (((mv aa mem used) (term-rw-alist (car x) rws mem used a))
          ((mv dd mem used) (term-rw-alist-lst (cdr x) rws mem used a)))
       (mv (cons aa dd) mem used)))))


(flag::make-flag term-rw-alist-ind term-rw-alist)


(mutual-recursion
 (defun term-rw-alist-indep-ind (x rws mem used a)
   (cond ((or (atom x) (eq (car x) 'quote)) (mv x mem used))
         ((hons-get x mem) (mv (cdr (hons-get x mem)) mem used))
         ((consp (car x))
          (b* (((mv args mem used)
                (term-rw-alist-lst-indep-ind (cdr x) rws mem used a))
               (ans (cons (car x) args)))
            (mv ans (hons-acons x ans mem) used)))
         (t (b* (((mv args mem used)
                  (term-rw-alist-lst-indep-ind (cdr x) rws mem used a))
                 ((mv newx rule) (fncall-rewrite (cons (car x) args) rws))
                 (al (fncall-rewrite-alist (cons (car x) args) rws a))
                 (used (hons-acons
                        rule (cons al (cdr (hons-get rule used))) used)))
              (mv newx mem used)))))
 (defun term-rw-alist-lst-indep-ind (x rws mem used a)
   (if (endp x)
       (mv nil mem used)
     (b* (((mv ?aa mem0 used0) (term-rw-alist (car x) rws mem used a))
          ((mv ?aa ?m used1)   (term-rw-alist (car x) rws mem nil a))
          ((mv ?aa ?m ?u) (term-rw-alist-indep-ind (car x) rws mem used a))
          ;; ((mv ?a ?m ?u) (term-rw-alist-indep-ind (car x) rws mem nil a))
          ((mv dd mem used) (term-rw-alist-lst-indep-ind (cdr x) rws mem0 used0 a))
          ((mv ?aa ?m ?u) (term-rw-alist-lst-indep-ind (cdr x) rws mem0 used1 a)))
       (mv (cons aa dd) mem used)))))

(flag::make-flag term-rw-alist-indep-ind-flg term-rw-alist-indep-ind)

(defthm-term-rw-alist-indep-ind-flg term-rw-alist-indep-of-used
  (term-rw-alist-indep-ind
   (implies (syntaxp (not (equal used ''nil)))
            (and (equal (mv-nth 0 (term-rw-alist x rws mem used a))
                        (mv-nth 0 (term-rw-alist x rws mem nil a)))
                 (equal (mv-nth 1 (term-rw-alist x rws mem used a))
                        (mv-nth 1 (term-rw-alist x rws mem nil a))))))
  (term-rw-alist-lst-indep-ind
   (implies (syntaxp (not (equal used ''nil)))
            (and (equal (mv-nth 0 (term-rw-alist-lst x rws mem used a))
                        (mv-nth 0 (term-rw-alist-lst x rws mem nil a)))
                 (equal (mv-nth 1 (term-rw-alist-lst x rws mem used a))
                        (mv-nth 1 (term-rw-alist-lst x rws mem nil a))))))
  :hints (("goal" :induct (term-rw-alist-indep-ind-flg flag x rws mem used a)
           :expand ((term-rw-alist-lst x rws mem used a)
                    (term-rw-alist-lst x rws mem nil a)
                    (term-rw-alist x rws mem used a)
                    (term-rw-alist x rws mem nil a))
           :in-theory (disable term-rw-alist-lst term-rw-alist))))

(defthm-term-rw-alist-ind term-rw-alist-is-term-rw
  (term-rw-alist
   (and (equal (mv-nth 0 (term-rw-alist x rws mem used a))
               (mv-nth 0 (term-rw x rws mem used)))
        (equal (mv-nth 1 (term-rw-alist x rws mem used a))
               (mv-nth 1 (term-rw x rws mem used)))))
  (term-rw-alist-lst
   (and (equal (mv-nth 0 (term-rw-alist-lst x rws mem used a))
               (mv-nth 0 (term-rw-lst x rws mem used)))
        (equal (mv-nth 1 (term-rw-alist-lst x rws mem used a))
               (mv-nth 1 (term-rw-lst x rws mem used)))))
  :hints (("goal" :induct (term-rw-alist-ind flag x rws mem used a))))

(defun used-al-to-used (x)
  (if (atom x)
      nil
    (let ((rest (used-al-to-used (cdr x))))
      (if (and (consp (car x))
               (not (hons-get (caar x) rest)))
          (hons-acons (caar x) t rest)
        rest))))

(defthm-term-rw-alist-ind used-al-to-used-term-rw
  (term-rw-alist
   (equal
    (used-al-to-used (mv-nth 2 (term-rw-alist x rws mem used-al a)))
    (mv-nth 2 (term-rw x rws mem (used-al-to-used used-al)))))
  (term-rw-alist-lst
   (equal
    (used-al-to-used (mv-nth 2 (term-rw-alist-lst x rws mem used-al a)))
    (mv-nth 2 (term-rw-lst x rws mem (used-al-to-used used-al)))))
  :hints (("goal" :induct (term-rw-alist-ind flag x rws mem used-al a))))

(defun used-and-used-al-to-alist-lists (used used-al)
  (if (atom used)
      nil
    (if (consp (car used))
        (cons (cdr (hons-get (caar used) used-al))
              (used-and-used-al-to-alist-lists (cdr used) used-al))
      (used-and-used-al-to-alist-lists (cdr used) used-al))))


(acl2::def-multi-env-fns dumb-ev dumb-ev-lst)

(defun alists-apply-alists-dumb-ev (used-al)
  (let ((used (used-al-to-used used-al)))
    (clauses-apply-alists-dumb-ev
     (alist-keys used)
     (used-and-used-al-to-alist-lists used used-al))))

(defthm clauses-apply-alists-dumb-ev-extend-al
  (implies (clauses-apply-alists-dumb-ev
            (alist-keys used)
            (used-and-used-al-to-alist-lists
             used (cons (cons cl
                              (cons al (cdr (hons-assoc-equal
                                             cl used-al))))
                        used-al)))
           (clauses-apply-alists-dumb-ev
            (alist-keys used)
            (used-and-used-al-to-alist-lists used used-al)))
  :hints(("Goal" :in-theory (enable alist-keys))))

(defthm clauses-apply-alists-dumb-ev-extend-al1
  (implies (and (not (hons-assoc-equal cl used-al))
                (clauses-apply-alists-dumb-ev
                 (alist-keys used)
                 (used-and-used-al-to-alist-lists
                  used (cons (list cl al)
                             used-al))))
           (clauses-apply-alists-dumb-ev
            (alist-keys used)
            (used-and-used-al-to-alist-lists
             used used-al)))
  :hints(("Goal" :in-theory (enable alist-keys))))

(defthm alists-apply-alists-extend-al1
  (implies (alists-apply-alists-dumb-ev
            (cons (cons cl (cons al (cdr (hons-assoc-equal cl used-al))))
                  used-al))
           (alists-apply-alists-dumb-ev used-al))
  :hints(("Goal" :in-theory (e/d (alist-keys used-al-to-used)
                                 (hons-assoc-equal)))))

(defthm alists-apply-alists-extend-special
  (implies (and (alists-apply-alists-dumb-ev
                 (cons (list cl al)
                       used-al))
                (not (hons-assoc-equal cl used-al)))
           (alists-apply-alists-dumb-ev used-al))
  :hints(("Goal" :use ((:instance alists-apply-alists-extend-al1))
          :in-theory (disable alists-apply-alists-extend-al1))))


(defthm-term-rw-alist-ind als-correct-implies-prev-correct1
  (term-rw-alist
   (b* ((used-al-out (mv-nth 2 (term-rw-alist x rws mem used-al a))))
     (implies (alists-apply-alists-dumb-ev used-al-out)
              (alists-apply-alists-dumb-ev used-al))))
  (term-rw-alist-lst
   (b* ((used-al-out (mv-nth 2 (term-rw-alist-lst x rws mem used-al a))))
     (implies (alists-apply-alists-dumb-ev used-al-out)
              (alists-apply-alists-dumb-ev used-al))))
  :hints (("goal" :induct (term-rw-alist-ind flag x rws mem used-al a)
           :in-theory (enable alist-keys))))



(defun term-rw-mem-okp (mem a)
  (or (atom mem)
      (and (equal (dumb-ev (caar mem) a)
                  (dumb-ev (cdar mem) a))
           (term-rw-mem-okp (cdr mem) a))))

(defthm term-rw-mem-okp-hons-assoc-equal
  (implies (and (term-rw-mem-okp mem a)
                (hons-assoc-equal x mem))
           (equal (dumb-ev (cdr (hons-assoc-equal x mem)) a)
                  (dumb-ev x a))))

(defthm hons-assoc-equal-used-al-to-used
  (iff (hons-assoc-equal x (used-al-to-used used))
       (hons-assoc-equal x used)))

(defthm assoc-used-al-impl-true
  (implies (and (hons-assoc-equal clause used)
                (member al (cdr (hons-assoc-equal clause used-al)))
                (clauses-apply-alists-dumb-ev
                 (alist-keys used)
                 (used-and-used-al-to-alist-lists
                  used used-al)))
           (dumb-ev (disjoin clause) al))
  :hints(("Goal" :in-theory (enable alist-keys))))


(defthm assoc-used-al-special
  (implies (and (alists-apply-alists-dumb-ev used-al)
                (member al (cdr (hons-assoc-equal clause used-al))))
           (dumb-ev (disjoin clause) al))
  :hints (("goal" :use ((:instance assoc-used-al-impl-true
                                   (used (used-al-to-used used-al)))))))

(in-theory (disable assoc-used-al-impl-true
                    term-rw-alist-lst
                    nonnil-symbol-listp rewrite-listp length
                    term-rw term-rw-alist term-rw-lst
                    fncall-rewrite fncall-rewrite-fail
                    fncall-rewrite-alist
                    default-car default-cdr term-subst
                    alists-apply-alists-dumb-ev))



(defthm-term-rw-alist-ind term-rw-correct-lemma
  (term-rw-alist
   (b* (((mv newx newmem &)
         (term-rw x rws mem (used-al-to-used used-al)))
        ((mv & & newused-al)
         (term-rw-alist x rws mem used-al a)))
     (implies (and (rewrite-listp rws)
                   (alistp a)
                   (pseudo-termp x)
                   (term-rw-mem-wfp mem)
                   (term-rw-mem-okp mem a)
                   (alists-apply-alists-dumb-ev newused-al))
              (and (term-rw-mem-okp newmem a)
                   (equal (dumb-ev newx a)
                          (dumb-ev x a)))))
   :name term-rw-correct)
  (term-rw-alist-lst
   (b* (((mv newx newmem &)
         (term-rw-lst x rws mem (used-al-to-used used-al)))
        ((mv & & newused-al)
         (term-rw-alist-lst x rws mem used-al a)))
     (implies (and (rewrite-listp rws)
                   (alistp a)
                   (pseudo-term-listp x)
                   (term-rw-mem-wfp mem)
                   (term-rw-mem-okp mem a)
                   (alists-apply-alists-dumb-ev newused-al))
              (and (term-rw-mem-okp newmem a)
                   (equal (dumb-ev-lst newx a)
                          (dumb-ev-lst x a)))))
   :name term-rw-lst-correct)
  :hints (("goal" :induct (term-rw-alist-ind flag x rws mem used-al a)
           :in-theory (e/d (conjoin-clauses)))
          (and stable-under-simplificationp
               '(:expand ((term-rw-alist-lst x rws mem used-al a)
                          (term-rw-alist x rws mem used-al a)
                          (:free (used) (term-rw x rws mem used))
                          (:free (used) (term-rw nil rws mem used))
                          (:free (used) (term-rw-lst x rws mem used))
                          (:free (used) (term-rw-lst nil rws mem used)))))
          (and stable-under-simplificationp
               '(:in-theory (e/d (conjoin-clauses dumb-ev-constraint-0))))))

(defthm term-rw-correct-rw
   (b* (((mv newx newmem &)
         (term-rw x rws mem nil))
        ((mv & & newused-al)
         (term-rw-alist x rws mem nil a)))
     (implies (and (rewrite-listp rws)
                   (alistp a)
                   (pseudo-termp x)
                   (term-rw-mem-wfp mem)
                   (term-rw-mem-okp mem a)
                   (alists-apply-alists-dumb-ev newused-al))
              (and (term-rw-mem-okp newmem a)
                   (equal (dumb-ev newx a)
                          (dumb-ev x a)))))
   :hints (("goal" :use ((:instance term-rw-correct (used-al nil)))
            :in-theory (e/d** (used-al-to-used)))))

(defthm term-rw-lst-correct-rw
   (b* (((mv newx newmem &)
         (term-rw-lst x rws mem nil))
        ((mv & & newused-al)
         (term-rw-alist-lst x rws mem nil a)))
     (implies (and (rewrite-listp rws)
                   (alistp a)
                   (pseudo-term-listp x)
                   (term-rw-mem-wfp mem)
                   (term-rw-mem-okp mem a)
                   (alists-apply-alists-dumb-ev newused-al))
              (and (term-rw-mem-okp newmem a)
                   (equal (dumb-ev-lst newx a)
                          (dumb-ev-lst x a)))))
   :hints (("goal" :use ((:instance term-rw-lst-correct (used-al nil)))
            :in-theory (e/d** (used-al-to-used)))))



(defthm fncall-rewrite-if
  (implies (rewrite-listp rws)
           (equal (fncall-rewrite (cons 'if args) rws)
                  (mv (cons 'if args) nil)))
  :hints(("Goal" :in-theory (enable fncall-rewrite
                                    rewrite-listp))))

(defthm consp-term-rw-lst1
  (equal (consp (mv-nth 0 (term-rw-lst x rw mem used)))
         (consp x))
  :hints (("goal" :induct (len x)
           :expand (term-rw-lst x rw mem used))))

(defun rw-cp (clause rws)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (if (rewrite-listp rws)
      (mv-let (newclause mem used)
        (term-rw-lst (hons-copy clause) rws nil nil)
        (prog2$ (flush-hons-get-hash-table-link used)
                (prog2$ (flush-hons-get-hash-table-link mem)
                        (cons newclause (alist-keys used)))))
    (list clause)))

(defun rw-cp-alists (clause rws a)
  (if (rewrite-listp rws)
      (mv-let (newclause mem used)
        (term-rw-alist-lst clause rws nil nil a)
        (declare (ignore newclause mem))
        (cons (list a) (used-and-used-al-to-alist-lists
                        (used-al-to-used used)
                        used)))
    (list (list a))))

(defthm car-rw-cp-alists
  (equal (car (rw-cp-alists clause rws a))
         (list a))
  :hints(("Goal" :in-theory (enable rw-cp-alists))))

(defthm consp-rw-cp-and-rw-cp-alists
  (and (consp (rw-cp clause rws))
       (consp (rw-cp-alists clause rws a))))

(defthm rw-cp-correct1
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (clauses-apply-alists-dumb-ev
                 (cdr (rw-cp clause rws))
                 (cdr (rw-cp-alists clause rws a))))
           (equal (dumb-ev-lst (car (rw-cp clause rws)) a)
                  (dumb-ev-lst clause a)))
  :hints (("goal" :use ((:instance term-rw-lst-correct-rw
                                   (x clause)
                                   (mem nil)))
           :in-theory (e/d** (alists-apply-alists-dumb-ev
                              rw-cp rw-cp-alists hons-copy
                              car-cons cdr-cons
                              term-rw-mem-okp
                              used-al-to-used
                              used-al-to-used-term-rw-term-rw-alist-lst
                              term-rw-mem-wfp)))))


(local (defun or-list (x)
         (if (atom x)
             nil
           (or (car x) (or-list (cdr x))))))

(local (defthm dumb-ev-of-disjoin
         (iff (dumb-ev (disjoin x) a)
              (or-list (dumb-ev-lst x a)))
         :hints(("Goal" :induct (len x)))))

(in-theory (Disable rw-cp rw-cp-alists))

(acl2::prove-multi-env-clause-proc
 rw-cp-correct
 :ev dumb-ev
 :evlst dumb-ev-lst
 :clauseproc rw-cp
 :alists (rw-cp-alists clause rws a)
 :alist-name a
 :hints ((and stable-under-simplificationp
              '(:expand ((CLAUSES-APPLY-ALISTS-DUMB-EV
                          (RW-CP CLAUSE RWS)
                          (RW-CP-ALISTS CLAUSE RWS A)))))))



(defun remove-first-hyp-cp (clause)
  (if (consp clause)
      (list (cdr clause))
    (list clause)))

(defthm remove-first-hyp-cp-correct
  (implies (and (pseudo-term-listp x)
                (alistp a)
                (dumb-ev (conjoin-clauses (remove-first-hyp-cp x))
                         a))
           (dumb-ev (disjoin x) a))
  :rule-classes :clause-processor)


(defun rw-from-name (name world)
  (declare (xargs :mode :program))
  (let ((eq (if (atom name)
                (let ((body (fgetprop name 'unnormalized-body nil world)))
                  (if body
                      `(equal (,name . ,(fgetprop name 'formals nil world))
                              ,body)
                    (fgetprop name 'theorem nil world)))
              (acl2::corollary name world))))
    (and (eq (car eq) 'equal)
         (list* (cadr eq)
                (caddr eq)
                name))))




(defun rws-from-ruleset-fn (runes world)
  (declare (xargs :mode :program))
  (if (atom runes)
      nil
    (let ((rw (rw-from-name (car runes) world)))
      (if rw
          (cons rw (rws-from-ruleset-fn (cdr runes) world))
        (rws-from-ruleset-fn (cdr runes) world)))))

(defmacro rws-from-ruleset (ruleset)
  `(let ((world (w state)))
     (rws-from-ruleset-fn
      (strip-cdrs (acl2::augment-theory (ruleset-theory ',ruleset) world))
      world)))

