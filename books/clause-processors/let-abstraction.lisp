; Clause processor that does let/let*-abstraction

; Copyright (C) 2013 Centaur Technology
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

(include-book "generalize")
(include-book "std/util/bstar" :dir :system)
(include-book "centaur/misc/equal-sets" :dir :system)

(local (in-theory (disable mv-nth)))

(defevaluator abs-ev abs-ev-lst ((if a b c) (not a) (equal a b)))

(def-join-thms abs-ev)

(local (in-theory (enable simple-term-vars simple-term-vars-lst)))


(mutual-recursion
 (defun let-abstract-term-rec (x subterms bindings)
   (declare (xargs :guard (and (pseudo-termp x)
                               (alistp subterms)
                               (symbol-listp (strip-cdrs subterms))
                               (symbol-alistp bindings))
                   :verify-guards nil))
   (b* (((when (variablep x)) (mv bindings x))
        (look (assoc-equal x subterms))
        ((when (and (consp look)
                    (consp (assoc (cdr look) bindings))))
         (mv bindings (cdr look)))
        ((when (fquotep x))
         (if (consp look)
             (mv (cons (cons (cdr look) x) bindings)
                 (cdr look))
           (mv bindings x)))
        ((mv bindings args) (let-abstract-list-rec (fargs x) subterms bindings))
        ((when (consp look))
         (mv (cons (cons (cdr look) (cons (ffn-symb x) args))
                   bindings)
             (cdr look))))
     (mv bindings (cons (ffn-symb x) args))))

 (defun let-abstract-list-rec (x subterms bindings)
   (declare (xargs :guard (and (pseudo-term-listp x)
                               (alistp subterms)
                               (symbol-listp (strip-cdrs subterms))
                               (symbol-alistp bindings))))
   (b* (((when (endp x)) (mv bindings nil))
        ((mv bindings first) (let-abstract-term-rec (car x) subterms bindings))
        ((mv bindings rest) (let-abstract-list-rec (cdr x) subterms bindings)))
     (mv bindings (cons first rest)))))

(flag::make-flag let-abstract-flg let-abstract-term-rec
                 :flag-mapping ((let-abstract-term-rec term)
                                (let-abstract-list-rec list)))


(defthm cdr-assoc-when-symbol-listp-cdrs
  (implies (symbol-listp (strip-cdrs bindings))
           (symbolp (cdr (assoc key bindings)))))

(defthm-let-abstract-flg
  (defthm let-abstract-term-bindings-symbol-alistp
    (implies (and (symbol-alistp bindings)
                  (symbol-listp (strip-cdrs subterms)))
             (symbol-alistp (mv-nth 0 (let-abstract-term-rec x subterms bindings))))
    :flag term)
  (defthm let-abstract-list-bindings-symbol-alistp
    (implies (and (symbol-alistp bindings)
                  (symbol-listp (strip-cdrs subterms)))
             (symbol-alistp (mv-nth 0 (let-abstract-list-rec x subterms bindings))))
    :flag list))

(verify-guards let-abstract-term-rec)

(defun var-ordered-bindingsp (bindings)
  (if (atom bindings)
      t
    (and (not (member (caar bindings)
                      (simple-term-vars-lst (strip-cdrs bindings))))
         (var-ordered-bindingsp (cdr bindings)))))

(defun eval-bindings (bindings a)
  (if (atom bindings)
      a
    (let ((rest (eval-bindings (cdr bindings) a)))
      (cons (cons (caar bindings)
                  (abs-ev (cdar bindings) rest))
            rest))))

(defthm intersectp-set-difference-remove-more
  (implies (not (intersectp a (set-difference$ b c)))
           (not (intersectp a (set-difference$ b (cons d c)))))
  :hints ((set-reasoning)))

(defthm intersectp-set-difference-remove-superset
  (implies (and (not (intersectp a (set-difference$ b c)))
                (subsetp c d))
           (not (intersectp a (set-difference$ b d))))
  :hints ((set-reasoning)))

(defthm intersectp-set-difference-when-not-intersectp
  (implies (not (intersectp a b))
           (not (intersectp a (set-difference$ b c))))
  :hints ((set-reasoning)))


(defthm set-difference-of-append
  (equal (set-difference-eq (append a b) c)
         (append (set-difference-eq a c)
                 (set-difference-eq b c)))
  :hints(("Goal" :in-theory (enable set-difference-equal))))

(defthm set-difference-nil
  (equal (set-difference$ nil x) nil)
  :hints(("Goal" :in-theory (enable set-difference$))))

(defthm-let-abstract-flg
  (defthm subsetp-old-bindings-of-let-abstract-term-rec
    (subsetp (strip-cars bindings)
             (strip-cars (mv-nth 0 (let-abstract-term-rec
                                    x subterms bindings))))
    :flag term)
  (defthm subsetp-old-bindings-of-let-abstract-list-rec
    (subsetp (strip-cars bindings)
             (strip-cars (mv-nth 0 (let-abstract-list-rec
                                    x subterms bindings))))
    :flag list))

(defthm simple-term-vars-of-fcons
  (implies (not (eq f 'quote))
           (equal (simple-term-vars (cons f args))
                  (simple-term-vars-lst args)))
  :hints(("Goal" :in-theory (enable simple-term-vars))))

(defthm cdr-assoc-member-strip-cdrs
  (implies (consp (assoc k x))
           (member (cdr (assoc k x)) (strip-cdrs x))))

(encapsulate nil
  (local
   (progn
     (defthm cdr-assocs-equal-when-no-duplicate-vals
       (implies (and (no-duplicatesp (strip-cdrs a))
                     (consp (assoc x a))
                     (consp (assoc y a)))
                (equal (equal (cdr (assoc x a)) (cdr (assoc y a)))
                       (equal x y))))

     (defthm-let-abstract-flg
       (defthm bigger-term-variable-not-bound-in-let-abstract-term-rec
         (implies (and (no-duplicatesp (strip-cdrs subterms))
                       (consp (assoc bigx subterms))
                       (not (consp (assoc (cdr (assoc bigx subterms)) bindings)))
                       (< (acl2-count x) (acl2-count bigx)))
                  (not (consp (assoc (cdr (assoc bigx subterms))
                                     (mv-nth 0 (let-abstract-term-rec
                                                x subterms bindings))))))
         :flag term)
       (defthm bigger-term-variable-not-bound-in-let-abstract-list-rec
         (implies (and (no-duplicatesp (strip-cdrs subterms))
                       (consp (assoc bigx subterms))
                       (not (consp (assoc (cdr (assoc bigx subterms)) bindings)))
                       (< (acl2-count x) (acl2-count bigx)))
                  (not (consp (assoc (cdr (assoc bigx subterms))
                                     (mv-nth 0 (let-abstract-list-rec
                                                x subterms bindings))))))
         :flag list))))

  (defthm subterm-var-not-bound-of-let-abstract-term
    (implies (and (no-duplicatesp (strip-cdrs subterms))
                  (consp (assoc x subterms))
                  (not (consp (assoc (cdr (assoc x subterms)) bindings))))
             (not (consp (assoc (cdr (assoc x subterms))
                                (mv-nth 0 (let-abstract-list-rec
                                           (cdr x) subterms bindings))))))))

(local (defthmd member-strip-cars-assoc
         (implies (alistp c)
                  (iff (member x (strip-cars c))
                       (consp (assoc x c))))))



(encapsulate nil
  (local (in-theory (enable member-strip-cars-assoc)))
  (local (defthm not-member-val-lemma1
           (implies (and (consp (assoc x a))
                         (alistp c)
                         (not (intersectp-equal
                               (strip-cdrs a) (set-difference$ b (strip-cars c))))
                         (not (consp (assoc (cdr (assoc x a)) c))))
                    (not (member-equal
                          (cdr (assoc x a))
                          b)))))

  (local (defthm simple-term-vars-of-symbol
           (implies (symbolp x)
                    (equal (simple-term-vars x)
                           (and x (list x))))))

  (defthm-let-abstract-flg
    (defthm var-ordered-bindings-of-let-abstract-term-rec
      (implies (and (no-duplicatesp (strip-cdrs subterms))
                    (symbol-listp (strip-cdrs subterms))
                    (not (intersectp (strip-cdrs subterms) (simple-term-vars x)))
                    (not (intersectp (simple-term-vars-lst (strip-cars subterms))
                                     (strip-cdrs subterms)))
                    (alistp bindings)
                    (no-duplicatesp (strip-cars bindings))
                    (not (intersectp (set-difference-eq (simple-term-vars-lst (strip-cdrs bindings))
                                                        (strip-cars bindings))
                                     (strip-cdrs subterms)))
                    (subsetp (strip-cars bindings) (strip-cdrs subterms))
                    (var-ordered-bindingsp bindings))
               (b* (((mv bindings newx)
                     (let-abstract-term-rec x subterms bindings)))
                 (and (alistp bindings)
                      (not (intersectp (set-difference-eq (simple-term-vars-lst (strip-cdrs bindings))
                                                          (strip-cars bindings))
                                       (strip-cdrs subterms)))
                      (subsetp (strip-cars bindings) (strip-cdrs subterms))
                      (var-ordered-bindingsp bindings)
                      (no-duplicatesp (strip-cars bindings))
                      (not (intersectp (set-difference-eq (simple-term-vars newx)
                                                          (strip-cars bindings))
                                       (strip-cdrs subterms))))))
      :hints ((and stable-under-simplificationp
                   '(:expand ((:free (a b c) (set-difference-equal (cons a b) c))))))
      :flag term)
    (defthm var-ordered-bindings-of-let-abstract-list-rec
      (implies (and (no-duplicatesp (strip-cdrs subterms))
                    (symbol-listp (strip-cdrs subterms))
                    (not (intersectp (strip-cdrs subterms) (simple-term-vars-lst x)))
                    (not (intersectp (simple-term-vars-lst (strip-cars subterms))
                                     (strip-cdrs subterms)))
                    (alistp bindings)
                    (no-duplicatesp (strip-cars bindings))
                    (not (intersectp (set-difference-eq (simple-term-vars-lst (strip-cdrs bindings))
                                                        (strip-cars bindings))
                                     (strip-cdrs subterms)))
                    (subsetp (strip-cars bindings) (strip-cdrs subterms))
                    (var-ordered-bindingsp bindings))
               (b* (((mv bindings newx)
                     (let-abstract-list-rec x subterms bindings)))
                 (and (alistp bindings)
                      (not (intersectp (set-difference-eq (simple-term-vars-lst (strip-cdrs bindings))
                                                          (strip-cars bindings))
                                       (strip-cdrs subterms)))
                      (subsetp (strip-cars bindings) (strip-cdrs subterms))
                      (var-ordered-bindingsp bindings)
                      (no-duplicatesp (strip-cars bindings))
                      (not (intersectp (set-difference-eq (simple-term-vars-lst newx)
                                                          (strip-cars bindings))
                                       (strip-cdrs subterms))))))
      :flag list)))

(defthm-let-abstract-flg
  (defthm bindings-preserved-by-let-abstract-term-rec
    (implies (consp (assoc k bindings))
             (equal (assoc k (mv-nth 0 (let-abstract-term-rec x subterms
                                                              bindings)))
                    (assoc k bindings)))
    :flag term)
  (defthm bindings-preserved-by-let-abstract-list-rec
    (implies (consp (assoc k bindings))
             (equal (assoc k (mv-nth 0 (let-abstract-list-rec x subterms bindings)))
                    (assoc k bindings)))
    :flag list))

(defthm-let-abstract-flg
  (defthm eval-bindings-preserved-by-let-abstract-term-rec
    (implies (consp (assoc k bindings))
             (equal (assoc k (eval-bindings
                              (mv-nth 0 (let-abstract-term-rec x subterms
                                                               bindings))
                              a))
                    (assoc k (eval-bindings bindings a))))
    :flag term)
  (defthm eval-bindings-preserved-by-let-abstract-list-rec
    (implies (consp (assoc k bindings))
             (equal (assoc k (eval-bindings (mv-nth 0 (let-abstract-list-rec x
                                                                             subterms
                                                                             bindings))
                                            a))
                    (assoc k (eval-bindings bindings a))))
    :flag list))

(encapsulate nil
  (local (defthm pseudo-termp-subterm-lookup-when-symbol-vals
           (implies (symbol-listp (strip-cdrs subterms))
                    (pseudo-termp (cdr (assoc x subterms))))))

  (defthm-let-abstract-flg
    (defthm len-of-let-abstract-list-rec
      (equal (len (mv-nth 1 (let-abstract-list-rec x subterms bindings)))
             (len x))
      :flag list)
    :skip-others t)

  (defthm-let-abstract-flg
    (defthm true-listp-of-let-abstract-list-rec
      (true-listp (mv-nth 1 (let-abstract-list-rec x subterms bindings)))
      :rule-classes (:rewrite :type-prescription)
      :flag list)
    :skip-others t)

  (defthm-let-abstract-flg
    (defthm pseudo-termp-of-let-abstract-term-rec
      (implies (and (symbol-listp (strip-cdrs subterms))
                    (pseudo-termp x))
               (pseudo-termp (mv-nth 1 (let-abstract-term-rec x subterms
                                                              bindings))))
      :flag term)
    (defthm pseudo-term-listp-of-let-abstract-list-rec
      (implies (and (symbol-listp (strip-cdrs subterms))
                    (pseudo-term-listp x))
               (pseudo-term-listp (mv-nth 1 (let-abstract-list-rec x subterms
                                                                   bindings))))
      :flag list))



  (defthm-let-abstract-flg
    (defthm pseudo-termp-binding-vals-of-let-abstract-term-rec
      (implies (and (symbol-listp (strip-cdrs subterms))
                    (pseudo-termp x)
                    (pseudo-term-listp (strip-cdrs bindings)))
               (pseudo-term-listp
                (strip-cdrs (mv-nth 0 (let-abstract-term-rec x subterms
                                                             bindings)))))
      :hints ((and stable-under-simplificationp
                   '(:expand ((pseudo-termp x)))))
      :flag term)
    (defthm pseudo-term-listp-binding-vals-of-let-abstract-list-rec
      (implies (and (symbol-listp (strip-cdrs subterms))
                    (pseudo-term-listp x)
                    (pseudo-term-listp (strip-cdrs bindings)))
               (pseudo-term-listp
                (strip-cdrs (mv-nth 0 (let-abstract-list-rec x subterms
                                                             bindings)))))
      :flag list)))



(encapsulate nil
  (defund subterms/bindings-ok (subterms bindings)
    (and (alistp subterms)
         (pseudo-term-listp (strip-cars subterms))
         (symbol-listp (strip-cdrs subterms))
         (not (member nil (strip-cdrs subterms)))
         (no-duplicatesp (strip-cdrs subterms))
         (not (intersectp (simple-term-vars-lst (strip-cars subterms))
                          (strip-cdrs subterms)))
         (symbol-alistp bindings)
         (pseudo-term-listp (strip-cdrs bindings))
         (not (intersectp (set-difference-eq (simple-term-vars-lst (strip-cdrs bindings))
                                             (strip-cars bindings))
                          (strip-cdrs subterms)))
         (no-duplicatesp (strip-cars bindings))
         (subsetp (strip-cars bindings) (strip-cdrs subterms))
         (var-ordered-bindingsp bindings)))

  (local (defthmd pseudo-termp-subterm-lookup-when-symbol-vals
           (implies (symbol-listp (strip-cdrs subterms))
                    (pseudo-termp (cdr (assoc x subterms))))))

  (local (defthm pseudo-termp-subterm-lookup-when-subterms/bindings
           (implies (subterms/bindings-ok subterms bindings)
                    (pseudo-termp (cdr (assoc x subterms))))
           :hints(("Goal" :in-theory (enable subterms/bindings-ok
                                             pseudo-termp-subterm-lookup-when-symbol-vals)))))

  (local (in-theory (enable subterms/bindings-ok)))

  (defthm pseudo-termp-of-let-abstract-term-rec-subterms/bindings-ok
    (implies (and (subterms/bindings-ok subterms bindings)
                  (pseudo-termp x))
             (pseudo-termp (mv-nth 1 (let-abstract-term-rec x subterms
                                                            bindings)))))
  (defthm pseudo-term-listp-of-let-abstract-list-rec-subterms/bindings-ok
    (implies (and (subterms/bindings-ok subterms bindings)
                  (pseudo-term-listp x))
             (pseudo-term-listp (mv-nth 1 (let-abstract-list-rec x subterms
                                                                 bindings)))))

  (defthm subterms-bindings-ok-of-let-abstract-term-rec
    (implies (and (not (intersectp (strip-cdrs subterms) (simple-term-vars x)))
                  (subterms/bindings-ok subterms bindings)
                  (pseudo-termp x))
             (b* (((mv bindings newx)
                   (let-abstract-term-rec x subterms bindings)))
               (and (subterms/bindings-ok subterms bindings)
                    (not (intersectp (set-difference-eq (simple-term-vars newx)
                                                        (strip-cars bindings))
                                     (strip-cdrs subterms)))))))

  (defthm subterms-bindings-ok-of-let-abstract-list-rec
    (implies (and (not (intersectp (strip-cdrs subterms) (simple-term-vars-lst x)))
                  (subterms/bindings-ok subterms bindings)
                  (pseudo-term-listp x))
             (b* (((mv bindings newx)
                   (let-abstract-list-rec x subterms bindings)))
               (and (subterms/bindings-ok subterms bindings)
                    (not (intersectp (set-difference-eq (simple-term-vars-lst newx)
                                                        (strip-cars bindings))
                                     (strip-cdrs subterms)))))))

  (defthm subterms-bindings-ok-of-let-abstract-term-rec-expand
    (implies (and (not (intersectp (strip-cdrs subterms) (simple-term-vars x)))
                  (subterms/bindings-ok subterms bindings)
                  (pseudo-termp x))
             (b* (((mv bindings ?newx)
                   (let-abstract-term-rec x subterms bindings)))
               (and (symbol-alistp bindings)
                    (pseudo-term-listp (strip-cdrs bindings))
                    (not (intersectp (set-difference-eq (simple-term-vars-lst (strip-cdrs bindings))
                                                        (strip-cars bindings))
                                     (strip-cdrs subterms)))
                    (no-duplicatesp (strip-cars bindings))
                    (subsetp (strip-cars bindings) (strip-cdrs subterms))
                    (var-ordered-bindingsp bindings)))))

  (defthm subterms-bindings-ok-of-let-abstract-list-rec-expand
    (implies (and (not (intersectp (strip-cdrs subterms) (simple-term-vars-lst x)))
                  (subterms/bindings-ok subterms bindings)
                  (pseudo-term-listp x))
             (b* (((mv bindings ?newx)
                   (let-abstract-list-rec x subterms bindings)))
               (and (symbol-alistp bindings)
                    (pseudo-term-listp (strip-cdrs bindings))
                    (not (intersectp (set-difference-eq (simple-term-vars-lst (strip-cdrs bindings))
                                                        (strip-cars bindings))
                                     (strip-cdrs subterms)))
                    (no-duplicatesp (strip-cars bindings))
                    (subsetp (strip-cars bindings) (strip-cdrs subterms))
                    (var-ordered-bindingsp bindings))))))




(encapsulate nil
  (local (in-theory (enable member-strip-cars-assoc)))
  (local (defthm lemma
           (implies (and (consp (assoc-equal k subterms))
                         (subterms/bindings-ok subterms bindings)
                         (not (consp (assoc (CDR (ASSOC-EQUAL K SUBTERMS)) bindings))))
                    (INTERSECTP-EQUAL
                     (STRIP-CDRS SUBTERMS)
                     (SET-DIFFERENCE-EQUAL (LIST (CDR (ASSOC-EQUAL K SUBTERMS)))
                                           (STRIP-CARS BINDINGS))))
           :hints(("Goal" :in-theory (enable set-difference-equal subterms/bindings-ok)))))

  (defthm-simple-term-vars-flag
    (defthm eval-of-add-irrelevant-binding
      (implies (and (not (intersectp-equal (strip-cdrs subterms)
                                           (set-difference-eq (simple-term-vars x)
                                                              (strip-cars
                                                               bindings))))
                    (consp (assoc-equal k subterms))
                    (not (consp (assoc (cdr (assoc-equal k subterms)) bindings)))
                    (subterms/bindings-ok subterms bindings)
                    (pseudo-termp x))
               (equal (abs-ev x (cons (cons (cdr (assoc-equal k subterms))
                                            val)
                                      (eval-bindings bindings a)))
                      (abs-ev x (eval-bindings bindings a))))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable abs-ev-constraint-0))))
      :flag simple-term-vars)
    (defthm eval-of-add-irrelevant-binding-list
      (implies (and (not (intersectp-equal (strip-cdrs subterms)
                                           (set-difference-eq (simple-term-vars-lst x)
                                                              (strip-cars
                                                               bindings))))
                    (consp (assoc-equal k subterms))
                    (not (consp (assoc (cdr (assoc-equal k subterms)) bindings)))
                    (subterms/bindings-ok subterms bindings)
                    (pseudo-term-listp x))
               (equal (abs-ev-lst x (cons (cons (cdr (assoc-equal k subterms))
                                                val)
                                          (eval-bindings bindings a)))
                      (abs-ev-lst x (eval-bindings bindings a))))
      :flag simple-term-vars-lst)))

(defthm-let-abstract-flg
  (defthm eval-of-let-abstract-term-rec-var-property-preserved
    (implies (and (not (intersectp (strip-cdrs subterms) (simple-term-vars x)))
                  (subterms/bindings-ok subterms bindings)
                  (not (intersectp (set-difference-eq (simple-term-vars y)
                                                      (strip-cars bindings))
                                   (strip-cdrs subterms))))
             (b* (((mv new-bindings ?newx)
                   (let-abstract-term-rec x subterms bindings)))
               (not (intersectp (set-difference-eq (simple-term-vars y)
                                                   (strip-cars new-bindings))
                                (strip-cdrs subterms)))))
    :flag term)
  (defthm eval-of-let-abstract-list-rec-var-property-preserved
    (implies (and (not (intersectp (strip-cdrs subterms) (simple-term-vars-lst x)))
                  (subterms/bindings-ok subterms bindings)
                  (not (intersectp (set-difference-eq (simple-term-vars y)
                                                      (strip-cars bindings))
                                   (strip-cdrs subterms))))
             (b* (((mv new-bindings ?newx)
                   (let-abstract-list-rec x subterms bindings)))
               (not (intersectp (set-difference-eq (simple-term-vars y)
                                                   (strip-cars new-bindings))
                                (strip-cdrs subterms)))))
    :flag list))


(encapsulate nil
  (local (Defthm no-duplicate-subterm-vars-when-subterms/bindings-ok
           (implies (subterms/bindings-ok subterms bindings)
                    (no-duplicatesp (strip-cdrs subterms)))
           :hints(("Goal" :in-theory (enable subterms/bindings-ok)))))


  (defthm-let-abstract-flg
    (defthm eval-of-let-abstract-term-rec-preserved
      (implies (and (not (intersectp (strip-cdrs subterms) (simple-term-vars x)))
                    (subterms/bindings-ok subterms bindings)
                    (not (intersectp (set-difference-eq (simple-term-vars y)
                                                        (strip-cars bindings))
                                     (strip-cdrs subterms)))
                    (pseudo-termp y)
                    (pseudo-termp x))
               (b* (((mv new-bindings ?newx)
                     (let-abstract-term-rec x subterms bindings)))
                 (equal (abs-ev y (eval-bindings new-bindings a))
                        (abs-ev y (eval-bindings bindings a)))))
      :hints ('(:expand ((let-abstract-term-rec x subterms bindings))))
      :flag term)
    (defthm eval-of-let-abstract-list-rec-preserved
      (implies (and (not (intersectp (strip-cdrs subterms) (simple-term-vars-lst x)))
                    (subterms/bindings-ok subterms bindings)
                    (not (intersectp (set-difference-eq (simple-term-vars y)
                                                        (strip-cars bindings))
                                     (strip-cdrs subterms)))
                    (pseudo-termp y)
                    (pseudo-term-listp x))
               (b* (((mv new-bindings ?newx)
                     (let-abstract-list-rec x subterms bindings)))
                 (equal (abs-ev y (eval-bindings new-bindings a))
                        (abs-ev y (eval-bindings bindings a)))))
      :hints ('(:expand ((let-abstract-list-rec x subterms bindings))))
      :flag list)))

;; (encapsulate nil
;;   (local (defthmd pseudo-termp-subterm-lookup-when-symbol-vals
;;            (implies (symbol-listp (strip-cdrs subterms))
;;                     (pseudo-termp (cdr (assoc x subterms))))))

;;   (local (defthm pseudo-termp-subterm-lookup-when-subterms/bindings
;;            (implies (subterms/bindings-ok subterms bindings)
;;                     (pseudo-termp (cdr (assoc x subterms))))
;;            :hints(("Goal" :in-theory (enable subterms/bindings-ok
;;                                              pseudo-termp-subterm-lookup-when-symbol-vals)))))

;;   (defthm-let-abstract-flg
;;     (defthm len-of-let-abstract-list-rec
;;       (equal (len (mv-nth 1 (let-abstract-list-rec x subterms bindings)))
;;              (len x))
;;       :flag list)
;;     :skip-others t)

;;   (defthm-let-abstract-flg
;;     (defthm pseudo-termp-of-let-abstract-term-rec
;;       (implies (and (subterms/bindings-ok subterms bindings)
;;                     (not (intersectp (strip-cdrs subterms) (simple-term-vars x)))
;;                     (pseudo-termp x))
;;                (pseudo-termp (mv-nth 1 (let-abstract-term-rec x subterms
;;                                                               bindings))))
;;       :flag term)
;;     (defthm pseudo-term-listp-of-let-abstract-list-rec
;;       (implies (and (subterms/bindings-ok subterms bindings)
;;                     (not (intersectp (strip-cdrs subterms) (simple-term-vars-lst x)))
;;                     (pseudo-term-listp x))
;;                (pseudo-term-listp (mv-nth 1 (let-abstract-list-rec x subterms
;;                                                                    bindings))))
;;       :flag list)))


(encapsulate nil
  (defthmd eval-bindings-when-variable-1
    (IMPLIES (AND (symbolp x)
                  (alistp bindings)
                  (not (member x (strip-cars bindings))))
             (EQUAL (assoc x (eval-bindings bindings a))
                    (assoc x a))))

  (defthm eval-bindings-when-variable
    (IMPLIES (AND (symbolp x)
                  (not (member x (strip-cdrs subterms)))
                  (SUBTERMS/BINDINGS-OK SUBTERMS BINDINGS))
             (EQUAL (assoc x (eval-bindings bindings a))
                    (assoc x a)))
    :hints(("Goal" :in-theory (enable subterms/bindings-ok)
            :use eval-bindings-when-variable-1
            :do-not-induct t)
           (set-reasoning))))

(encapsulate nil
  (local (defthmd symbolp-subterm-lookup-when-symbol-vals
           (implies (symbol-listp (strip-cdrs subterms))
                    (symbolp (cdr (assoc x subterms))))))

  (local (defthm symbolp-subterm-lookup-when-subterms/bindings
           (implies (subterms/bindings-ok subterms bindings)
                    (symbolp (cdr (assoc x subterms))))
           :hints(("Goal" :in-theory (enable subterms/bindings-ok
                                             symbolp-subterm-lookup-when-symbol-vals)))))

  (local (defthmd cdr-assoc-when-consp-assoc
           (implies (and (not (member nil (strip-cdrs subterms)))
                         (consp (assoc x subterms)))
                    (cdr (assoc x subterms)))))

  (local (defthm cdr-assoc-when-consp-assoc-when-subterms/bindings
           (implies (and (subterms/bindings-ok subterms bindings)
                         (consp (assoc x subterms)))
                    (cdr (assoc x subterms)))
           :hints(("Goal" :in-theory (enable subterms/bindings-ok
                                             cdr-assoc-when-consp-assoc)))))

  (defun-sk bindings-correct (subterms bindings a)
    (forall (x)
            (implies (and (consp (assoc x subterms))
                          (consp (assoc (cdr (assoc x subterms)) bindings)))
                     (equal (cdr (assoc (cdr (assoc x subterms))
                                        (eval-bindings bindings a)))
                            (abs-ev x a))))
    :rewrite :direct)

  (in-theory (disable bindings-correct))
  (local (defthm cdr-assocs-equal-when-no-duplicate-vals
           (implies (and (no-duplicatesp (strip-cdrs a))
                         (consp (assoc x a))
                         (consp (assoc y a)))
                    (equal (equal (cdr (assoc x a)) (cdr (assoc y a)))
                           (equal x y)))))

  (defthmd bindings-correct-of-cons
    (implies (and (bindings-correct subterms bindings a)
                  (no-duplicatesp (strip-cdrs subterms))
                  (consp (assoc x subterms))
                  (equal (abs-ev val (eval-bindings bindings a))
                         (abs-ev x a)))
             (bindings-correct subterms (cons (cons (cdr (assoc x subterms))
                                                    val)
                                              bindings)
                               a))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :do-not-induct t))))

  (defthm bindings-correct-of-cons-when-subterms/bindings-ok
    (implies (and (bindings-correct subterms bindings a)
                  (subterms/bindings-ok subterms bindings)
                  (consp (assoc x subterms))
                  (equal (abs-ev val (eval-bindings bindings a))
                         (abs-ev x a)))
             (bindings-correct subterms (cons (cons (cdr (assoc x subterms))
                                                    val)
                                              bindings)
                               a))
    :hints(("Goal" :in-theory (enable subterms/bindings-ok
                                      bindings-correct-of-cons))))

  (defthm-let-abstract-flg
    (defthm eval-of-let-abstract-term-rec
      (implies (and (not (intersectp (strip-cdrs subterms) (simple-term-vars x)))
                    (subterms/bindings-ok subterms bindings)
                    (bindings-correct subterms bindings a)
                    (pseudo-termp x))
               (b* (((mv bindings newx)
                     (let-abstract-term-rec x subterms bindings)))
                 (and (equal (abs-ev newx (eval-bindings bindings a))
                             (abs-ev x a))
                      (bindings-correct subterms bindings a))))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable abs-ev-constraint-0))))
      :flag term)
    (defthm eval-of-let-abstract-list-rec
      (implies (and (not (intersectp (strip-cdrs subterms) (simple-term-vars-lst x)))
                    (subterms/bindings-ok subterms bindings)
                    (bindings-correct subterms bindings a)
                    (pseudo-term-listp x))
               (b* (((mv bindings newx)
                     (let-abstract-list-rec x subterms bindings)))
                 (and (equal (abs-ev-lst newx (eval-bindings bindings a))
                             (abs-ev-lst x a))
                    (bindings-correct subterms bindings a))))
      :flag list)))

(defsection check-subterm-alist
  (defund check-subterm-alist (subterms)
    (declare (xargs :guard t))
    (and (alistp subterms)
         (pseudo-term-listp (strip-cars subterms))
         (SYMBOL-LISTP (STRIP-CDRS SUBTERMS))
         (NOT (MEMBER NIL (STRIP-CDRS SUBTERMS)))
         (NO-DUPLICATESP (STRIP-CDRS SUBTERMS))
         (NOT (INTERSECTP (SIMPLE-TERM-VARS-LST (STRIP-CARS SUBTERMS))
                          (STRIP-CDRS SUBTERMS)))))

  (defthm invariants-ok-start-when-check-subterm-alist
    (implies (check-subterm-alist subterms)
             (and (subterms/bindings-ok subterms nil)
                  (bindings-correct subterms nil a)))
    :hints(("Goal" :in-theory (enable bindings-correct
                                      subterms/bindings-ok
                                      check-subterm-alist)))))


(local
 (progn
   (defthm no-duplicates-of-remove
     (implies (no-duplicatesp x)
              (no-duplicatesp (remove k x))))

   (defthm symbol-listp-remove-duplicates
     (implies (symbol-listp x)
              (symbol-listp (remove-duplicates-equal x))))

   (defthm symbol-listp-append
     (implies (and (symbol-listp x)
                   (symbol-listp y))
              (symbol-listp (append x y))))

   (defthm symbol-listp-remove-eq
     (implies (symbol-listp x)
              (symbol-listp (remove k x))))

   (defthm no-duplicatesp-remove-duplicates
     (no-duplicatesp (remove-duplicates-equal x)))

   (defthm pseudo-term-listp-remove-equal
     (implies (pseudo-term-listp x)
              (pseudo-term-listp (remove-equal k x))))

   (defthm pseudo-term-listp-when-symbol-listp
     (implies (symbol-listp x)
              (pseudo-term-listp x)))))

(defthm assoc-pairlis-abs-ev-lst
  (equal (assoc x (pairlis$ syms (abs-ev-lst syms a)))
         (and (member x syms)
              (cons x (abs-ev x a)))))


(defthm assoc-in-cons-pairlis-remove
  (equal (assoc x (cons (cons k v)
                        (pairlis$ (remove k syms)
                                  (abs-ev-lst (remove k syms) a))))
         (assoc x (cons (cons k v)
                        (pairlis$ syms (abs-ev-lst syms a))))))


(defthm-simple-term-vars-flag
  (defthm abs-ev-of-cons-pairlis-remove-more
    (implies (and (pseudo-termp x)
                  (subsetp (simple-term-vars x) syms))
             (equal (abs-ev x (cons (cons k v)
                                    (pairlis$ (remove k syms)
                                              (abs-ev-lst (remove k syms) a))))
                    (abs-ev x (cons (cons k v)
                                     a))))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable abs-ev-constraint-0))))
    :flag simple-term-vars)
  (defthm abs-ev-lst-of-cons-pairlis-remove-more
    (implies (and (pseudo-term-listp x)
                  (subsetp (simple-term-vars-lst x) syms))
             (equal (abs-ev-lst x (cons (cons k v)
                                    (pairlis$ (remove k syms)
                                              (abs-ev-lst (remove k syms) a))))
                    (abs-ev-lst x (cons (cons k v) a))))
    :flag simple-term-vars-lst))

(defsection let-abstract-build-lambdas


  (defund let-abstract-build-lambdas (bindings abs-term vars)
    (declare (xargs :guard (and (symbol-alistp bindings)
                                (pseudo-term-listp (strip-cdrs bindings))
                                (symbol-listp vars))))
    (if (atom bindings)
        abs-term
      (let* ((new-vars (remove-eq (caar bindings) vars))
             (new-abs-term
              `((lambda ,(cons (caar bindings) new-vars) ,abs-term)
                ,(cdar bindings) . ,new-vars))
             (new-vars2 (remove-duplicates-eq
                         (append (simple-term-vars (cdar bindings)) new-vars))))
        (let-abstract-build-lambdas (cdr bindings) new-abs-term new-vars2))))

  (local (in-theory (enable let-abstract-build-lambdas)))


  (defthm symbol-listp-remove-equal
    (implies (symbol-listp x)
             (symbol-listp (remove k x))))

  (defthm term-list-vars-of-symbol-list
    (implies (symbol-listp x)
             (set-equiv (simple-term-vars-lst x) (remove nil x))))

  (local (in-theory (disable set-equiv)))

  (defthm-simple-term-vars-flag
    (defthm nil-not-member-of-simple-term-vars
      (not (member nil (simple-term-vars x)))
      :flag simple-term-vars)
    (defthm nil-not-member-of-simple-term-vars-lst
      (not (member nil (simple-term-vars-lst x)))
      :flag simple-term-vars-lst))

  (local (defthm remove-equal-redundant
           (implies (and (symbol-listp x)
                         (not (member k x)))
                    (equal (remove k x) x))))


  (defthm let-abstract-build-lambdas-pseudo-termp
    (implies (and (var-ordered-bindingsp bindings)
                  (symbol-alistp bindings)
                  (pseudo-term-listp (strip-cdrs bindings))
                  (pseudo-termp abs-term)
                  (symbol-listp vars)
                  (not (member nil vars))
                  (double-rewrite (set-equiv vars (simple-term-vars abs-term)))
                  (no-duplicatesp vars)
                  (no-duplicatesp (strip-cars bindings)))
             (pseudo-termp (let-abstract-build-lambdas bindings abs-term
                                                       vars))))

  (defthm let-abstract-build-lambdas-correct
    (implies (and (var-ordered-bindingsp bindings)
                  (symbol-alistp bindings)
                  (pseudo-term-listp (strip-cdrs bindings))
                  (pseudo-termp abs-term)
                  (symbol-listp vars)
                  (not (member nil vars))
                  (double-rewrite (set-equiv vars (simple-term-vars abs-term)))
                  (no-duplicatesp vars)
                  (no-duplicatesp (strip-cars bindings)))
             (equal (abs-ev (let-abstract-build-lambdas bindings abs-term vars)
                            a)
                    (abs-ev abs-term (eval-bindings bindings a))))))



(defsection let-abstract-term-top
  (defund let-abstract-term-top (term subterms)
    (declare (xargs :guard (and (pseudo-termp term)
                                (check-subterm-alist subterms))
                    :guard-hints (("goal" :in-theory (enable check-subterm-alist)))))
    (b* (((mv bindings abs-term) (let-abstract-term-rec term subterms nil))
         (vars (remove-duplicates-eq (simple-term-vars abs-term))))
      (let-abstract-build-lambdas bindings abs-term vars)))

  (local (in-theory (enable let-abstract-term-top)))

  (defthm let-abstract-term-top-pseudo-termp
    (implies (and (check-subterm-alist subterms)
                  (not (intersectp-eq (strip-cdrs subterms)
                                      (simple-term-vars term)))
                  (pseudo-termp term))
             (pseudo-termp (let-abstract-term-top term subterms)))
    :hints (("goal" :do-not-induct t)))

  (defthm let-abstract-term-top-correct
    (implies (and (check-subterm-alist subterms)
                  (not (intersectp-eq (strip-cdrs subterms)
                                      (simple-term-vars term)))
                  (pseudo-termp term))
             (equal (abs-ev (let-abstract-term-top term subterms) a)
                    (abs-ev term a)))
    :hints (("goal" :do-not-induct t))))

(defsection let-abstract-literals
  (defund let-abstract-literals (clause subterms)
    (declare (xargs :guard (and (pseudo-term-listp clause)
                                (check-subterm-alist subterms))))
    (if (atom clause)
        nil
      (cons (let-abstract-term-top (car clause) subterms)
            (let-abstract-literals (cdr clause) subterms))))

  (local (in-theory (enable let-abstract-literals)))

  (defthm let-abstract-literals-pseudo-termp
    (implies (and (check-subterm-alist subterms)
                  (not (intersectp-eq (strip-cdrs subterms)
                                      (simple-term-vars-lst clause)))
                  (pseudo-term-listp clause))
             (pseudo-term-listp (let-abstract-literals clause subterms))))

  (defthm let-abstract-literals-correct
    (implies (and (check-subterm-alist subterms)
                  (not (intersectp-eq (strip-cdrs subterms)
                                      (simple-term-vars-lst clause)))
                  (pseudo-term-listp clause))
             (equal (abs-ev-lst (let-abstract-literals clause subterms) a)
                    (abs-ev-lst clause a))))

  (defthm let-abstract-literals-disjoin
    (implies (and (check-subterm-alist subterms)
                  (not (intersectp-eq (strip-cdrs subterms)
                                      (simple-term-vars-lst clause)))
                  (pseudo-term-listp clause))
             (iff (abs-ev (disjoin (let-abstract-literals clause subterms)) a)
                  (abs-ev (disjoin clause) a)))))



(defsection let-abstraction-cp
  (defund let-abstraction-cp (clause subterm-alist)
    (declare (xargs :guard (pseudo-term-listp clause)
                    :guard-hints ('(:in-theory (enable check-subterm-alist)))))
    (b* (((unless (check-subterm-alist subterm-alist)) (list clause))
         (vars (strip-cdrs subterm-alist))
         ((when (intersectp-eq vars (simple-term-vars-lst clause)))
          (list clause)))
      (list (let-abstract-literals clause subterm-alist))))

  (local (in-theory (enable let-abstraction-cp)))

  (defthm let-abstraction-cp-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp a)
                  (abs-ev (conjoin-clauses (let-abstraction-cp clause
                                                               subterm-alist)) a))
             (abs-ev (disjoin clause) A))
    :rule-classes :clause-processor))


(mutual-recursion
 (defun collect-multi-occ-subterms1 (x seen multi)
   (declare (xargs :guard (and (pseudo-termp x)
                               (true-listp seen)
                               (true-listp multi))
                   :verify-guards nil))
   (b* (((when (or (variablep x)
                   (fquotep x)
                   (member-equal x multi))) (mv seen multi))
        ((when (member-equal x seen)) (mv seen (cons x multi)))
        (seen (cons x seen)))
     (collect-multi-occ-subterms1-list (cdr x) seen multi)))
 (defun collect-multi-occ-subterms1-list (x seen multi)
   (declare (xargs :guard (and (pseudo-term-listp x)
                               (true-listp seen)
                               (true-listp multi))))
   (b* (((when (atom x)) (mv seen multi))
        ((mv seen multi) (collect-multi-occ-subterms1 (car x) seen multi)))
     (collect-multi-occ-subterms1-list (cdr x) seen multi))))

(flag::make-flag collect-multi-occ-subterms1-flg collect-multi-occ-subterms1)

(defthm-collect-multi-occ-subterms1-flg
  (defthm true-listp-collect-multi-occ-subterms1-seen
    (equal (true-listp (mv-nth 0 (collect-multi-occ-subterms1 x seen multi)))
           (true-listp seen))
    :flag collect-multi-occ-subterms1)
  (defthm true-listp-collect-multi-occ-subterms1-list-seen
    (equal (true-listp (mv-nth 0 (collect-multi-occ-subterms1-list x seen multi)))
           (true-listp seen))
    :flag collect-multi-occ-subterms1-list))

(defthm-collect-multi-occ-subterms1-flg
  (defthm true-listp-collect-multi-occ-subterms1-multi
    (equal (true-listp (mv-nth 1 (collect-multi-occ-subterms1 x seen multi)))
           (true-listp multi))
    :flag collect-multi-occ-subterms1)
  (defthm true-listp-collect-multi-occ-subterms1-list-multi
    (equal (true-listp (mv-nth 1 (collect-multi-occ-subterms1-list x seen multi)))
           (true-listp multi))
    :flag collect-multi-occ-subterms1-list))

(verify-guards collect-multi-occ-subterms1-list)


(defun collect-multi-occ-subterms (term)
  (declare (xargs :guard (pseudo-termp term)))
  (b* (((mv ?seen multi) (collect-multi-occ-subterms1 term nil nil)))
    multi))

(defun collect-multi-occ-subterms-list (termlist)
  (declare (xargs :guard (pseudo-term-listp termlist)))
  (b* (((mv ?seen multi) (collect-multi-occ-subterms1-list termlist nil nil)))
    multi))


(mutual-recursion
 (defun collect-subterm-counts-term (x alist)
   (declare (xargs :guard (and (pseudo-termp x)
                               (alistp alist))
                   :verify-guards nil))
   (b* (((when (variablep x)) alist)
        ((when (fquotep x)) alist)
        (look (assoc-equal x alist))
        ((when look) (cons (cons x (+ 1 (nfix (cdr look)))) alist))
        (alist (cons (cons x 1) alist)))
     (collect-subterm-counts-list (cdr x) alist)))
 (defun collect-subterm-counts-list (x alist)
   (declare (xargs :guard (and (pseudo-term-listp x)
                               (alistp alist))))
   (if (atom x)
       alist
     (collect-subterm-counts-list
      (cdr x) (collect-subterm-counts-term (car x) alist)))))

(flag::make-flag collect-subterm-counts-flg collect-subterm-counts-term)

(defthm-collect-subterm-counts-flg
  (defthm alistp-collect-subterm-counts-term
    (implies (alistp alist)
             (alistp (collect-subterm-counts-term x alist)))
    :flag collect-subterm-counts-term)
  (defthm alistp-collect-subterm-counts-list
    (implies (alistp alist)
             (alistp (collect-subterm-counts-list x alist)))
    :flag collect-subterm-counts-list))

(verify-guards collect-subterm-counts-term)

(defun collect-bound-to-gte-n (alist n)
  (declare (xargs :guard (and (alistp alist)
                              (natp n))))
  (if (atom alist)
      nil
    (let ((rest (collect-bound-to-gte-n (cdr alist) n)))
      (if (and (<= n (nfix (cdar alist)))
               (not (member-equal (caar alist) rest)))
          (cons (caar alist) rest)
        rest))))


(defun collect-multi-occurrence-subterms (x n)
  "Gets a list of subterms of x that occur N or more times"
  (declare (xargs :guard (and (pseudo-termp x) (natp n))))
  (collect-bound-to-gte-n (collect-subterm-counts-term x nil) n))
