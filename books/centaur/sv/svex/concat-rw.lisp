; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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

(in-package "SV")
(include-book "context-alist")
(include-book "rsh-concat")
(defxdoc concat-rw.lisp :parents (svex-rewriting))
(local (xdoc::set-default-parents svex-rewrite.lisp))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/misc/arith-equivs" :dir :system))

(std::add-default-post-define-hook :fix)

(local (defthm 2vec-of-4vec->lower
           (implies (2vec-p x)
                    (equal (2vec (4vec->lower x))
                           (4vec-fix x)))))

(define svex-normalize-concatenation ((width natp)
                                      (first svex-p)
                                      (rest svex-p)
                                      (ctxalist svex-context-alist-p))
  :measure (svex-count first)
  :verify-guards nil
  :returns (new-concat svex-p)
  (b* ((width (lnfix width))
       (const-width-concat-p (svex-case first
                               :call (and (eq first.fn 'concat)
                                          (eql (len first.args) 3)
                                          (svex-quoted-index-p (car first.args)))
                               :otherwise nil))
       ((unless (and const-width-concat-p
                     ;; check that it's only referenced once:
                     (eql (len (cdr (hons-get (svex-fix first)
                                              (svex-context-alist-fix ctxalist)))) 1)))
        (svex-call 'concat (list (svex-quote (2vec (lnfix width)))
                                 first rest)))

       ((list width1 first1 rest1) (svex-call->args first))
       (width1 (2vec->val (svex-quote->val width1)))

        ;; Have (concat width (concat width1 first1 rest1) rest).
       ((when (>= width1 width))
        ;; Here width1 >= width.  So really this is just
        ;; (concat width first1 rest), which we might be able to further simplify.
        (svex-normalize-concatenation width first1 rest ctxalist)))

    ;; Otherwise with width1 < width, we normalize this to
    ;; (concat width1 first1 (concat (- width width1) rest1 rest)).
    (svex-normalize-concatenation
     width1 first1
     (svex-normalize-concatenation (- width width1) rest1 rest ctxalist)
     ctxalist))
  ///
  ;; (local (defthm 4vec-concat-normalize
  ;;          (implies (and (2vec-p width)
  ;;                        (2vec-p width1)
  ;;                        (<= 0 width)
  ;;                        (<= 0 width1))
  ;;                   (equal (4vec-concat width (4vec-concat width1 first1 rest1) rest)
  ;;                          (if (<= (2vec->val width) (2vec->val width1))
  ;;                              (4vec-concat width first1 rest)
  ;;                            (4vec-concat width1 first1 (4vec-concat
  ;;                                                        (2vec (- (2vec->val width)
  ;;                                                                 (2vec->val width1)))
  ;;                                                        rest1 rest)))))
  ;;          :hints(("Goal" :in-theory (enable 4vec-concat)))))

  ;; (local (defthm 2vec-of-4vec->lower


  (defret svex-normalize-concatenation-correct
    (equal (svex-eval new-concat env)
           (4vec-concat (2vec (nfix width))
                        (svex-eval first env)
                        (svex-eval rest env)))
    :hints(("Goal" :in-theory (enable svex-apply svexlist-eval 4vec-index-p
                                      4veclist-nth-safe nth))))

  (local (defthm svexlist-count-when-len-0
           (implies (equal (len (cdddr x)) 0)
                    (equal (svexlist-count (cdddr x)) 1))
           :hints(("Goal" :in-theory (enable len svexlist-count)
                   :expand ((len (cdddr x)))))))
             

  (defret svex-count-of-svex-normalize-concatenation
    (<= (svex-count (svex-normalize-concatenation width first rest ctxalist))
        (svex-count (svex-call 'concat (list (svex-quote (2vec (nfix width)))
                                             first rest))))
    :hints (("Goal" :induct (svex-normalize-concatenation width first rest ctxalist)
             :expand ((:free (width first rest)
                       (svex-count (svex-call 'concat (list width first rest))))
                      (:free (width)
                       (svex-count (svex-quote width)))
                      (:free (a b) (svexlist-count (cons a b)))
                      ))
            (and stable-under-simplificationp
                 '(:expand ((svex-count first)
                            (svexlist-count (svex-call->args first))
                            (SVEX-COUNT (CAR (SVEX-CALL->ARGS FIRST)))
                            (svexlist-count (cdr (svex-call->args first)))
                            (svexlist-count (cddr (svex-call->args first)))))))
    :rule-classes nil)

  (defthm svex-count-of-svex-normalize-concatenation-special
    (implies (svex-case x :call (and (equal x.fn 'concat)
                                     (equal (len x.args) 3)
                                     (svex-quoted-index-p (car x.args)))
               :otherwise nil)
             (b* (((svex-call x)))
               (<= (svex-count (svex-normalize-concatenation
                                (4vec->lower (svex-quote->val (car x.args)))
                                (cadr x.args) (caddr x.args) ctxalist))
                   (svex-count x))))
    :hints (("goal" :use ((:instance svex-count-of-svex-normalize-concatenation
                           (width (2vec->val (svex-quote->val (car (svex-call->args x)))))
                           (first (cadr (svex-call->args x)))
                           (rest  (caddr (svex-call->args x)))))
             :in-theory (e/d ()
                             (svex-normalize-concatenation))
             :expand ((:free (width first rest)
                       (svex-count (svex-call 'concat (list width first rest))))
                      (svex-count x)
                      (:free (width)
                       (svex-count (svex-quote width)))
                      (:free (a b) (svexlist-count (cons a b)))
                      (svexlist-count (svex-call->args x))
                      (SVEX-COUNT (CAR (SVEX-CALL->ARGS x)))
                      (svexlist-count (cdr (svex-call->args x)))
                      (svexlist-count (cddr (svex-call->args x))))))
    :rule-classes :linear)
  
  (verify-guards svex-normalize-concatenation))

(defines svex-normalize-concats-aux
  :verify-guards nil
  (define svex-normalize-concats-aux ((x svex-p)
                                      (ctxalist svex-context-alist-p))
    :returns (new-x svex-p)
    :measure (svex-count x)
    (b* ((x1 (svex-case x
               :call (b* (((unless (and (eq x.fn 'concat)
                                        (eql (len x.args) 3)
                                        (svex-quoted-index-p (car x.args))))
                           (svex-fix x)))
                       (svex-normalize-concatenation
                        (2vec->val (svex-quote->val (car x.args)))
                        (cadr x.args) (caddr x.args) ctxalist))
               :otherwise (svex-fix x))))
      (svex-case x1
        :call (svex-call x1.fn (svexlist-normalize-concats-aux x1.args ctxalist))
        :otherwise x1)))

  (define svexlist-normalize-concats-aux ((x svexlist-p)
                                          (ctxalist svex-context-alist-p))
    :returns (new-x (and (svexlist-p new-x)
                         (eql (len new-x) (len x))))
    :measure (svexlist-count x)
    (if (atom x)
        nil
      (cons (svex-normalize-concats-aux (car x) ctxalist)
            (svexlist-normalize-concats-aux (cdr x) ctxalist))))
  ///
  (verify-guards svex-normalize-concats-aux)
  (deffixequiv-mutual svex-normalize-concats-aux)

  (local (defthm svex-apply-of-call-args
           (implies (and ;; (syntaxp (not (and (consp x)
                         ;;                    (eq (car x) 'svex-call))))
                         (svex-case x :call))
                    (equal (svex-apply (svex-call->fn x) (svexlist-eval
                                                          (svex-call->args x) env))
                           (svex-eval x env)))
           :hints(("Goal" :in-theory (enable svex-eval)))))

  (local (in-theory (disable svex-eval-when-fncall)))

  (defthm-svex-normalize-concats-aux-flag
    (defthm svex-normalize-concats-aux-correct
      (equal (svex-eval (svex-normalize-concats-aux x ctxalist) env)
             (svex-eval x env))
      :hints ('(:expand ((svex-normalize-concats-aux x ctxalist)
                         (:free (args) (Svex-apply 'concat args))
                         (:free (x) (nth 0 x)) (:free (x) (nth 1 x))
                         (:free (x) (nth 2 x))
                         (svex-eval x env))
                :in-theory (enable 4veclist-nth-safe)))
      :flag svex-normalize-concats-aux)
    (defthm svexlist-normalize-concats-aux-correct
      (equal (svexlist-eval (svexlist-normalize-concats-aux x ctxalist) env)
             (svexlist-eval x env))
      :hints ('(:expand ((svexlist-normalize-concats-aux x ctxalist))))
      :flag svexlist-normalize-concats-aux))

  (memoize 'svex-normalize-concats-aux))

(define svex-normalize-concats ((x svex-p))
  :returns (new-x svex-p)
  (b* ((ctxalist (svexlist-make-top-context-alist (list x) nil))
       (res (svex-normalize-concats-aux x ctxalist)))
    (clear-memoize-table 'svex-normalize-concats-aux)
    (fast-alist-free ctxalist)
    res)
  ///
  (defret svex-normalize-concats-correct
    (equal (svex-eval new-x env) (svex-eval x env))))

(define svexlist-normalize-concats ((x svexlist-p))
  :returns (new-x (and (svexlist-p new-x) (equal (len new-x) (len x))))
  (b* ((ctxalist (svexlist-make-top-context-alist x nil))
       (res (svexlist-normalize-concats-aux x ctxalist)))
    (clear-memoize-table 'svex-normalize-concats-aux)
    (fast-alist-free ctxalist)
    res)
  ///
  (defret svexlist-normalize-concats-correct
    (equal (svexlist-eval new-x env) (svexlist-eval x env))))


      
                           
                  

