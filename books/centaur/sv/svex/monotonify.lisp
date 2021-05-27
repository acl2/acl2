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
(include-book "lattice")

(local (defthm svex-count-gt-1
         (implies (svex-case x :call)
                  (< 1 (svex-count x)))
         :hints(("Goal" :expand ((svex-count x))))
         :rule-classes :linear))

;; (local
;;  (progn
;;    (defthm 4vec-==-[=-===-ext
;;      (implies (and (4vec-[= a1 a)
;;                    (4vec-[= b1 b))
;;               (4vec-[= (4vec-== a1 b1) (4vec-=== a b)))
;;      :hints (("goal" :in-theory (e/d (4vec-[=-transitive-2)
;;                                      (4vec-==-[=-===))
;;               :use ((:instance 4vec-==-[=-===)))))

;;    (defthm 4vec-wildeq-safe-[=-wildeq-ext
;;      (implies (and (4vec-[= a1 a)
;;                    (4vec-[= b1 b))
;;               (4vec-[= (4vec-wildeq-safe a1 b1) (4vec-wildeq a b)))
;;      :hints (("goal" :in-theory (e/d (4vec-[=-transitive-2)
;;                                      (4vec-wildeq-safe-[=-wildeq))
;;               :use ((:instance 4vec-wildeq-safe-[=-wildeq)))))


;;    (defthm 4vec-bit?-[=-bit?!-ext
;;      (implies (and (4vec-[= test1 test)
;;                    (4vec-[= then1 then)
;;                    (4vec-[= else1 else))
;;               (4vec-[= (4vec-bit? test1 then1 else1)
;;                        (4vec-bit?! test then else)))
;;      :hints (("goal" :in-theory (e/d (4vec-[=-transitive-2)
;;                                      (4vec-bit?-[=-bit?!))
;;               :use ((:instance 4vec-bit?-[=-bit?!)))))


;;    (defthm 4vec-?*-[=-?!-ext
;;      (implies (and (4vec-[= test1 test)
;;                    (4vec-[= then1 then)
;;                    (4vec-[= else1 else))
;;               (4vec-[= (4vec-?* test1 then1 else1)
;;                        (4vec-?! test then else)))
;;      :hints (("goal" :in-theory (e/d (4vec-[=-transitive-2)
;;                                      (4vec-?*-[=-?!))
;;               :use ((:instance 4vec-?*-[=-?!)))))))

(defconst *svex-fn/args-monotonify-body*
  '(case (fnsym-fix fn)
     (=== (b* (((unless (eql (len args) 2))
                (svex-call '== (svexlist-monotonify args)))
               ((list first second) args)
               ((when (svex-case second :quote))
                (svex-call '===* (list (svex-monotonify first) second)))
               ((when (svex-case first :quote))
                (svex-call '===* (list (svex-monotonify second) first))))
            (svex-call '== (list (svex-monotonify first) (svex-monotonify second)))))
     (===* (b* (((unless (eql (len args) 2))
                 (svex-call '== (svexlist-monotonify args)))
                ((list first second) args)
                ((when (svex-case second :quote))
                 (svex-call '===* (list (svex-monotonify first) second))))
             (svex-call '== (list (svex-monotonify first) (svex-monotonify second)))))
     (==? (b* (((unless (and (eql (len args) 2)
                             (svex-case (second args) :quote)))
                (svex-call 'safer-==? (svexlist-monotonify args))))
            (svex-call '==? (list (svex-monotonify (first args)) (second args)))))
     (?!  (b* (((unless (and (eql (len args) 3)
                             (svex-case (first args) :quote)))
                (svex-call '?* (svexlist-monotonify args))))
            (svex-call '?! (list (first args)
                                 (svex-monotonify (second args))
                                 (svex-monotonify (third args))))))
     (bit?! (b* (((unless (and (eql (len args) 3)
                               (svex-case (first args) :quote)))
                  (svex-call 'bit? (svexlist-monotonify args))))
              (svex-call 'bit?! (list (first args)
                                      (svex-monotonify (second args))
                                      (svex-monotonify (third args))))))
     (otherwise (svex-call fn (svexlist-monotonify args)))))

(defconst *svex-monotonify-event*
  '(defines svex-monotonify
     (define svex-monotonify ((x svex-p))
       :measure (acl2::two-nats-measure (svex-count x) 1)
       :returns (new-x svex-p)
       :verify-guards nil
       (svex-case x
         :var (svex-fix x)
         :quote (svex-fix x)
         :call (svex-call-monotonify x)))
     (define svex-call-monotonify ((x svex-p))
       :measure (acl2::two-nats-measure (svex-count x) 0)
       :guard (svex-case x :call)
       :returns (new-x svex-p)
       (b* (((unless (mbt (svex-case x :call))) (svex-x))
            ((svex-call x)))
         (mbe :logic (svex-fn/args-monotonify x.fn x.args)
              :exec (let* ((fn x.fn)
                           (args x.args))
                      <body>))))
     (define svex-fn/args-monotonify ((fn fnsym-p)
                                      (args svexlist-p))
       :measure (acl2::two-nats-measure (svexlist-count args) 1)
       :returns (new-x svex-p)
       <body>)
     (define svexlist-monotonify ((x svexlist-p))
       :measure (acl2::two-nats-measure (svexlist-count x) 0)
       :returns (new-x svexlist-p)
       (if (atom x)
           nil
         (cons (svex-monotonify (car x))
               (svexlist-monotonify (cdr x)))))
     ///
     (local (in-theory (disable svex-monotonify
                                svex-call-monotonify
                                svexlist-monotonify)))

     (verify-guards svex-monotonify)
     (memoize 'svex-call-monotonify)


     (defret len-of-<fn>
       (equal (len new-x) (len x))
       :hints(("Goal" :in-theory (enable svexlist-monotonify)))
       :fn svexlist-monotonify)

     (local (defthm open-svex-apply
              (implies (syntaxp (quotep fn))
                       (equal (svex-apply fn args)
                              (b* ((fn (fnsym-fix fn))
                                   (args (4veclist-fix args)))
                                (svex-apply-cases fn args))))
              :hints(("Goal" :in-theory (enable svex-apply)))))


     (local (defthm nth-of-svexlist-mono-eval
              (4vec-equiv (nth n (svexlist-mono-eval x env))
                          (svex-mono-eval (nth n x) env))
              :hints(("Goal" :in-theory (enable nth svexlist-mono-eval
                                                svex-mono-eval-of-quote)))))

     (local (defthm 4veclist-nth-safe-of-svex-mono-eval
              (equal (4veclist-nth-safe n (svexlist-mono-eval x env))
                     (svex-mono-eval (nth n x) env))
              :hints(("Goal" :in-theory (enable 4veclist-nth-safe nth)))))

     (local (defthm nth-of-svexlist-eval
              (4vec-equiv (nth n (svexlist-eval x env))
                          (svex-eval (nth n x) env))
              :hints(("Goal" :in-theory (enable nth svexlist-eval)))))

     (local (defthm 4veclist-nth-safe-of-svex-eval
              (equal (4veclist-nth-safe n (svexlist-eval x env))
                     (svex-eval (nth n x) env))
              :hints(("Goal" :in-theory (enable 4veclist-nth-safe nth)))))

     (local (defthm 4vec-[=-car-mono-eval/eval-when-4veclist-[=
              (implies (4veclist-[= (svexlist-mono-eval x env) (svexlist-eval x env))
                       (4vec-[= (svex-mono-eval (car x) env)
                                (svex-eval (car x) env)))
              :hints (("goal" :expand ((svexlist-mono-eval x env) (svexlist-eval x env))
                       :in-theory (enable svex-mono-eval-of-quote)))))

     (local (defthm 4veclist-[=-cdr-mono-eval/eval-when-4veclist-[=
              (implies (4veclist-[= (svexlist-mono-eval x env) (svexlist-eval x env))
                       (4veclist-[= (svexlist-mono-eval (cdr x) env)
                                    (svexlist-eval (cdr x) env)))
              :hints (("goal" :expand ((svexlist-mono-eval x env) (svexlist-eval x env))))))

     (local (defthm 4vec-[=-nth-mono-eval/eval-when-4veclist-[=
              (implies (4veclist-[= (svexlist-mono-eval x env) (svexlist-eval x env))
                       (4vec-[= (svex-mono-eval (nth n x) env)
                                (svex-eval (nth n x) env)))
              :hints (("goal"
                       :induct (nth n x)
                       :expand ((svexlist-mono-eval x env)
                                (svexlist-eval x env)
                                (nth n x))
                       :in-theory (enable svex-mono-eval-of-quote)))))

     (std::defret-mutual svex-monotonify-correct
       (defret <fn>-correct
         (equal (svex-eval new-x env)
                (svex-mono-eval x env))
         :hints ('(:expand <call>)
                 (and stable-under-simplificationp
                      '(:expand ((svex-mono-eval x env)
                                 (svex-eval x env)))))
         :fn svex-monotonify)
       (defret <fn>-correct
         (equal (svex-eval new-x env)
                (svex-call-mono-eval x env))
         :hints ('(:expand (<call>
                            (svex-call-mono-eval x env))
                   :in-theory (enable svex-mono-eval-of-quote)))
         :fn svex-call-monotonify)
       (defret <fn>-correct
         (equal (svex-eval new-x env)
                (svex-fn/args-mono-eval fn args env))
         :hints ('(:expand ((:free (fn) <call>)
                            (:free (fn) (svex-fn/args-mono-eval fn args env)))
                   :in-theory (enable svex-mono-eval-of-quote)))
         :fn svex-fn/args-monotonify)
       (defret <fn>-correct
         (equal (svexlist-eval new-x env)
                (svexlist-mono-eval x env))
         :hints ('(:expand (<call>
                            (svexlist-mono-eval x env))))
         :fn svexlist-monotonify))


     (std::defret-mutual svex-monotonify-check-monotonic
       (defret <fn>-check-monotonic
         (svex-check-monotonic new-x)
         :hints ('(:expand (<call>))
                 (and stable-under-simplificationp
                      '(:in-theory (enable svex-check-monotonic))))
         :fn svex-monotonify)
       (defret <fn>-check-monotonic
         (svex-check-monotonic new-x)
         :hints ('(:expand (<call>)))
         :fn svex-call-monotonify)
       (defret <fn>-check-monotonic
         (svex-check-monotonic new-x)
         :hints ('(:expand (<call>))
                 (and stable-under-simplificationp
                      '(:in-theory (enable svex-check-monotonic)
                        :expand ((:free (a b) (svexlist-check-monotonic (cons a b)))))))
         :fn svex-fn/args-monotonify)
       (defret <fn>-check-monotonic
         (svexlist-check-monotonic new-x)
         :hints ('(:expand (<call>
                            (:free (a b) (svexlist-check-monotonic (cons a b))))))
         :fn svexlist-monotonify))))

#||
(defines svex-monotonify
  (define svex-monotonify ...)
  (define svex-call-monotonify ...)
  (define svex-fn/args-monotonify ...)
  (define svexlist-monotonify ...)
  ...)
||#
(make-event
 (subst *svex-fn/args-monotonify-body* '<body> *svex-monotonify-event*))
