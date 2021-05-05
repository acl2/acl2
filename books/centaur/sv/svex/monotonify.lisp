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
(include-book "std/basic/two-nats-measure" :dir :system)

(local (defthm svex-count-gt-1
         (implies (svex-case x :call)
                  (< 1 (svex-count x)))
         :hints(("Goal" :expand ((svex-count x))))
         :rule-classes :linear))

(local
 (progn
   (defthm 4vec-==-[=-===-ext
     (implies (and (4vec-[= a1 a)
                   (4vec-[= b1 b))
              (4vec-[= (4vec-== a1 b1) (4vec-=== a b)))
     :hints (("goal" :in-theory (e/d (4vec-[=-transitive-2)
                                     (4vec-==-[=-===))
              :use ((:instance 4vec-==-[=-===)))))

   (defthm 4vec-wildeq-safe-[=-wildeq-ext
     (implies (and (4vec-[= a1 a)
                   (4vec-[= b1 b))
              (4vec-[= (4vec-wildeq-safe a1 b1) (4vec-wildeq a b)))
     :hints (("goal" :in-theory (e/d (4vec-[=-transitive-2)
                                     (4vec-wildeq-safe-[=-wildeq))
              :use ((:instance 4vec-wildeq-safe-[=-wildeq)))))


   (defthm 4vec-bit?-[=-bit?!-ext
     (implies (and (4vec-[= test1 test)
                   (4vec-[= then1 then)
                   (4vec-[= else1 else))
              (4vec-[= (4vec-bit? test1 then1 else1)
                       (4vec-bit?! test then else)))
     :hints (("goal" :in-theory (e/d (4vec-[=-transitive-2)
                                     (4vec-bit?-[=-bit?!))
              :use ((:instance 4vec-bit?-[=-bit?!)))))


   (defthm 4vec-?*-[=-?!-ext
     (implies (and (4vec-[= test1 test)
                   (4vec-[= then1 then)
                   (4vec-[= else1 else))
              (4vec-[= (4vec-?* test1 then1 else1)
                       (4vec-?! test then else)))
     :hints (("goal" :in-theory (e/d (4vec-[=-transitive-2)
                                     (4vec-?*-[=-?!))
              :use ((:instance 4vec-?*-[=-?!)))))))

(defines svex-monotonify
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
      (case x.fn
        (=== (svex-call '== (svexlist-monotonify x.args)))
        (==? (b* (((unless (and (eql (len x.args) 2)
                                (svex-case (second x.args) :quote)))
                   (svex-call 'safer-==? (svexlist-monotonify x.args))))
               (svex-call '==? (list (svex-monotonify (first x.args)) (second x.args)))))
        (?!  (b* (((unless (and (eql (len x.args) 3)
                                (svex-case (first x.args) :quote)))
                   (svex-call '?* (svexlist-monotonify x.args))))
               (svex-call '?! (list (first x.args)
                                    (svex-monotonify (second x.args))
                                    (svex-monotonify (third x.args))))))
        (bit?! (b* (((unless (and (eql (len x.args) 3)
                                  (svex-case (first x.args) :quote)))
                     (svex-call 'bit? (svexlist-monotonify x.args))))
                 (svex-call 'bit?! (list (first x.args)
                                         (svex-monotonify (second x.args))
                                         (svex-monotonify (third x.args))))))
        (otherwise (svex-call x.fn (svexlist-monotonify x.args))))))
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

  


  (std::defret-mutual svex-monotonify-correct
    (defret <fn>-correct
      (4vec-[= (svex-eval new-x env) (svex-eval x env))
      :hints ('(:expand <call>))
      :fn svex-monotonify)
    (defret <fn>-correct
      (4vec-[= (svex-eval new-x env) (svex-eval x env))
      :hints ('(:expand <call>)
              ;; (and stable-under-simplificationp
              ;;      '(:in-theory (enable svex-apply)))
              )
      :fn svex-call-monotonify)
    (defret <fn>-correct
      (4veclist-[= (svexlist-eval new-x env) (svexlist-eval x env))
      :hints ('(:expand <call>))
      :fn svexlist-monotonify))

  (local (defthm svex-monotonic-p-of-quote
           (implies (svex-case x :quote)
                    (svex-monotonic-p x))
           :hints(("Goal" :in-theory (enable svex-monotonic-p)))))

  (local (defthm svex-monotonic-p-of-var
           (implies (svex-case x :var)
                    (svex-monotonic-p x))
           :hints(("Goal" :in-theory (enable svex-monotonic-p)))))

  (std::defret-mutual svex-monotonify-monotonic
    (defret <fn>-monotonic
      (svex-monotonic-p new-x)
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:in-theory (enable svex-monotonic-p))))
      :fn svex-monotonify)
    (defret <fn>-monotonic
      (svex-monotonic-p new-x)
      :hints ('(:expand (<call>
                         (:free (fn args) (svex-monotonic-p (svex-call fn args)))
                         (:free (a b) (svexlist-monotonic-p (cons a b))))))
      :fn svex-call-monotonify)
    (defret <fn>-monotonic
      (svexlist-monotonic-p new-x)
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:in-theory (enable svexlist-monotonic-p))))
      :fn svexlist-monotonify)))
