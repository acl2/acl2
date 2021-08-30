; Centaur Meta-reasoning Library
; Copyright (C) 2019 Centaur Technology
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

(in-package "CMR")

(include-book "equivalence")
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "std/lists/index-of" :dir :system)
(include-book "centaur/misc/nth-equiv" :dir :system)

(local (include-book "std/lists/append" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))

(local (include-book "std/lists/nthcdr" :dir :system))

(std::make-returnspec-config :hints-sub-returnnames t)

(local (in-theory (disable pseudo-termp)))

;; This is just a list of pseudo-fnsyms, but we'll name it equiv-contexts to
;; show its intended use (and in case we generalize it in the future).
(deflist equiv-contexts
  :pred equiv-contextsp
  :elt-type pseudo-fnsym :true-listp t)


;; The reflexive closure of the OR of the equivalences.
(define equiv-ev-context-equiv-base ((ctx equiv-contextsp) x y)
  (if (atom ctx)
      (equal x y)
    (or (and (equiv-ev (pseudo-term-fncall (car ctx)
                                           (list (pseudo-term-quote x)
                                                 (pseudo-term-quote y)))
                       nil)
             t)
        (equiv-ev-context-equiv-base (cdr ctx) x y)))
  ///
  (defthm equiv-ev-context-equiv-base-reflexive
    (equiv-ev-context-equiv-base ctx x x))

  (defthm equiv-ev-context-equiv-base-equal
    (equal (equiv-ev-context-equiv-base nil x y)
           (equal x y)))

  (defthm equiv-ev-context-equiv-base-of-append
    (equal (equiv-ev-context-equiv-base (append ctx1 ctx2) x y)
           (or (equiv-ev-context-equiv-base ctx1 x y)
               (equiv-ev-context-equiv-base ctx2 x y))))

  (defthmd equiv-ev-context-equiv-base-by-member
    (implies (and (member equiv (equiv-contexts-fix ctx))
                  (equiv-ev (pseudo-term-fncall equiv (list (pseudo-term-quote x) (pseudo-term-quote y))) nil))
             (equiv-ev-context-equiv-base ctx x y)))

  (defthmd equiv-ev-context-equiv-base-by-singleton
    (implies (and (equiv-ev-context-equiv-base (list equiv) x y)
                  (member (pseudo-fnsym-fix equiv) (equiv-contexts-fix ctx)))
             (equiv-ev-context-equiv-base ctx x y)))

  (defthmd equiv-ev-context-equiv-base-of-singleton
    (implies (equiv-ev-theoremp (equiv-rel-term equiv))
             (iff (equiv-ev-context-equiv-base (list equiv) x y)
                  (equiv-ev (pseudo-term-fncall equiv (list (pseudo-term-quote x)
                                                            (pseudo-term-quote y)))
                            nil)))
    :hints (("goal" :use ((:instance equiv-rel-term-implies-reflexive
                           (fn (pseudo-fnsym-fix equiv))
                           (x (pseudo-term-quote x))
                           (a nil))))))

  (defthmd equiv-ev-context-equiv-base-when-singleton
    (implies (equiv-ev (pseudo-term-fncall equiv (list (pseudo-term-quote x)
                                                       (pseudo-term-quote y)))
                       nil)
             (equiv-ev-context-equiv-base (list equiv) x y))))

;; The symmetric/reflexiv closure of the OR of the equivalences.
(define equiv-ev-context-equiv-symm ((ctx equiv-contextsp) x y)
  (or (equiv-ev-context-equiv-base ctx x y)
      (equiv-ev-context-equiv-base ctx y x))
  ///
  (defthm equiv-ev-context-equiv-symm-reflexive
    (equiv-ev-context-equiv-symm ctx x x))

  (defthm equiv-ev-context-equiv-symm-symmetric
    (implies (equiv-ev-context-equiv-symm ctx x y)
             (equiv-ev-context-equiv-symm ctx y x)))

  (defthm equiv-ev-context-equiv-symm-equal
    (equal (equiv-ev-context-equiv-symm nil x y)
           (equal x y)))

  (defthm equiv-ev-context-equiv-symm-of-append
    (equal (equiv-ev-context-equiv-symm (append ctx1 ctx2) x y)
           (or (equiv-ev-context-equiv-symm ctx1 x y)
               (equiv-ev-context-equiv-symm ctx2 x y))))

  (defthmd equiv-ev-context-equiv-symm-by-member
    (implies (and (member equiv (equiv-contexts-fix ctx))
                  (or (equiv-ev (pseudo-term-fncall equiv (list (pseudo-term-quote x) (pseudo-term-quote y))) nil)
                      (equiv-ev (pseudo-term-fncall equiv (list (pseudo-term-quote y) (pseudo-term-quote x))) nil)))
             (equiv-ev-context-equiv-symm ctx x y))
    :hints(("Goal" :in-theory (enable equiv-ev-context-equiv-base-by-member))))

  (defthmd equiv-ev-context-equiv-symm-by-singleton
    (implies (and (equiv-ev-context-equiv-symm (list equiv) x y)
                  (member (pseudo-fnsym-fix equiv) (equiv-contexts-fix ctx)))
             (equiv-ev-context-equiv-symm ctx x y))
    :hints(("Goal" :in-theory (enable equiv-ev-context-equiv-base-by-singleton))))

  (defthmd equiv-ev-context-equiv-symm-of-singleton
    (implies (equiv-ev-theoremp (equiv-rel-term equiv))
             (iff (equiv-ev-context-equiv-symm (list equiv) x y)
                  (equiv-ev (pseudo-term-fncall equiv (list (pseudo-term-quote x)
                                                            (pseudo-term-quote y)))
                            nil)))
    :hints (("goal" :in-theory (enable equiv-ev-context-equiv-base-of-singleton)
             :use ((:instance equiv-rel-term-implies-symmetric
                    (fn (pseudo-fnsym-fix equiv))
                    (x (pseudo-term-quote y))
                    (y (pseudo-term-quote x))
                    (a nil))))))

  (defthmd equiv-ev-context-equiv-symm-when-singleton
    (implies (equiv-ev (pseudo-term-fncall equiv (list (pseudo-term-quote x)
                                                       (pseudo-term-quote y)))
                       nil)
             (equiv-ev-context-equiv-symm (list equiv) x y))
    :hints(("Goal" :in-theory (enable equiv-ev-context-equiv-base-when-singleton)))))



(local (defthm car-last-of-append
         (equal (car (last (append x y)))
                (if (consp y)
                    (car (last y))
                  (car (last x))))))

(local (defthm car-last-of-rev
         (equal (car (last (acl2::rev x)))
                (car x))
         :hints(("Goal" :in-theory (enable acl2::rev)))))

(local (defthm consp-of-rev
         (equal (consp (acl2::rev x))
                (consp x))
         :hints(("Goal" :in-theory (enable acl2::rev)))))

(local (defthm car-of-append
         (equal (car (append x y))
                (if (consp x) (car x) (car y)))))

(local (defthm car-of-rev
         (equal (car (acl2::rev x))
                (car (last x)))
         :hints(("Goal" :in-theory (enable acl2::rev)))))

(define equiv-ev-context-equiv-trace ((ctx equiv-contextsp) (trace true-listp))
  (if (atom (cdr trace))
      t
    (and (equiv-ev-context-equiv-symm ctx (car trace) (cadr trace))
         (equiv-ev-context-equiv-trace ctx (cdr trace))))
  ///
  (defthm equiv-ev-context-equiv-trace-of-append
    (implies (And (equiv-ev-context-equiv-trace contexts trace1)
                  (equiv-ev-context-equiv-trace contexts trace2)
                  (implies (and (consp trace1) (consp trace2))
                           (equiv-ev-context-equiv-symm contexts (car (last trace1)) (car trace2))))
             (equiv-ev-context-equiv-trace contexts
                                          (append trace1 trace2))))

  (defthm equiv-ev-context-equiv-trace-not-equal
    (implies (not (equal (car (last trace)) (car trace)))
             (not (equiv-ev-context-equiv-trace nil trace))))

  (defthm equiv-ev-context-equiv-trace-implies-cdr
    (implies (equiv-ev-context-equiv-trace contexts trace)
             (equiv-ev-context-equiv-trace contexts (cdr trace))))

  (defthm equiv-ev-context-equiv-trace-implies-first
    (implies (and (equiv-ev-context-equiv-trace contexts trace)
                  (consp (cdr trace)))
             (equiv-ev-context-equiv-symm contexts (car trace) (cadr trace))))

  (defthm equiv-ev-context-equiv-trace-of-single
    (equiv-ev-context-equiv-trace contexts (list x)))

  (defthm equiv-ev-context-equiv-trace-of-two
    (iff (equiv-ev-context-equiv-trace contexts (list x y))
         (equiv-ev-context-equiv-symm contexts x y)))

  (local (defthm not-equiv-ev-context-equiv-trace-of-append-1
           (implies (not (equiv-ev-context-equiv-trace ctx trace1))
                    (not (equiv-ev-context-equiv-trace ctx (append trace1 trace2))))))

  ;; (local (defthm not-equiv-ev-context-equiv-trace-of-append-2
  ;;          (implies (not (equiv-ev-context-equiv-trace ctx trace2))
  ;;                   (not (equiv-ev-context-equiv-trace ctx (append trace1 trace2))))))

  ;; (local (defthm not-equiv-ev-context-equiv-trace-of-append-3
  ;;          (implies (and (consp trace1) (consp trace2)
  ;;                        (not (equiv-ev-context-equiv-symm ctx (car (last trace1)) (car trace2))))
  ;;                   (not (equiv-ev-context-equiv-trace ctx (append trace1 trace2))))))

  (local (defthm not-equiv-ev-context-equiv-trace-of-append-4
           (implies (and (consp trace1) (consp trace2)
                         (not (equiv-ev-context-equiv-symm ctx (car trace2) (car (last trace1)))))
                    (not (equiv-ev-context-equiv-trace ctx (append trace1 trace2))))))

  (defthm equiv-ev-context-equiv-trace-of-rev
    (iff (equiv-ev-context-equiv-trace ctx (acl2::rev trace))
         (equiv-ev-context-equiv-trace ctx trace))
    :hints(("Goal" :in-theory (enable acl2::rev))))

  (defthmd equiv-ev-context-equiv-trace-by-singleton
    (implies (and (equiv-ev-context-equiv-trace (list equiv) trace)
                  (member (pseudo-fnsym-fix equiv) (equiv-contexts-fix ctx)))
             (equiv-ev-context-equiv-trace ctx trace))
    :hints(("Goal" :in-theory (enable equiv-ev-context-equiv-symm-by-singleton))))

  (local (in-theory (enable true-list-fix)))

  (defthmd equiv-ev-context-equiv-trace-of-singleton
    (implies (and (equiv-ev-theoremp (equiv-rel-term equiv))
                  (not (equiv-ev (pseudo-term-fncall equiv (list (pseudo-term-quote (car trace))
                                                                 (pseudo-term-quote (car (last trace)))))
                                 nil)))
             (not (equiv-ev-context-equiv-trace (list equiv) trace)))
    :hints (("goal" :in-theory (enable equiv-ev-context-equiv-symm-of-singleton)
             :induct t)
            (and stable-under-simplificationp
                 '(:use ((:instance equiv-rel-term-implies-transitive
                          (fn (pseudo-fnsym-fix equiv))
                          (x (pseudo-term-quote (car trace)))
                          (y (pseudo-term-quote (cadr trace)))
                          (z (pseudo-term-quote (car (last trace))))
                          (a nil))
                         (:instance equiv-rel-term-implies-reflexive
                          (fn (pseudo-fnsym-fix equiv))
                          (x (pseudo-term-quote (car trace)))
                          (a nil)))))))


  (defthm equiv-ev-context-equiv-trace-of-append-contexts
    (implies (or (equiv-ev-context-equiv-trace ctx1 trace)
                 (equiv-ev-context-equiv-trace ctx2 trace))
             (equiv-ev-context-equiv-trace (append ctx1 ctx2) trace))))

;; The transitive/symmetric/reflexive closure of the OR of the equivalences.
(defsection equiv-ev-context-equiv
  (defun-sk equiv-ev-context-equiv1 (ctx x y)
    (exists trace
            (and (consp trace)
                 (true-listp trace)
                 (equal (car trace) x)
                 (equal (car (last trace)) y)
                 (equiv-ev-context-equiv-trace ctx trace))))

  (in-theory (disable equiv-ev-context-equiv1
                      equiv-ev-context-equiv1-suff))

  (define equiv-ev-context-equiv-witness ((ctx equiv-contextsp)
                                          x y)
    :returns (trace (and (consp trace) (true-listp trace)) :rule-classes :type-prescription)
    (let ((trace (true-list-fix (ec-call (equiv-ev-context-equiv1-witness (equiv-contexts-fix ctx) x y)))))
      (if (consp trace)
          trace
        (list x))))

  (define equiv-ev-context-equiv ((ctx equiv-contextsp)
                                  x y)
    (let ((trace (equiv-ev-context-equiv-witness ctx x y)))
      (and (equal (car trace) x)
           (equal (car (last trace)) y)
           (equiv-ev-context-equiv-trace ctx trace)))
    ///
    (defthm equiv-ev-context-equiv-suff
      (implies (and (equal (car trace) x)
                    (equal (car (last trace)) y)
                    (equiv-ev-context-equiv-trace ctx trace))
               (equiv-ev-context-equiv ctx x y))
      :hints(("Goal" :in-theory (enable equiv-ev-context-equiv-witness
                                        equiv-ev-context-equiv1)
              :use ((:instance equiv-ev-context-equiv1-suff
                     (trace (let ((trace (true-list-fix trace)))
                              (if (consp trace) trace (list x))))
                     (ctx (equiv-contexts-fix ctx))))
              :do-not-induct t))
      :otf-flg t))


  (defthm equiv-ev-context-equiv-reflexive
    (equiv-ev-context-equiv ctx x x)
    :hints (("goal" :use ((:instance equiv-ev-context-equiv-suff
                           (trace (list x)) (y x)))
             :in-theory (e/d ()))))

  (defthm equiv-ev-context-equiv-symmetric
    (implies (equiv-ev-context-equiv ctx x y)
             (equiv-ev-context-equiv ctx y x))
    :hints (("goal" :expand ((equiv-ev-context-equiv ctx x y))
             :use ((:instance equiv-ev-context-equiv-suff
                    (x y) (y x) (trace (acl2::rev (equiv-ev-context-equiv-witness ctx x y))))))))

  (defthm equiv-ev-context-equiv-transitive
    (implies (and (equiv-ev-context-equiv ctx x y)
                  (equiv-ev-context-equiv ctx y z))
             (equiv-ev-context-equiv ctx x z))
    :hints (("goal" :expand ((equiv-ev-context-equiv ctx x y)
                             (equiv-ev-context-equiv ctx y z))
             :use ((:instance equiv-ev-context-equiv-suff
                    (x x) (y z) (trace (append (equiv-ev-context-equiv-witness ctx x y)
                                               (equiv-ev-context-equiv-witness ctx y z))))))))

  (defthm equiv-ev-context-equiv-equal
    (equal (equiv-ev-context-equiv nil x y)
           (equal x y))
    :hints (("goal" :cases ((equiv-ev-context-equiv nil x y))
             :use ((:instance equiv-ev-context-equiv-suff (ctx nil) (trace (list x)))))
            (and stable-under-simplificationp
                 '(:expand ((equiv-ev-context-equiv nil x y))))))

  (defthmd equiv-ev-context-equiv-by-singleton
    (implies (and (equiv-ev-context-equiv (list equiv) x y)
                  (member (pseudo-fnsym-fix equiv) (equiv-contexts-fix ctx)))
             (equiv-ev-context-equiv ctx x y))
    :hints(("Goal" :expand ((equiv-ev-context-equiv (list equiv) x y))
            :in-theory (enable equiv-ev-context-equiv-trace-by-singleton)
            :use ((:instance equiv-ev-context-equiv-suff
                   (trace (equiv-ev-context-equiv-witness (list equiv) x y)))))))

  (defthmd equiv-ev-context-equiv-of-singleton
    (implies (equiv-ev-theoremp (equiv-rel-term equiv))
             (iff (equiv-ev-context-equiv (list equiv) x y)
                  (equiv-ev (pseudo-term-fncall equiv (list (pseudo-term-quote x)
                                                            (pseudo-term-quote y)))
                            nil)))
    :hints (("goal" :in-theory (enable equiv-ev-context-equiv-trace-of-singleton
                                       equiv-ev-context-equiv-symm-of-singleton)
             :use ((:instance equiv-ev-context-equiv-suff
                    (ctx (list equiv))
                    (trace (list x y))))
             :expand ((equiv-ev-context-equiv (list equiv) x y)
                      (equiv-ev-context-equiv-trace (list equiv) (list x y))))))

  (defthmd equiv-ev-context-equiv-when-singleton
    (implies (equiv-ev (pseudo-term-fncall equiv (list (pseudo-term-quote x)
                                                       (pseudo-term-quote y)))
                       nil)
             (equiv-ev-context-equiv (list equiv) x y))
    :hints (("goal" :in-theory (enable equiv-ev-context-equiv-trace-of-singleton
                                       equiv-ev-context-equiv-symm-when-singleton)
             :use ((:instance equiv-ev-context-equiv-suff
                    (ctx (list equiv))
                    (trace (list x y)))))))

  (fty::deffixcong equiv-contexts-equiv equal (equiv-ev-context-equiv ctx x y) ctx
    :hints (("goal"
             :cases ((equiv-ev-context-equiv ctx x y)))
            (and stable-under-simplificationp
                 (let* ((other (assoc 'equiv-ev-context-equiv clause))
                        (assum (if (equal (cadr other) 'ctx)
                                   '(equiv-ev-context-equiv (equiv-contexts-fix ctx) x y)
                                 '(equiv-ev-context-equiv ctx x y))))
                   `(:expand (,assum)
                     :use ((:instance equiv-ev-context-equiv-suff
                            (ctx ,(cadr other))
                            (trace (equiv-ev-context-equiv-witness . ,(cdr assum))))))))))

  (defthm equiv-ev-context-equiv-of-append-contexts
    (implies (or (equiv-ev-context-equiv ctx1 x y)
                 (equiv-ev-context-equiv ctx2 x y))
             (equiv-ev-context-equiv (append ctx1 ctx2) x y))
    :hints (("goal" :expand ((equiv-ev-context-equiv ctx1 x y)
                             (equiv-ev-context-equiv ctx2 x y))
             :use ((:instance equiv-ev-context-equiv-suff
                    (ctx (append ctx1 ctx2))
                    (trace (equiv-ev-context-equiv-witness ctx1 x y)))
                   (:instance equiv-ev-context-equiv-suff
                    (ctx (append ctx1 ctx2))
                    (trace (equiv-ev-context-equiv-witness ctx2 x y)))))))

  (defthmd equiv-ev-context-equiv-when-symm
    (implies (equiv-ev-context-equiv-symm ctx x y)
             (equiv-ev-context-equiv ctx x y))
    :hints (("Goal" :use ((:instance equiv-ev-context-equiv-suff
                           (trace (list x y))))
             :in-theory (e/d (equiv-ev-context-equiv-trace))))))

(defsection equiv-ev-context-fix

  (defchoose equiv-ev-context-fix1 (rep) (contexts x)
    (equiv-ev-context-equiv contexts x rep)
    :strengthen t)

  (define equiv-ev-context-fix ((contexts equiv-contextsp) x)
    :non-executable t
    (equiv-ev-context-fix1 (equiv-contexts-fix contexts) x)
    ///
    (in-theory (disable (equiv-ev-context-fix)))
    (defthm equiv-ev-context-fix-equiv
      (equiv-ev-context-equiv contexts x (equiv-ev-context-fix contexts x))
      :hints (("goal" :use ((:instance equiv-ev-context-fix1
                             (rep x)
                             (contexts (equiv-contexts-fix contexts)))))))

    (defthm equiv-ev-context-fix-strengthen
      (implies (equiv-ev-context-equiv contexts x y)
               (equal (equiv-ev-context-fix contexts x) (equiv-ev-context-fix contexts y)))
      :hints (("goal" :use ((:instance equiv-ev-context-fix1
                             (contexts1 (equiv-contexts-fix contexts))
                             (contexts (equiv-contexts-fix contexts))
                             (x1 y)
                             (rep y))
                            (:instance equiv-ev-context-equiv-transitive
                             (ctx contexts)
                             (x (equiv-ev-context-fix contexts x))
                             (y x) (z y))
                            (:instance equiv-ev-context-equiv-transitive
                             (ctx contexts)
                             (x (equiv-ev-context-fix contexts y))
                             (y y) (z x)))
               :in-theory (disable equiv-ev-context-equiv-transitive
                                   )))
      :rule-classes nil))

  (defthm equiv-ev-context-fix-equiv-rev
    (equiv-ev-context-equiv contexts (equiv-ev-context-fix contexts x) x))

  (defthmd equal-of-equiv-ev-context-fix
    (iff (equal (equiv-ev-context-fix contexts x) (equiv-ev-context-fix contexts y))
         (equiv-ev-context-equiv contexts x y))
    :hints (("goal"
             :use (equiv-ev-context-fix-strengthen
                   (:instance equiv-ev-context-fix-equiv)
                   (:instance equiv-ev-context-fix-equiv-rev (x y)))
             :in-theory (disable equiv-ev-context-fix-equiv-rev
                                 equiv-ev-context-fix-equiv))))

  (defthmd equiv-ev-context-equiv-is-equal-of-fixes
    (iff (equiv-ev-context-equiv contexts x y)
         (equal (equiv-ev-context-fix contexts x) (equiv-ev-context-fix contexts y)))
    :hints(("Goal" :in-theory (enable equal-of-equiv-ev-context-fix))))




  (defthm equiv-ev-context-fix-of-equiv-ev-context-fix
    (equal (equiv-ev-context-fix contexts (equiv-ev-context-fix contexts x))
           (equiv-ev-context-fix contexts x))
    :hints (("goal" :use ((:instance equiv-ev-context-fix-strengthen
                           (y (equiv-ev-context-fix contexts x)))))))

  (defthm equiv-ev-context-fix-under-equiv-ev-context-equiv-1
    (equal (equiv-ev-context-equiv contexts (equiv-ev-context-fix contexts x) y)
           (equiv-ev-context-equiv contexts x y))
    :hints(("Goal" :in-theory (enable equiv-ev-context-equiv-is-equal-of-fixes))))

  (defthm equiv-ev-context-fix-under-equiv-ev-context-equiv-2
    (equal (equiv-ev-context-equiv contexts x (equiv-ev-context-fix contexts y))
           (equiv-ev-context-equiv contexts x y))
    :hints(("Goal" :in-theory (enable equiv-ev-context-equiv-is-equal-of-fixes))))

  (defthm equiv-ev-context-fix-of-nil
    (equal (equiv-ev-context-fix nil x) x)
    :hints (("goal" :use ((:instance equiv-ev-context-fix-equiv (contexts nil)))
             :in-theory (disable equiv-ev-context-fix-equiv
                                 equiv-ev-context-fix-equiv-rev
                                 equiv-ev-context-fix-under-equiv-ev-context-equiv-1
                                 equiv-ev-context-fix-under-equiv-ev-context-equiv-2)))))


(defsection equiv-ev-equiv-contexts-refinement-p
  (defun-sk equiv-ev-equiv-contexts-refinement-p (sub super)
    (forall (x y)
            (implies (equiv-ev-context-equiv sub x y)
                     (equiv-ev-context-equiv super x y)))
    :rewrite :direct)

  (in-theory (disable equiv-ev-equiv-contexts-refinement-p
                      equiv-ev-equiv-contexts-refinement-p-necc))

  (defthm equiv-ev-equiv-contexts-refinement-p-when-member
    (implies (member (pseudo-fnsym-fix equiv) (equiv-contexts-fix super))
             (equiv-ev-equiv-contexts-refinement-p (list equiv) super))
    :hints(("Goal" :in-theory (enable equiv-ev-equiv-contexts-refinement-p
                                      equiv-ev-context-equiv-by-singleton))))

  (defthm equiv-ev-equiv-contexts-refinement-p-of-append-1
    (equiv-ev-equiv-contexts-refinement-p ctx1 (append ctx1 ctx2))
    :hints(("Goal" :in-theory (enable equiv-ev-equiv-contexts-refinement-p))))

  (defthm equiv-ev-equiv-contexts-refinement-p-of-append-2
    (equiv-ev-equiv-contexts-refinement-p ctx1 (append ctx1 ctx2))
    :hints(("Goal" :in-theory (enable equiv-ev-equiv-contexts-refinement-p)))))

(deflist equiv-contextslist :elt-type equiv-contexts :true-listp t)

(define equiv-ev-context-equiv-list ((contexts equiv-contextslist-p)
                                     (x true-listp)
                                     (y true-listp))
  (if (atom contexts)
      (acl2::nth-equiv-exec x y)
    (and (equiv-ev-context-equiv (car contexts) (car x) (car y))
         (equiv-ev-context-equiv-list (cdr contexts) (cdr x) (cdr y))))
  ///
  (local (in-theory (enable equiv-contextslist-fix true-list-fix)))

  (defthm equiv-ev-context-equiv-of-nth-when-equiv-ev-context-equiv-list
    (implies (equiv-ev-context-equiv-list contexts x y)
             (equiv-ev-context-equiv (nth n contexts) (nth n x) (nth n y)))
    :hints (("goal" :induct (list (nthcdr n contexts)
                                  (nthcdr n x)
                                  (nthcdr n y))
             :in-theory (enable acl2::nth-equiv-recursive))))

  (local (defthm update-nth-self-under-nth-equiv
           ;; (implies (< (nfix n) (len x))
           (acl2::nth-equiv (update-nth n (nth n x) (true-list-fix x))
                            x)
           :hints(("Goal" :in-theory (enable acl2::nth-equiv-recursive)))))

  (local (defthm nth-equiv-when-not-consp
           (implies (not (consp x))
                    (acl2::nth-equiv x nil))
           :hints(("Goal" :in-theory (enable acl2::nth-equiv)))
           :rule-classes :forward-chaining))

  (local (defthm nth-equiv-when-single-nil
           (acl2::nth-equiv '(nil) nil)
           :hints(("Goal" :in-theory (enable acl2::nth-equiv-recursive)))))

  (defthm equiv-ev-context-equiv-list-of-update-nth-1
    (implies (and (equiv-ev-context-equiv-list contexts x y)
                  (equiv-ev-context-equiv (nth n contexts) (nth n x) val)
                  ;; (< (nfix n) (len contexts))
                  )
             (equiv-ev-context-equiv-list contexts (update-nth n val x) y))
    :hints (("goal" :induct (list (nthcdr n contexts)
                                  (nthcdr n x)
                                  (nthcdr n y))
             :expand ((:free (x y) (equiv-ev-context-equiv-list contexts x y))))
            (and stable-under-simplificationp
                 '(:use ((:instance equiv-ev-context-equiv-transitive
                          (ctx (car contexts))
                          (x (car y))
                          (y (car x))
                          (z val)))
                   :in-theory (disable equiv-ev-context-equiv-transitive)))))

  (defthmd equiv-ev-context-equiv-list-transitive
    (implies (and (equiv-ev-context-equiv-list contexts x y)
                  (equiv-ev-context-equiv-list contexts y z))
             (equiv-ev-context-equiv-list contexts x z)))

  (defthmd equiv-ev-context-equiv-list-transitive2
    (implies (and (equiv-ev-context-equiv-list contexts y z)
                  (equiv-ev-context-equiv-list contexts x y))
             (equiv-ev-context-equiv-list contexts x z)))

  (defthm equiv-ev-context-equiv-list-symm
    (implies (equiv-ev-context-equiv-list contexts x y)
             (equiv-ev-context-equiv-list contexts y x)))

  (defthm equiv-ev-context-equiv-list-of-nil
    (equal (equiv-ev-context-equiv-list nil x y)
           (acl2::nth-equiv x y)))

  (defthm equiv-ev-context-equiv-list-self
    (equiv-ev-context-equiv-list contexts x x))

  (defcong acl2::nth-equiv equal (equiv-ev-context-equiv-list contexts x y) 2)
  (defcong acl2::nth-equiv equal (equiv-ev-context-equiv-list contexts x y) 3))

(defsection equiv-ev-context-fix-list

  (defchoose equiv-ev-context-fix-list1 (rep) (contexts x)
    (equiv-ev-context-equiv-list contexts x rep)
    :strengthen t)

  (define equiv-ev-context-fix-list ((contexts equiv-contextslist-p)
                                     (x true-listp))
    :non-executable t
    (true-list-fix
     (equiv-ev-context-fix-list1 (equiv-contextslist-fix contexts)
                                 (true-list-fix x)))
    ///
    (in-theory (disable (equiv-ev-context-fix-list)))
    (defthm equiv-ev-context-fix-list-equiv
      (equiv-ev-context-equiv-list contexts x (equiv-ev-context-fix-list contexts x))
      :hints (("goal" :use ((:instance equiv-ev-context-fix-list1
                             (rep (true-list-fix x))
                             (x (true-list-fix x))
                             (contexts (equiv-contextslist-fix contexts)))))))

    (defthm equiv-ev-context-fix-list-strengthen
      (implies (equiv-ev-context-equiv-list contexts x y)
               (equal (equiv-ev-context-fix-list contexts x) (equiv-ev-context-fix-list contexts y)))
      :hints (("goal" :use ((:instance equiv-ev-context-fix-list1
                             (contexts1 (equiv-contextslist-fix contexts))
                             (contexts (equiv-contextslist-fix contexts))
                             (x1 (true-list-fix y))
                             (x (true-list-fix x))
                             (rep (true-list-fix y)))
                            (:instance equiv-ev-context-equiv-list-transitive
                             (x (equiv-ev-context-fix-list contexts x))
                             (y x) (z y))
                            (:instance equiv-ev-context-equiv-list-transitive
                             (x (equiv-ev-context-fix-list contexts y))
                             (y y) (z x)))
               :in-theory (disable equiv-ev-context-equiv-list-transitive
                                   )))
      :rule-classes nil))

  (defthm equiv-ev-context-fix-list-equiv-rev
    (equiv-ev-context-equiv-list contexts (equiv-ev-context-fix-list contexts x) x))

  (defthmd equal-of-equiv-ev-context-fix-list
    (iff (equal (equiv-ev-context-fix-list contexts x) (equiv-ev-context-fix-list contexts y))
         (equiv-ev-context-equiv-list contexts x y))
    :hints (("goal"
             :use (equiv-ev-context-fix-list-strengthen
                   (:instance equiv-ev-context-fix-list-equiv)
                   (:instance equiv-ev-context-fix-list-equiv-rev (x y)))
             :in-theory (e/d (equiv-ev-context-equiv-list-transitive)
                             (equiv-ev-context-fix-list-equiv-rev
                              equiv-ev-context-fix-list-equiv)))))

  (defthmd equiv-ev-context-equiv-list-is-equal-of-fixes
    (iff (equiv-ev-context-equiv-list contexts x y)
         (equal (equiv-ev-context-fix-list contexts x) (equiv-ev-context-fix-list contexts y)))
    :hints(("Goal" :in-theory (enable equal-of-equiv-ev-context-fix-list))))




  (defthm equiv-ev-context-fix-list-of-equiv-ev-context-fix-list
    (equal (equiv-ev-context-fix-list contexts (equiv-ev-context-fix-list contexts x))
           (equiv-ev-context-fix-list contexts x))
    :hints (("goal" :use ((:instance equiv-ev-context-fix-list-strengthen
                           (y (equiv-ev-context-fix-list contexts x)))))))

  (defthm equiv-ev-context-fix-list-under-equiv-ev-context-equiv-list-1
    (equal (equiv-ev-context-equiv-list contexts (equiv-ev-context-fix-list contexts x) y)
           (equiv-ev-context-equiv-list contexts x y))
    :hints(("Goal" :in-theory (enable equiv-ev-context-equiv-list-is-equal-of-fixes))))

  (defthm equiv-ev-context-fix-list-under-equiv-ev-context-equiv-list-2
    (equal (equiv-ev-context-equiv-list contexts x (equiv-ev-context-fix-list contexts y))
           (equiv-ev-context-equiv-list contexts x y))
    :hints(("Goal" :in-theory (enable equiv-ev-context-equiv-list-is-equal-of-fixes))))

  (defthm equiv-ev-context-fix-list-of-nil
    (acl2::nth-equiv (equiv-ev-context-fix-list nil x) x)
    :hints (("goal" :use ((:instance equiv-ev-context-fix-list-equiv (contexts nil)))
             :in-theory (disable equiv-ev-context-fix-list-equiv
                                 equiv-ev-context-fix-list-equiv-rev
                                 equiv-ev-context-fix-list-under-equiv-ev-context-equiv-list-1
                                 equiv-ev-context-fix-list-under-equiv-ev-context-equiv-list-2)))))


(local (defthm true-list-fix-when-true-listp
         (implies (true-listp x)
                  (equal (true-list-fix x) x))
         :hints(("Goal" :in-theory (enable true-list-fix)))))






(define equiv-ev-context-equiv-list-step-p ((contexts equiv-contextslist-p)
                                            (x true-listp)
                                            (y true-listp))
  (if (atom contexts)
      (acl2::nth-equiv-exec x y)
    (if (equal (car x) (car y))
        (equiv-ev-context-equiv-list-step-p (cdr contexts) (cdr x) (cdr y))
      (and (equiv-ev-context-equiv-symm (car contexts) (car x) (car y))
           (acl2::nth-equiv-exec (cdr x) (cdr y)))))
  ///
  (defthm equiv-ev-context-equiv-list-step-p-same
    (equiv-ev-context-equiv-list-step-p contexts x x))

  (defthm equiv-ev-context-equiv-list-step-p-of-update-nth
    (implies (equiv-ev-context-equiv-symm (nth n contexts) a b)
             (equiv-ev-context-equiv-list-step-p contexts
                                                 (update-nth n a x)
                                                 (update-nth n b x)))
    :hints(("Goal" :in-theory (enable nth update-nth)
            :induct (list (nthcdr n contexts)
                          (nthcdr n x))
            :expand ((:free (x y) (equiv-ev-context-equiv-list-step-p contexts x y))
                     (nth n contexts)
                     (update-nth n a x)
                     (update-nth n b x)))))

  (defcong acl2::nth-equiv equal (equiv-ev-context-equiv-list-step-p contexts x y) 2
    :hints(("Goal" :in-theory (enable acl2::nth-equiv-recursive))))


  (defthm equiv-ev-context-equiv-list-when-step-p
    (implies (equiv-ev-context-equiv-list-step-p contexts x y)
             (equiv-ev-context-equiv-list contexts x y))
    :hints (("goal" :induct (equiv-ev-context-equiv-list contexts x y)
             :in-theory (enable equiv-ev-context-equiv-when-symm
                                equiv-ev-context-equiv-list)
             :expand ((equiv-ev-context-equiv-list-step-p contexts x y))))))

(define equiv-ev-context-equiv-list-trace ((contexts equiv-contextslist-p)
                                           (trace true-list-listp))
  (if (atom (cdr trace))
      t
    (and (equiv-ev-context-equiv-list-step-p contexts (car trace) (cadr trace))
         (equiv-ev-context-equiv-list-trace contexts (cdr trace))))
  ///
  (defthm equiv-ev-context-equiv-list-trace-of-nil
    (equiv-ev-context-equiv-list-trace contexts nil))

  (defthm equiv-ev-context-equiv-list-trace-of-single
    (equiv-ev-context-equiv-list-trace contexts (list x)))

  (local (defthm true-list-equiv-forward
           (implies (equal (true-list-fix x) (true-list-fix y))
                    (list-equiv x y))
           :hints(("Goal" :in-theory (enable list-equiv)))
           :rule-classes :forward-chaining))

  (defthm equiv-ev-context-equiv-list-trace-of-append
    (implies (and (equiv-ev-context-equiv-list-trace contexts x)
                  (equiv-ev-context-equiv-list-trace contexts y)
                  (double-rewrite (acl2::nth-equiv (car (last x))
                                                   (car y))))
             (equiv-ev-context-equiv-list-trace contexts (append x y))))

  (defthm equiv-ev-context-equiv-list-when-trace
    (implies (equiv-ev-context-equiv-list-trace contexts trace)
             (equiv-ev-context-equiv-list contexts (car trace) (car (last trace))))
    :hints (("goal" :induct (equiv-ev-context-equiv-list-trace contexts trace)
             :in-theory (e/d (equiv-ev-context-equiv-list-trace
                              equiv-ev-context-equiv-list-transitive2)
                             (equiv-ev-context-equiv-list))))))

(define all-lengthsp ((n natp) (x true-listp))
  (if (atom x)
      t
    (and (equal (len (car x)) (lnfix n))
         (all-lengthsp n (cdr x))))
  ///
  (defthm all-lengthsp-of-cons
    (equal (all-lengthsp n (cons a b))
           (and (equal (len a) (nfix n))
                (all-lengthsp n b))))
  (defthm all-lengthsp-of-append
    (equal (all-lengthsp n (append a b))
           (and (all-lengthsp n a)
                (all-lengthsp n b))))

  (defthm all-lengthsp-of-nil
    (all-lengthsp n nil)))


(define equiv-ev-context-equiv-trace-to-list-trace ((trace true-listp)
                                                    (index natp)
                                                    (x true-listp))
  :returns (listtrace)
  (if (atom trace)
      nil
    (cons (update-nth index (car trace) (true-list-fix x))
          (equiv-ev-context-equiv-trace-to-list-trace (cdr trace) index x)))
  ///
  (defthm last-of-equiv-ev-context-equiv-trace-to-list-trace
    (implies (consp trace)
             (equal (car (last (equiv-ev-context-equiv-trace-to-list-trace trace index x)))
                    (update-nth index (car (last trace)) (true-list-fix x)))))

  (defthm car-of-equiv-ev-context-equiv-trace-to-list-trace
    (implies (consp trace)
             (equal (car (equiv-ev-context-equiv-trace-to-list-trace trace index x))
                    (update-nth index (car trace) (true-list-fix x)))))

  (defthm consp-of-equiv-ev-context-equiv-trace-to-list-trace
    (equal (consp (equiv-ev-context-equiv-trace-to-list-trace trace index x))
           (consp trace)))

  (defthm equiv-ev-context-equiv-trace-to-list-trace-correct
    (implies (equiv-ev-context-equiv-trace (nth index contexts) trace)
             (equiv-ev-context-equiv-list-trace
              contexts
              (equiv-ev-context-equiv-trace-to-list-trace trace index x)))
    :hints(("Goal" :in-theory (enable equiv-ev-context-equiv-list-trace
                                      equiv-ev-context-equiv-trace))))

  (defret all-lengthsp-of-<fn>
    (implies (< (nfix index) (len x))
             (all-lengthsp (len x) listtrace))))


(local (defthm nth-of-equiv-contextslist-fix-local
         (equal (nth n (equiv-contextslist-fix x))
                (equiv-contexts-fix (nth n x)))))

(local (defthm equiv-contexts-p-nth-of-equiv-contextslist-p
         (implies (equiv-contextslist-p x)
                  (equiv-contextsp (nth n x)))))

(local (defthm nth-of-true-list-fix
         (equal (nth n (true-list-fix x))
                (nth n x))))

(local (defthm true-list-fix-of-update-nth
         (equal (true-list-fix (update-nth n v x))
                (update-nth n v (true-list-fix x)))))

(define equiv-ev-context-equiv-list-witness-aux ((n natp)
                                                 (contexts equiv-contextslist-p)
                                                 (x true-listp)
                                                 (y true-listp))
  :returns (listtrace)
  (if (zp n)
      (list (true-list-fix x))
    (b* ((n (1- n))
         (ctx (nth n contexts))
         (xn (nth n x))
         (yn (nth n y))
         (new-x (update-nth n (nth n y) x)))
      (append (equiv-ev-context-equiv-trace-to-list-trace
               (equiv-ev-context-equiv-witness ctx xn yn)
               n x)
              (equiv-ev-context-equiv-list-witness-aux n contexts new-x y))))
  ///
  (local (defthm update-nth-self-under-nth-equiv
           ;; (implies (< (nfix n) (len x))
           (acl2::nth-equiv (update-nth n (nth n x) (true-list-fix x))
                            x)
           :hints(("Goal" :in-theory (enable acl2::nth-equiv-recursive)))))
  (local (defthm len-of-update-nth-when-less
           (implies (< (nfix n) (len x))
                    (equal (len (update-nth n v x)) (len x)))))
  (local (in-theory (disable len-update-nth)))



  (defthm car-of-equiv-ev-context-equiv-list-witness-aux
    (implies (and (equiv-ev-context-equiv-list contexts x y)
                  ;; (<= (nfix n) (len contexts))
                  ;; (<= (nfix n) (len x))
                  ;; (<= (nfix n) (len y))
                  )
             (acl2::nth-equiv (car (equiv-ev-context-equiv-list-witness-aux n contexts x y))
                              x))
    :hints (("goal" :induct (equiv-ev-context-equiv-list-witness-aux n contexts x y))
            (and stable-under-simplificationp
                 '(:use ((:instance equiv-ev-context-equiv-of-nth-when-equiv-ev-context-equiv-list
                          (n (+ -1 n))
                          (contexts (equiv-contextslist-fix contexts))))
                   :in-theory (e/d (equiv-ev-context-equiv)
                                   (equiv-ev-context-equiv-of-nth-when-equiv-ev-context-equiv-list
                                    EQUIV-EV-CONTEXT-EQUIV-EQUIV-CONTEXTS-EQUIV-CONGRUENCE-ON-CTX
                                    EQUIV-EV-CONTEXT-EQUIV-OF-EQUIV-CONTEXTS-FIX-CTX))
                   :do-not-induct t))))

  (local (defthm nthcdr-of-update-nth
           (equal (nthcdr n (update-nth n v x))
                  (cons v (nthcdr (+ 1 (nfix n)) x)))
           :hints(("Goal" :in-theory (disable acl2::nthcdr-of-cdr)))))

  (local (defthm expand-nthcdr-of-one-less
           (implies (not (zp n))
                    (acl2::nth-equiv (nthcdr (+ -1 n) y)
                                     (cons (nth (+ -1 n) y)
                                           (nthcdr n y))))
           :hints(("Goal" :in-theory (enable acl2::nth-equiv-recursive)))))

  (local (Defthm car-of-nthcdr
           (equal (car (nthcdr n x))
                  (nth n x))))

  (defthm car-last-of-equiv-ev-context-equiv-list-witness-aux
    (implies (and (equiv-ev-context-equiv-list contexts x y)
                  ;; (<= (nfix n) (len contexts))
                  ;; (<= (nfix n) (len x))
                  ;; (<= (nfix n) (len y))
                  (acl2::nth-equiv (nthcdr n x) (nthcdr n y)))
             (acl2::nth-equiv (car (last (equiv-ev-context-equiv-list-witness-aux n contexts x y)))
                        y))
    :hints (("goal" :induct (equiv-ev-context-equiv-list-witness-aux n contexts x y))
            (and stable-under-simplificationp
                 '(:use ((:instance equiv-ev-context-equiv-of-nth-when-equiv-ev-context-equiv-list
                          (n (+ -1 n))
                          (contexts (equiv-contextslist-fix contexts))))
                   :expand ((:with acl2::nth-equiv-recursive
                             (:free (a b c) (acl2::nth-equiv (cons a b) c))))
                   :in-theory (e/d (equiv-ev-context-equiv)
                                   (equiv-ev-context-equiv-of-nth-when-equiv-ev-context-equiv-list
                                    EQUIV-EV-CONTEXT-EQUIV-EQUIV-CONTEXTS-EQUIV-CONGRUENCE-ON-CTX
                                    EQUIV-EV-CONTEXT-EQUIV-OF-EQUIV-CONTEXTS-FIX-CTX))
                   :do-not-induct t))))

  (defthm equiv-ev-context-equiv-list-trace-of-equiv-ev-context-equiv-list-witness-aux
    (implies (and (equiv-ev-context-equiv-list contexts x y)
                  ;; (<= (nfix n) (len contexts))
                  ;; (<= (nfix n) (len x))
                  ;; (<= (nfix n) (len y))
                  )
             (equiv-ev-context-equiv-list-trace
              contexts
              (equiv-ev-context-equiv-list-witness-aux n contexts x y)))
    :hints (("goal" :induct (equiv-ev-context-equiv-list-witness-aux n contexts x y))
            (and stable-under-simplificationp
                 '(:use ((:instance equiv-ev-context-equiv-of-nth-when-equiv-ev-context-equiv-list
                          (n (+ -1 n))
                          (contexts (equiv-contextslist-fix contexts))))
                   :in-theory (e/d (equiv-ev-context-equiv)
                                   (equiv-ev-context-equiv-of-nth-when-equiv-ev-context-equiv-list
                                    EQUIV-EV-CONTEXT-EQUIV-EQUIV-CONTEXTS-EQUIV-CONGRUENCE-ON-CTX
                                    EQUIV-EV-CONTEXT-EQUIV-OF-EQUIV-CONTEXTS-FIX-CTX))
                   :do-not-induct t))))

  (defret all-lengthsp-of-<fn>
    (implies (<= (nfix n) (len x))
             (all-lengthsp (len x) listtrace))))

(define equiv-ev-context-equiv-list-witness ((contexts equiv-contextslist-p)
                                             (x true-listp)
                                             (y true-listp))
  :returns (listtrace)
  (equiv-ev-context-equiv-list-witness-aux (len contexts)
                                           contexts x y)
  ///
  (local (defthm equiv-ev-context-equiv-list-implies-nthcdr-same
           (implies (equiv-ev-context-equiv-list contexts x y)
                    (acl2::nth-equiv (nthcdr (len contexts) x)
                                     (nthcdr (len contexts) y)))
           :hints(("Goal" :in-theory (enable equiv-ev-context-equiv-list list-equiv
                                             acl2::nth-equiv-recursive)))))

  ;; (local (defthm nthcdr-nest
  ;;          (equal (nthcdr n (nthcdr m x))
  ;;                 (nthcdr (+ (nfix n) (nfix m)) x))))

  (local (defthm plus-minus
           (equal (+ n (- n) x)
                  (fix x))))

  (local (defthm equiv-ev-context-equiv-list-implies-nthcdr-same-gen
           (implies (and (equiv-ev-context-equiv-list contexts x y)
                         (<= (len contexts) (nfix n)))
                    (acl2::nth-equiv (nthcdr n x)
                                     (nthcdr n y)))
           :hints(("Goal" :use ((:instance acl2::nthcdr-of-nthcdr (a (- (nfix n) (len contexts)))
                                 (b (len contexts)) (x x))
                                (:instance acl2::nthcdr-of-nthcdr (a (- (nfix n) (len contexts)))
                                 (b (len contexts)) (x y))
                                (:instance equiv-ev-context-equiv-list-implies-nthcdr-same))
                   :in-theory (disable acl2::nthcdr-of-nthcdr
                                       acl2::nthcdr-of-cdr
                                       equiv-ev-context-equiv-list-implies-nthcdr-same)))))

  (defthm equiv-ev-context-equiv-list-necc
    (implies (equiv-ev-context-equiv-list contexts x y)
             (let ((trace (equiv-ev-context-equiv-list-witness contexts x y)))
               (and (acl2::nth-equiv (car trace) x)
                    (acl2::nth-equiv (car (last trace)) y)
                    (equiv-ev-context-equiv-list-trace contexts trace)))))

  (defret all-lengthsp-of-<fn>
    (implies (<= (len contexts) (len x))
             (all-lengthsp (len x) listtrace))))



(define join-equiv-contexts ((x equiv-contextsp)
                             (y equiv-contextsp))
  :enabled t
  (mbe :logic (append (equiv-contexts-fix x) (equiv-contexts-fix y))
       :exec
       (cond ((atom x) y)
             ((atom y) x)
             (t (append x y)))))

(define join-equiv-contextslists ((x equiv-contextslist-p)
                                  (y equiv-contextslist-p))
  :returns (union equiv-contextslist-p)
  (cond ((atom x) (equiv-contextslist-fix y))
        ((atom y) (equiv-contextslist-fix x))
        (t (cons (join-equiv-contexts (equiv-contexts-fix (car x))
                                      (equiv-contexts-fix (car y)))
                 (join-equiv-contextslists (cdr x) (cdr y)))))
  ///
  (local (in-theory (enable join-equiv-contextslists)))

  (defthm equiv-ev-context-equiv-list-step-p-of-join-equiv-contextslists
    (iff (equiv-ev-context-equiv-list-step-p (join-equiv-contextslists ctx1 ctx2) x y)
         (or (equiv-ev-context-equiv-list-step-p ctx1 x y)
             (equiv-ev-context-equiv-list-step-p ctx2 x y)))
    :hints(("Goal" :in-theory (enable equiv-ev-context-equiv-list-step-p)))))


(local (defthm kwote-lst-redef
         (equal (kwote-lst x)
                (if (atom x)
                    nil
                  (cons (pseudo-term-quote (car x))
                        (kwote-lst (cdr x)))))
         :hints(("Goal" :in-theory (enable kwote-lst pseudo-term-quote)))
         :rule-classes ((:definition :controller-alist ((kwote-lst t))))))

(local (defthm pseudo-term-listp-of-kwote-lst
         (pseudo-term-listp (kwote-lst x))))

(local (in-theory (disable (:d kwote-lst))))

(defsection equiv-ev-congruence-correct-p



  (defun-sk equiv-ev-congruence-correct-p1 (ctx fn arg-ctxs arity)
    (forall (args1 args2)
            (implies (and (equiv-ev-context-equiv-list arg-ctxs args1 args2)
                          (equal (len args1) (nfix arity))
                          (equal (len args2) (nfix arity)))
                     (equiv-ev-context-equiv ctx
                                             (equiv-ev (pseudo-term-fncall fn (kwote-lst args1)) nil)
                                             (equiv-ev (pseudo-term-fncall fn (kwote-lst args2)) nil))))
    :rewrite :direct)

  (in-theory (disable equiv-ev-congruence-correct-p1
                      equiv-ev-congruence-correct-p1-necc))




  (define equiv-ev-congruence-correct-p-witness ((ctx equiv-contextsp)
                                         (fn pseudo-fnsym-p)
                                         (arg-ctxs equiv-contextslist-p)
                                         (arity natp))
    :returns (mv (args1 true-listp :rule-classes :type-prescription)
                 (args2 true-listp :rule-classes :type-prescription))
    (b* (((mv args1 args2) (ec-call (equiv-ev-congruence-correct-p1-witness
                                     (equiv-contexts-fix ctx)
                                     (pseudo-fnsym-fix fn)
                                     (equiv-contextslist-fix arg-ctxs)
                                     (lnfix arity)))))
      (mbe :logic (mv (take arity args1)
                      (take arity args2))
           :exec (mv (take arity (true-list-fix args1))
                     (take arity (true-list-fix args2)))))
    ///
    (defret len-of-<fn>
      (and (equal (len args1) (nfix arity))
           (equal (len args2) (nfix arity)))))

  (local (defthm len-equal-0
           (equal (Equal (len x) 0)
                  (not (consp x)))))

  (local (defthm take-of-len-gen
           (implies (equal (nfix n) (len x))
                    (equal (take n x)
                           (true-list-fix x)))))

  (local (defthm kwote-lst-of-true-list-fix
           (Equal (kwote-lst (true-list-fix x)) (kwote-lst x))))

  (define equiv-ev-congruence-correct-p ((ctx equiv-contextsp)
                                         (fn pseudo-fnsym-p)
                                         (arg-ctxs equiv-contextslist-p)
                                         (arity natp))
    (b* (((mv args1 args2) (equiv-ev-congruence-correct-p-witness ctx fn arg-ctxs arity)))
      (implies (equiv-ev-context-equiv-list arg-ctxs args1 args2)
               (equiv-ev-context-equiv ctx
                                       (equiv-ev (pseudo-term-fncall fn (kwote-lst args1)) nil)
                                       (equiv-ev (pseudo-term-fncall fn (kwote-lst args2)) nil))))
    ///
    (defthmd equiv-ev-congruence-correct-p-necc
      (implies (and (equiv-ev-congruence-correct-p ctx fn arg-ctxs arity)
                    (equiv-ev-context-equiv-list arg-ctxs args1 args2)
                    (equal (len args1) (nfix arity))
                    (equal (len args2) (nfix arity)))
               (equiv-ev-context-equiv ctx
                                       (equiv-ev (pseudo-term-fncall fn (kwote-lst args1)) nil)
                                       (equiv-ev (pseudo-term-fncall fn (kwote-lst args2)) nil)))
      :hints(("Goal" :in-theory (enable equiv-ev-congruence-correct-p-witness
                                        equiv-ev-congruence-correct-p1)
              :use ((:instance equiv-ev-congruence-correct-p1-necc
                     (args1 args1)
                     (args2 args2)
                     (fn (pseudo-fnsym-fix fn))
                     (arg-ctxs (equiv-contextslist-fix arg-ctxs))
                     (arity (len args1))
                     (ctx (equiv-contexts-fix ctx))))
              :do-not-induct t))
      :otf-flg t))

  (local
   (defthm equiv-ev-congruence-correct-p-of-join-equiv-contextslists-trace
     (let ((arg-ctxs (join-equiv-contextslists arg-ctxs1 arg-ctxs2)))
       (implies (and (equiv-ev-congruence-correct-p ctx fn arg-ctxs1 arity)
                     (equiv-ev-congruence-correct-p ctx fn arg-ctxs2 arity)
                     (equiv-ev-context-equiv-list-trace arg-ctxs trace)
                     (all-lengthsp arity trace)
                     (consp trace))
                (equiv-ev-context-equiv ctx
                                        (equiv-ev (pseudo-term-fncall fn (kwote-lst (car trace))) nil)
                                        (equiv-ev (pseudo-term-fncall fn (kwote-lst (car (last trace)))) nil))))
     :hints (("goal" :induct (equiv-ev-context-equiv-list-trace (join-equiv-contextslists arg-ctxs1 arg-ctxs2) trace)
              :in-theory (enable (:i equiv-ev-context-equiv-list-trace))
              :expand ((:free (arg-ctxs) (equiv-ev-context-equiv-list-trace arg-ctxs trace))
                       (all-lengthsp arity trace)
                       (all-lengthsp arity (cdr trace))))
             (and stable-under-simplificationp
                  '(:use ((:instance equiv-ev-congruence-correct-p-necc
                           (arg-ctxs arg-ctxs1) (args1 (car trace)) (args2 (cadr trace)) (arity (len (car trace))))
                          (:instance equiv-ev-congruence-correct-p-necc
                           (arg-ctxs arg-ctxs2) (args1 (car trace)) (args2 (cadr trace)) (arity (len (car trace))))))))))
  (local (defthm acl2::nth-equiv-when-same-length
           (implies (equal (len x) (len y))
                    (equal (acl2::nth-equiv x y)
                           (list-equiv x y)))
           :hints(("Goal" :in-theory (enable list-equiv
                                             acl2::nth-equiv-recursive
                                             acl2::nth-equiv-ind)))))

  (local (defthm len-of-car-when-all-lengthsp
           (implies (and (all-lengthsp n x)
                         (consp x))
                    (equal (len (car x)) (nfix n)))
           :hints(("Goal" :in-theory (enable all-lengthsp)))))

  (local (defthm len-of-car-last-when-all-lengthsp
           (implies (and (all-lengthsp n x)
                         (consp x))
                    (equal (len (car (last x))) (nfix n)))
           :hints(("Goal" :in-theory (enable all-lengthsp)))))

  (local (fty::deffixcong list-equiv equal (kwote-lst x) x))


  (local
   (defthm equiv-ev-congruence-correct-p-of-join-equiv-contextslists-lemma
    (let ((arg-ctxs (join-equiv-contextslists arg-ctxs1 arg-ctxs2)))
      (implies (and (equiv-ev-congruence-correct-p ctx fn arg-ctxs1 arity)
                    (equiv-ev-congruence-correct-p ctx fn arg-ctxs2 arity)
                    (equiv-ev-context-equiv-list arg-ctxs args1 args2)
                    (equal (len args1) (nfix arity))
                    (equal (len args2) (nfix arity))
                    (<= (len arg-ctxs) (nfix arity)))
               (equiv-ev-context-equiv ctx
                                       (equiv-ev (pseudo-term-fncall fn (kwote-lst args1)) nil)
                                       (equiv-ev (pseudo-term-fncall fn (kwote-lst args2)) nil))))
    :hints (("goal" :use ((:instance equiv-ev-context-equiv-list-necc
                           (contexts (join-equiv-contextslists arg-ctxs1 arg-ctxs2))
                           (x args1)
                           (y args2))
                          (:instance equiv-ev-congruence-correct-p-of-join-equiv-contextslists-trace
                           (trace (equiv-ev-context-equiv-list-witness
                                   (join-equiv-contextslists arg-ctxs1 arg-ctxs2)
                                   args1 args2)))
                          (:instance all-lengthsp-of-equiv-ev-context-equiv-list-witness
                           (contexts (join-equiv-contextslists arg-ctxs1 arg-ctxs2))
                           (x args1) (y args2)))
             :in-theory (acl2::e/d*
                         (acl2::arith-equiv-forwarding)
                         (equiv-ev-context-equiv-list-necc
                          all-lengthsp-of-equiv-ev-context-equiv-list-witness
                          equiv-ev-congruence-correct-p-of-join-equiv-contextslists-trace))))))

  (defthm equiv-ev-congruence-correct-p-of-join-equiv-contextslists
    (let ((arg-ctxs (join-equiv-contextslists arg-ctxs1 arg-ctxs2)))
      (implies (and (equiv-ev-congruence-correct-p ctx fn arg-ctxs1 arity)
                    (equiv-ev-congruence-correct-p ctx fn arg-ctxs2 arity)
                    (<= (len arg-ctxs) (nfix arity)))
               (equiv-ev-congruence-correct-p ctx fn arg-ctxs arity)))
    :hints (("goal" :in-theory (disable equiv-ev-when-pseudo-term-fncall
                                        equiv-ev-of-pseudo-term-fncall))
            (and stable-under-simplificationp
                 `(:expand ,(car (last clause)))))))

(defprod congruence-rule
  ((equiv-req pseudo-fnsym-p)
   (fn pseudo-fnsym-p)
   (arg-contexts equiv-contextslist-p)
   (arity natp :rule-classes :type-prescription))
  :layout :list)

(define equiv-ev-congruence-rule-correct-p ((rule congruence-rule-p))
  (b* (((congruence-rule rule)))
    (and (<= (len rule.arg-contexts) rule.arity)
         (ec-call (equiv-ev-congruence-correct-p (list rule.equiv-req)
                                                 rule.fn rule.arg-contexts rule.arity))))
  ///
  (defthm equiv-ev-congruence-rule-correct-implies
    (b* (((congruence-rule rule)))
      (implies (and (equiv-ev-congruence-rule-correct-p rule)
                    (member rule.equiv-req (equiv-contexts-fix contexts))
                    (equiv-ev-context-equiv-list rule.arg-contexts args1 args2)
                    (equal (len args1) rule.arity)
                    (equal (len args2) rule.arity))
               (equiv-ev-context-equiv contexts
                                       (equiv-ev (pseudo-term-fncall rule.fn (kwote-lst args1)) nil)
                                       (equiv-ev (pseudo-term-fncall rule.fn (kwote-lst args2)) nil))))
    :hints(("Goal" :in-theory (e/d (equiv-ev-congruence-correct-p-necc)
                                   (equiv-ev-of-pseudo-term-fncall
                                    equiv-ev-when-pseudo-term-fncall))
            :use ((:instance equiv-ev-context-equiv-by-singleton
                   (equiv (congruence-rule->equiv-req rule))
                   (x (equiv-ev (pseudo-term-fncall (congruence-rule->fn rule) (kwote-lst args1)) nil))
                   (y (equiv-ev (pseudo-term-fncall (congruence-rule->fn rule) (kwote-lst args2)) nil))
                   (ctx contexts)))))))


(define pseudo-term-var-listp ((x pseudo-term-listp))
  (if (atom x)
      t
    (and (pseudo-term-case (car x) :var)
         (pseudo-term-var-listp (cdr x))))
  ///
  (defthm pseudo-term-var-listp-of-cons
    (equal (pseudo-term-var-listp (cons a b))
           (and (pseudo-term-case a :var)
                (pseudo-term-var-listp b))))
  (defthm pseudo-term-var-listp-of-append
    (equal (pseudo-term-var-listp (append a b))
           (and (pseudo-term-var-listp a)
                (pseudo-term-var-listp b)))))

(local (defthm pseudo-term-list-fix-of-append
         (equal (pseudo-term-list-fix (append a b))
                (append (pseudo-term-list-fix a) (pseudo-term-list-fix b)))))

(local (defthm pseudo-term-list-fix-of-take
         (equal (pseudo-term-list-fix (take n x))
                (take n (pseudo-term-list-fix x)))))

(local (defthm pseudo-term-list-fix-of-nthcdr
         (equal (pseudo-term-list-fix (nthcdr n x))
                (nthcdr n (pseudo-term-list-fix x)))))

;; (define congruence-var-list-check-aux ((n natp) ;; index of var1 in vars
;;                                        (vars1 pseudo-term-listp)
;;                                        (vars2 pseudo-term-listp)
;;                                        (var2 pseudo-termp))
;;   ;; :prepwork ((local (defthm equal-of-cons
;;   ;;                     (equal (equal (cons a b) c)
;;   ;;                            (and (consp c)
;;   ;;                                 (equal a (car c))
;;   ;;                                 (equal b (cdr c)))))))
;;   :enabled t
;;   (mbe :logic (pseudo-term-list-equiv
;;                vars2
;;                (append (take n vars1)
;;                        (cons var2 (nthcdr (+ 1 (nfix n)) vars1))))
;;        :exec (cond ((atom vars2) nil)
;;                    ((zp n) (and (equal (car vars2) var2)
;;                                 (equal (cdr vars2) (cdr vars1))))
;;                    (t (and (equal (car vars1) (car vars2))
;;                            (congruence-var-list-check-aux (1- n) (cdr vars1) (cdr vars2) var2))))))


(define pseudo-term-var-list->names ((x pseudo-term-listp))
  :guard (pseudo-term-var-listp x)
  :returns (vars pseudo-var-list-p)
  :prepwork ((local (in-theory (enable pseudo-term-var-listp))))
  (if (atom x)
      nil
    (cons (pseudo-term-var->name (car x))
          (pseudo-term-var-list->names (cdr x))))
  ///
  (defthm pseudo-term-var-list->names-when-pseudo-term-listp
    (implies (and (pseudo-term-listp x)
                  (pseudo-term-var-listp x))
             (equal (pseudo-term-var-list->names x) x))
    :hints(("Goal" :in-theory (enable pseudo-termp
                                      pseudo-term-kind
                                      pseudo-term-var->name))))

  (local (defthm equiv-ev-list-of-acons-non-member
           (implies (and (pseudo-term-var-listp vars)
                         (pseudo-var-p var1)
                         (not (member var1 (pseudo-term-var-list->names vars))))
                    (equal (equiv-ev-list vars (cons (cons var1 val) rest))
                           (equiv-ev-list vars rest)))
           :hints(("Goal" :in-theory (enable pseudo-term-var-listp
                                             member
                                             pseudo-term-var-list->names
                                             pseudo-term-var->name
                                             pseudo-term-kind)))))

  (defthm equiv-ev-of-pair-pseudo-term-var-list->names-no-duplicates
    (implies (and (pseudo-term-var-listp vars)
                  (no-duplicatesp (pseudo-term-var-list->names vars)))
             (equal (equiv-ev-list vars (pairlis$ (pseudo-term-var-list->names vars) vals))
                    (take (len vars) vals)))
    :hints(("Goal" :in-theory (enable pseudo-term-var-listp)
            :induct (pairlis$ vars vals))))

  (local (in-theory (enable pseudo-term-list-fix)))


  (defthm pseudo-term-var-list->names-of-cons
    (equal (pseudo-term-var-list->names (cons a b))
           (cons (pseudo-term-var->name a)
                (pseudo-term-var-list->names b))))
  (defthm pseudo-term-var-list->names-of-append
    (equal (pseudo-term-var-list->names (append a b))
           (append (pseudo-term-var-list->names a)
                   (pseudo-term-var-list->names b)))))



(local (defthm symbol-listp-when-pseudo-term-var-listp
         (implies (and (pseudo-term-var-listp x)
                       (pseudo-term-listp x))
                  (symbol-listp x))
         :hints(("Goal" :in-theory (enable pseudo-term-var-listp
                                           pseudo-term-listp
                                           pseudo-termp
                                           pseudo-term-kind)))))

;; (define congruence-var-list-prefix ((vars1 pseudo-term-listp)
;;                                     (vars2 pseudo-term-listp)
;;                                     (var1 pseudo-termp)
;;                                     (var2 pseudo-termp))
;;   :ignore-ok t
;;   :irrelevant-formals-ok t
;;   :verify-guards nil
;;   (take (acl2::index-of (pseudo-term-fix var1) (pseudo-term-list-fix vars1))
;;         (pseudo-term-list-fix vars1)))

;; (define congruence-var-list-suffix ((vars1 pseudo-term-listp)
;;                                     (vars2 pseudo-term-listp)
;;                                     (var1 pseudo-termp)
;;                                     (var2 pseudo-termp))
;;   :ignore-ok t
;;   :irrelevant-formals-ok t
;;   :verify-guards nil
;;   (nthcdr (+ 1 (acl2::index-of (pseudo-term-fix var1) (pseudo-term-list-fix vars1)))
;;           (pseudo-term-list-fix vars1)))

;; (define congruence-var-list-check ((vars1 pseudo-term-listp)
;;                                    (vars2 pseudo-term-listp)
;;                                    (var1 pseudo-termp)
;;                                    (var2 pseudo-termp))
;;   (b* ((var1 (pseudo-term-fix var1))
;;        (var2 (pseudo-term-fix var2))
;;        (vars1 (pseudo-term-list-fix vars1))
;;        (vars2 (pseudo-term-list-fix vars2)))
;;     (and (pseudo-term-var-listp vars1)
;;          (pseudo-term-var-listp vars2)
;;          (b* ((index (acl2::index-of var1 vars1))
;;             ((unless index) nil))
;;            (and (congruence-var-list-check-aux index vars1 vars2 var2)
;;                 (mbe :logic (no-duplicatesp-eq (pseudo-term-var-list->names vars1))
;;                      :exec (no-duplicatesp-eq vars1))
;;                 (mbe :logic (no-duplicatesp-eq (pseudo-term-var-list->names vars2))
;;                      :exec (no-duplicatesp-eq vars2)))))))








(define congruence-var-list-check ((vars1 pseudo-term-listp)
                                   (vars2 pseudo-term-listp)
                                   (var1 pseudo-termp)
                                   (var2 pseudo-termp))
  :returns (n acl2::maybe-natp :rule-classes :type-prescription)
  (b* (((when (or (atom vars1) (atom vars2))) nil)
       (v1 (pseudo-term-fix (car vars1)))
       (v2 (pseudo-term-fix (car vars2)))
       ((when (equal v1 v2))
        (and (not (equal v1 (pseudo-term-fix var1)))
             (not (equal v1 (pseudo-term-fix var2)))
             (b* ((rest (congruence-var-list-check (cdr vars1) (cdr vars2) var1 var2)))
               (and rest (+ 1 rest))))))
    (and (or (and (equal (pseudo-term-fix var1) v1)
                  (equal (pseudo-term-fix var2) v2))
             ;; (and (equal (pseudo-term-fix var1) v2)
             ;;      (equal (pseudo-term-fix var2) v1))
             )
         (equal (pseudo-term-list-fix (cdr vars1))
                (pseudo-term-list-fix (cdr vars2)))
         0))

  ///
  (local (deffixcong pseudo-term-list-equiv equal (len x) x))

  (defthmd congruence-var-list-check-implies-len
    (implies (congruence-var-list-check vars1 vars2 var1 var2)
             (equal (len vars2) (len vars1)))
    :hints(("Goal" :in-theory (enable len))))

  (defret congruence-var-list-check-bound
    (implies n
             (and (< n (len vars1))
                  (< n (len vars2))))
    :rule-classes :linear)

  ;; (defund congruence-var-list-prefix (vars1 vars2 var1 var2)
  ;;   (take (congruence-var-list-check vars1 vars2 var1 var2) (pseudo-term-list-fix vars1)))

  ;; (defund congruence-var-list-suffix (vars1 vars2 var1 var2)
  ;;   (nthcdr (+ 1 (congruence-var-list-check vars1 vars2 var1 var2)) (pseudo-term-list-fix vars1)))

  ;; (local (include-book "std/lists/nthcdr" :dir :system))

  ;; (defret congruence-var-list-check-implies-vars1
  ;;   (iff n
  ;;        (b* ((prefix (take n vars1))
  ;;             (suffix (cdr (nthcdr n vars1))))
  ;;          (and (hide n)
  ;;               (pseudo-term-list-equiv vars1
  ;;                                       (append prefix (cons var1 suffix)))
  ;;               (pseudo-term-list-equiv vars2
  ;;                                       (append prefix (cons var2 suffix))))))
  ;;   :hints (("Goal" :expand ((:free (x) (hide x)))
  ;;            :induct <call>
  ;;            :in-theory (enable ;; congruence-var-list-prefix
  ;;                        ;; congruence-var-list-suffix
  ;;                        ;; nthcdr
  ;;                        pseudo-term-list-fix))))
  )





(local
 (define congruence-var-list-alist ((vars1 pseudo-term-listp)
                                    (vars2 pseudo-term-listp)
                                    (var1 pseudo-termp)
                                    (var2 pseudo-termp)
                                    (args1 true-listp)
                                    (args2 true-listp))
   :verify-guards nil
   :returns (alist)
   :prepwork ((local (in-theory (disable pseudo-term-listp take nthcdr
                                         pseudo-term-list-p-when-pseudo-var-list-p
                                         acl2::take-of-len-free))))
   (b* (((when (or (atom vars1) (atom vars2))) nil)
        (v1 (pseudo-term-fix (car vars1)))
        (v2 (pseudo-term-fix (car vars2)))
        ((when (equal v1 v2))
         (b* ((rest (congruence-var-list-alist (cdr vars1) (cdr vars2) var1 var2 (cdr args1) (cdr args2))))
           (cons (cons (pseudo-term-var->name v1) (car args1))
                 rest)))
        (rest (pairlis$ (pseudo-term-var-list->names (cdr vars1)) (cdr args1))))
     (cons (cons (pseudo-term-var->name v1) (car args1))
           (cons (cons (pseudo-term-var->name v2) (car args2))
                 rest)))
   ///
   (local (defthm equiv-ev-list-of-acons-non-member
            (implies (and (pseudo-term-var-listp vars)
                          (pseudo-var-p var1)
                          (not (member var1 (pseudo-term-var-list->names vars))))
                     (equal (equiv-ev-list vars (cons (cons var1 val) rest))
                            (equiv-ev-list vars rest)))
            :hints(("Goal" :in-theory (enable pseudo-term-var-listp
                                              member
                                              pseudo-term-var-list->names
                                              pseudo-term-var->name
                                              pseudo-term-kind)))))

   ;; (local (defthm take-of-len-gen
   ;;          (implies (equal len (len x))
   ;;                   (equal (take len x)
   ;;                          (true-list-fix x)))))

   (local (defthm pseudo-term-list-fix-equal-forward
            (implies (equal (pseudo-term-list-fix x) y)
                     (pseudo-term-list-equiv x y))))

   (local (defcong pseudo-term-list-equiv pseudo-term-equiv (car x) 1
            :hints(("Goal" :in-theory (enable pseudo-term-list-fix)))))

   (local (defthm pseudo-term-fix-equal-when-vars
            (implies (pseudo-term-case x :var)
                     (equal (equal (pseudo-term-fix x) y)
                            (and (pseudo-termp y)
                                 (pseudo-term-case y :var)
                                 (equal (pseudo-term-var->name x)
                                        (pseudo-term-var->name y)))))
            :hints (("goal" :use ((:instance acl2::pseudo-term-var-of-accessors
                                   (x x))
                                  (:instance acl2::pseudo-term-var-of-accessors
                                   (x y)))
                     :in-theory (disable acl2::pseudo-term-var-of-accessors)))))

   (local (defthm no-duplicatesp-of-pseudo-term-var-list->names-when-equal-pseudo-term-list-fix
            (implies (equal (pseudo-term-list-fix x) (append y z))
                     (equal (no-duplicatesp (pseudo-term-var-list->names x))
                            (no-duplicatesp (append (pseudo-term-var-list->names y)
                                                    (pseudo-term-var-list->names z)))))
            :hints (("Goal" :use ((:instance pseudo-term-var-list->names-of-append
                                   (a y) (b z)))
                     :in-theory (disable pseudo-term-var-list->names-of-append)
                     :do-not-induct t))))


   (defret congruence-var-list-alist-correct
     (b* ((index (congruence-var-list-check vars1 vars2 var1 var2)))
       (implies (and index
                     (pseudo-term-var-listp vars1)
                     (pseudo-term-var-listp vars2)
                     (no-duplicatesp-eq (pseudo-term-var-list->names vars1))
                     (no-duplicatesp-eq (pseudo-term-var-list->names vars2))
                     (pseudo-term-case var1 :var)
                     (pseudo-term-case var2 :var)
                     (not (equal (pseudo-term-fix var1)
                                 (pseudo-term-fix var2)))
                     (equal (take index args1) (take index args2))
                     (list-equiv (nthcdr (+ 1 index) args1)
                                 (nthcdr (+ 1 index) args2))
                     (equal (len args1) (len vars1))
                     (equal (len args2) (len vars1)))
                (and (list-equiv (equiv-ev-list vars1 alist) args1)
                     (list-equiv (equiv-ev-list vars2 alist) args2))))
     :hints (("goal" :in-theory (enable congruence-var-list-check
                                        equiv-ev-context-equiv-list
                                        update-nth
                                        pseudo-term-var-listp
                                        pseudo-term-var-list->names
                                        no-duplicatesp-eq
                                        true-list-fix
                                        list-equiv
                                        len)
              :induct <call>
              :expand ((:free (n x) (nthcdr (+ 1 n) x))
                       (:free (n x) (nthcdr (+ 2 n) x))
                       (:free (n x) (take (+ 1 n) x)) )
              :do-not-induct t)))

   (defret congruence-var-list-alist-var1-lookup
     (b* ((index (congruence-var-list-check vars1 vars2 var1 var2)))
       (implies (and index
                     (pseudo-term-var-listp vars1)
                     (pseudo-term-var-listp vars2)
                     (no-duplicatesp-eq (pseudo-term-var-list->names vars1))
                     (no-duplicatesp-eq (pseudo-term-var-list->names vars2))
                     (pseudo-term-case var1 :var)
                     (pseudo-term-case var2 :var)
                     (not (equal (pseudo-term-fix var1)
                                 (pseudo-term-fix var2))))
                (equal (cdr (assoc-equal (pseudo-term-var->name var1) alist))
                       (nth index args1))))
     :hints (("goal" :in-theory (enable congruence-var-list-check
                                        equiv-ev-context-equiv-list
                                        update-nth
                                        pseudo-term-var-listp
                                        pseudo-term-var-list->names
                                        no-duplicatesp-eq
                                        true-list-fix
                                        list-equiv
                                        len)
              :induct <call>
              :do-not-induct t)))

   (defret congruence-var-list-alist-var2-lookup
     (b* ((index (congruence-var-list-check vars1 vars2 var1 var2)))
       (implies (and index
                     (pseudo-term-var-listp vars1)
                     (pseudo-term-var-listp vars2)
                     (no-duplicatesp-eq (pseudo-term-var-list->names vars1))
                     (no-duplicatesp-eq (pseudo-term-var-list->names vars2))
                     (pseudo-term-case var1 :var)
                     (pseudo-term-case var2 :var)
                     (not (equal (pseudo-term-fix var1)
                                 (pseudo-term-fix var2))))
                (equal (cdr (assoc-equal (pseudo-term-var->name var2) alist))
                       (nth index args2))))
     :hints (("goal" :in-theory (enable congruence-var-list-check
                                        equiv-ev-context-equiv-list
                                        update-nth
                                        pseudo-term-var-listp
                                        pseudo-term-var-list->names
                                        no-duplicatesp-eq
                                        true-list-fix
                                        list-equiv
                                        len)
              :induct <call>
              :do-not-induct t)))))





(define parse-congruence-rule-shape ((x pseudo-termp))
  :returns errmsg-or-alist
  :prepwork ((local (defthm equal-of-len
                      (implies (syntaxp (quotep n))
                               (equal (equal (len x) n)
                                      (cond ((equal n 0) (atom x))
                                            ((zp n) nil)
                                            ((consp x) (equal (len (cdr x)) (1- n)))
                                            (t nil))))))
             (local (in-theory (disable len))))
  (pseudo-term-case x
    :fncall (b* (((unless (and (eq x.fn 'implies)
                               (eql (len x.args) 2)))
                  "bad congruence (no implies)")
                 ((list hyp concl) x.args)
                 ((mv errmsg equiv var1 var2)
                  (pseudo-term-case hyp
                    :fncall (b* (((unless (eql (len hyp.args) 2))
                                  (mv "bad congruence (number of hyp args)" nil nil nil))
                                 ((list var1 var2) hyp.args)
                                 ;; ((when (equal var1 var2))
                                 ;;  (mv "bad congruence (vars same)" nil nil nil))
                                 )
                              (mv nil hyp.fn var1 var2))
                    :otherwise (mv "bad congruence: hyp" nil nil nil)))
                 ((when errmsg) errmsg))
              (pseudo-term-case concl
                :fncall (b* (((unless (eql (len concl.args) 2))
                              "bad congruence (number of concl args)")
                             ((list call1 call2) concl.args)
                             ((unless (pseudo-term-case call1 :fncall))
                              "bad congruence (first concl arg)")
                             ((unless (pseudo-term-case call2 :fncall))
                              "bad congruence (second concl arg)")
                             ((pseudo-term-fncall call1))
                             ((pseudo-term-fncall call2))
                             ((unless (eq call1.fn call2.fn))
                              "bad congruence (different fns)"))
                          `((equiv-new . ,equiv)
                            (equiv-req . ,concl.fn)
                            (var1 . ,var1)
                            (var2 . ,var2)
                            (fn . ,call1.fn)
                            (args1 . ,call1.args)
                            (args2 . ,call2.args)))
                :otherwise "bad congruence: concl"))
    :otherwise "bad congruence: top-level")
  ///

  (local (in-theory (enable equal-of-pseudo-term-fncall)))

  (local (defthm equal-of-cons
           (equal (equal (cons a b) c)
                  (and (consp c)
                       (equal a (car c))
                       (equal b (cdr c))))))


  (defret parse-congruence-rule-shape-consp
    (iff (consp errmsg-or-alist)
         (and (not (stringp errmsg-or-alist))
              (b* (((acl2::assocs equiv-req equiv-new var1 var2 fn args1 args2) errmsg-or-alist))
                (equal (pseudo-term-fix x)
                       (pseudo-term-fncall 'implies
                                           (list (pseudo-term-fncall equiv-new (list var1 var2))
                                                 (pseudo-term-fncall equiv-req
                                                                     (list (pseudo-term-fncall fn args1)
                                                                           (pseudo-term-fncall fn args2)))))))))
    :hints (("goal" :expand ((:free (x) (hide x))))))

  (defret parse-congruence-rule-shape-alistp
    (implies (not (stringp errmsg-or-alist))
             (and (symbol-alistp errmsg-or-alist)
                  (alistp errmsg-or-alist))))

  (defret parse-congruence-rule-shape-types
    (implies (not (stringp errmsg-or-alist))
             (b* (((acl2::assocs equiv-req equiv-new var1 var2 fn args1 args2) errmsg-or-alist))
               (and (pseudo-fnsym-p equiv-req)
                    (symbolp equiv-req)
                    (not (equal equiv-req 'quote))
                    (pseudo-fnsym-p equiv-new)
                    (symbolp equiv-new)
                    (not (equal equiv-new 'quote))
                    (pseudo-termp var1)
                    (pseudo-termp var2)
                    (pseudo-fnsym-p fn)
                    (symbolp fn)
                    (not (equal fn 'quote))
                    (pseudo-term-listp args1)
                    (pseudo-term-listp args2))))))

(local (defthm consp-assoc-equal-when-key
         (implies k
                  (iff (consp (assoc-equal k x))
                       (assoc-equal k x)))))



(local (defun equiv-ev-context-equiv-list-of-update-nth-ind (n x y)
         (if (zp n)
             (list x y)
           (equiv-ev-context-equiv-list-of-update-nth-ind (1- n) (cdr x) (cdr y)))))

(local (defthm equiv-ev-context-equiv-list-of-update-nth
         (equal (equiv-ev-context-equiv-list (update-nth n equivs nil) x y)
                (and (equal (take n x) (take n y))
                     (equiv-ev-context-equiv equivs (nth n x) (nth n y))
                     (acl2::nth-equiv (nthcdr (+ 1 (nfix n)) x)
                                      (nthcdr (+ 1 (nfix n)) y))))
         :hints(("Goal" :in-theory (e/d (equiv-ev-context-equiv-list
                                           update-nth nth nthcdr true-list-fix)
                                        (cons-equal true-listp len))
                 :induct (equiv-ev-context-equiv-list-of-update-nth-ind n x y)))))



(define parse-congruence-rule ((x pseudo-termp) (w plist-worldp))
  :returns (mv errmsg
               (rule (implies (not errmsg) (congruence-rule-p rule))))
  :prepwork (
             (local (defthm equiv-contextslist-p-of-update-nth
                      (implies (equiv-contextsp x)
                               (equiv-contextslist-p (update-nth n x nil)))
                      :hints(("Goal" :in-theory (enable update-nth equiv-contextslist-p))))))
  (b* ((errmsg-or-alist (parse-congruence-rule-shape x))
       ((unless (consp errmsg-or-alist)) (mv errmsg-or-alist nil))
       ((acl2::assocs equiv-req equiv-new var1 var2 fn args1 args2) errmsg-or-alist)
       ((unless (pseudo-term-case var1 :var))
        (mv "bad congruence (first hyp arg)" nil))
       ((unless (pseudo-term-case var2 :var))
        (mv "bad congruence (second hyp arg)" nil))
       ((when (equal var1 var2))
        (mv "bad congruence (vars same)" nil))
       ((unless (and (pseudo-term-var-listp args1)
                     (pseudo-term-var-listp args2)
                     (mbe :logic (no-duplicatesp-eq (pseudo-term-var-list->names args1))
                          :exec (no-duplicatesp-eq args1))
                     (mbe :logic (no-duplicatesp-eq (pseudo-term-var-list->names args2))
                          :exec (no-duplicatesp-eq args2))))
        (mv "bad congruence: args" nil))
       (index (congruence-var-list-check args1 args2 var1 var2))
       ((unless index)
        (mv "bad congruence: args mismatched" nil))
       ((unless (ensure-equiv-relationp equiv-new w))
        (mv "bad congruence: not equiv relation" nil)))
    (mv nil (make-congruence-rule :equiv-req equiv-req
                                  :fn fn
                                  :arg-contexts (update-nth index (list equiv-new) nil)
                                  :arity (len args1))))
  ///
  (local (defund equiv-ev-theoremp-fn (x)
           (equiv-ev-theoremp x)))
  (local (defthmd equiv-ev-theoremp-fn-implies
           (implies (equiv-ev-theoremp-fn x)
                    (equiv-ev x a))
           :hints(("Goal" :in-theory (enable equiv-ev-theoremp-fn)
                   :use equiv-ev-falsify))))

  (local (defthm equiv-ev-when-pseudo-term-equiv
           (implies (and (equal (pseudo-term-fix x) (pseudo-term-fncall fn args))
                         (syntaxp (not (equal a ''nil))))
                    (equal (equiv-ev x a)
                           (equiv-ev (pseudo-term-fncall
                                      fn (kwote-lst (equiv-ev-list args a)))
                                     nil)))
           :hints (("goal" :use ((:instance equiv-ev-of-pseudo-term-fix-x)
                                 (:instance equiv-ev-of-pseudo-term-fncall
                                  (fn fn)))
                    :in-theory (e/d (equiv-ev-of-fncall-args)
                                    (equiv-ev-of-pseudo-term-fix-x
                                     acl2::pseudo-term-fix-under-pseudo-term-equiv
                                     equiv-ev-of-pseudo-term-fncall))))))

  (local (defthm kwote-lst-of-cons
           (equal (kwote-lst (cons a b))
                  (cons (pseudo-term-quote a) (kwote-lst b)))))

  (local (defthm kwote-lst-of-append
           (equal (kwote-lst (append a b))
                  (append (kwote-lst a) (kwote-lst b)))))

  (local (fty::deffixcong list-equiv equal (kwote-lst x) x))

  (local (in-theory (disable kwote-lst)))

  (local (defthm acl2::nth-equiv-when-same-length
           (implies (equal (len x) (len y))
                    (equal (acl2::nth-equiv x y)
                           (list-equiv x y)))
           :hints(("Goal" :in-theory (enable list-equiv
                                             acl2::nth-equiv-recursive
                                             acl2::nth-equiv-ind)))))

  (local (defthm equal-len-cdr
           (implies (equal (len x) (len y))
                    (equal (equal (len (cdr x)) (len (cdr y))) t))))


  (local (defret equiv-ev-congruence-rule-correct-p-of-<fn>-lemma
           (implies (and (equiv-ev-theoremp-fn x)
                         (equiv-ev-meta-extract-global-facts)
                         (equal w (w state))
                         (not errmsg))
                    (equiv-ev-congruence-rule-correct-p rule))
           :hints(("Goal" :in-theory (e/d (equiv-ev-congruence-rule-correct-p
                                           equiv-ev-congruence-correct-p
                                           equiv-ev-of-fncall-args
                                           equiv-ev-context-equiv-of-singleton
                                           ensure-equiv-relationp-correct
                                           equiv-ev-context-equiv-when-singleton
                                           list-equiv)
                                          (equiv-ev-when-pseudo-term-fncall
                                           len kwote-lst-redef))
                   :use ((:instance equiv-ev-theoremp-fn-implies
                          (a (b* (((congruence-rule r) rule))
                               (congruence-var-list-alist
                                (cdr (assoc 'args1 (parse-congruence-rule-shape x)))
                                (cdr (assoc 'args2 (parse-congruence-rule-shape x)))
                                (cdr (assoc 'var1 (parse-congruence-rule-shape x)))
                                (cdr (assoc 'var2 (parse-congruence-rule-shape x)))
                                (mv-nth 0 (equiv-ev-congruence-correct-p-witness
                                           (list r.equiv-req)
                                           r.fn r.arg-contexts r.arity))
                                (mv-nth 1 (equiv-ev-congruence-correct-p-witness
                                           (list r.equiv-req)
                                           r.fn r.arg-contexts r.arity)))))))
                   :do-not-induct t))
           :otf-flg t))

  (defret equiv-ev-congruence-rule-correct-p-of-<fn>
    (implies (and (equiv-ev-theoremp x)
                  (equiv-ev-meta-extract-global-facts)
                  (equal w (w state))
                  (not errmsg))
             (equiv-ev-congruence-rule-correct-p rule))
    :hints(("Goal" :use equiv-ev-congruence-rule-correct-p-of-<fn>-lemma
            :in-theory (enable equiv-ev-theoremp-fn)))))
