; FGL - A Symbolic Simulation Framework for ACL2
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

(in-package "FGL")

(include-book "bvar-db-bfrlist")
(include-book "pathcond")
(include-book "contexts")




(defsection bvar-db-boundedp
  (defun-sk bvar-db-boundedp (bvar-db logicman)
    (forall var
            (implies (and (natp var)
                          (<= (base-bvar$a bvar-db) var)
                          (< var (next-bvar$a bvar-db)))
                     (bfrlist-boundedp (fgl-object-bfrlist (get-bvar->term$a var bvar-db))
                                       var logicman)))
    :rewrite :direct)

  (defthm bvar-db-boundedp-of-empty
    (bvar-db-boundedp (init-bvar-db$a base bvar-db) logicman))

  (in-theory (disable bvar-db-boundedp
                      bvar-db-boundedp-necc))

  (defthm bvar-db-boundedp-of-add
    (implies (and (equal (next-bvar$a bvar-db) (bfr-nvars logicman))
                  (bvar-db-boundedp bvar-db logicman))
             (bvar-db-boundedp (add-term-bvar$a x bvar-db) logicman))
    :hints (("goal" :expand ((bvar-db-boundedp (add-term-bvar$a x bvar-db) logicman))
             :use ((:instance bvar-db-boundedp-necc
                    (var (bvar-db-boundedp-witness (add-term-bvar$a x bvar-db) logicman)))))))

  (defthm bvar-db-boundedp-of-update-term-equivs
    (implies (bvar-db-boundedp bvar-db logicman)
             (bvar-db-boundedp (update-term-equivs$a equivs bvar-db) logicman))
    :hints (("goal" :expand ((bvar-db-boundedp (update-term-equivs$a equivs bvar-db) logicman))
             :use ((:instance bvar-db-boundedp-necc
                    (var (bvar-db-boundedp-witness (update-term-equivs$a equivs bvar-db) logicman)))))))

  (defthm bvar-db-boundedp-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (bvar-db-boundedp bvar-db old)
                  (lbfr-listp (bvar-db-bfrlist bvar-db) old))
             (bvar-db-boundedp bvar-db new))
    :hints (("goal" :expand ((bvar-db-boundedp bvar-db new))
             :use ((:instance bvar-db-boundedp-necc
                    (var (bvar-db-boundedp-witness bvar-db new))
                    (logicman old)))))))




;; (local (include-book "std/lists/take" :dir :system))
;; (local (in-theory (disable acl2::take-redefinition acl2::take-of-1)))

;; (local (defthm take-of-symbol-list
;;          (implies (symbol-listp x)
;;                   (symbol-listp (take n x)))
;;          :hints(("Goal" :in-theory (enable acl2::take-redefinition)))))

;; (define context-p (x)
;;   (or (pseudo-fnsym-p x)
;;       (and (pseudo-lambda-p x)
;;            (eql (len (acl2::pseudo-lambda->formals x)) 1)))
;;   ///
;;   (define context-fix ((x context-p))
;;     :Returns (new-x context-p)
;;     (mbe :logic (if (pseudo-fnsym-p x)
;;                     x
;;                   (b* (((pseudo-lambda x) (pseudo-lambda-fix x)))
;;                     (pseudo-lambda (take 1 x.formals) x.body)))
;;          :exec x)
;;     ///
;;     (defthm context-fix-when-context-p
;;       (implies (context-p x)
;;                (equal (context-fix x) x)))

;;     (fty::deffixtype context :pred context-p :fix context-fix :equiv context-equiv
;;       :define t)))


(define check-equiv-replacement ((x fgl-object-p)
                                 (equiv-term fgl-object-p)
                                 (contexts equiv-contextsp)
                                 state)
  :returns (mv ok
               (equiv fgl-object-p)
               negp
               iff-equiv-p)
  (declare (ignorable state))
  ;; BOZO fix these to work with context fixing terms, refinements, negated equivs, etc
  (b* (((when (hons-equal (fgl-object-fix x)
                          (fgl-object-fix equiv-term)))
        (mv t nil t (member-eq 'iff (equiv-contexts-fix contexts))))
       ((unless (fgl-object-case equiv-term :g-apply))
        (mv nil nil nil nil))
       (equiv (g-apply->fn equiv-term))
       ((unless (or (eq equiv 'equal)
                    (member-eq equiv (equiv-contexts-fix contexts))))
        (mv nil nil nil nil))
       (args (g-apply->args equiv-term))
       ((unless (equal (len args) 2))
        (mv nil nil nil nil))
       ((when (hons-equal (car args) (fgl-object-fix x)))
        (mv t (cadr args) nil nil))
       ((when (hons-equal (cadr args) (fgl-object-fix x)))
        (mv t (car args) nil nil)))
    (mv nil nil nil nil))
  ///
  (defret fgl-object-bfrlist-of-<fn>
    (implies (not (member v (fgl-object-bfrlist equiv-term)))
             (not (member v (fgl-object-bfrlist equiv))))))



(define try-equivalences ((x fgl-object-p)
                          (bvars nat-listp)
                          (contexts equiv-contextsp)
                          pathcond
                          bvar-db
                          logicman
                          state)
  :guard (and (bvar-list-okp bvars bvar-db)
              (equal (next-bvar bvar-db) (bfr-nvars)))
  :returns (mv ok
               (new-x fgl-object-p)
               (new-pathcond (equal new-pathcond (pathcond-fix pathcond))))
  :guard-hints ((and stable-under-simplificationp
                     '(:expand ((bvar-list-okp$a bvars bvar-db))
                       :in-theory (enable bfr-varname-p))))
  (b* ((pathcond (pathcond-fix pathcond))
       ((when (atom bvars)) (mv nil nil pathcond))
       (bvar (lnfix (car bvars)))
       (bfr-var (bfr-var bvar logicman))
       (equiv-term (get-bvar->term bvar bvar-db))
       ((mv check-ok repl negp iff-equiv-p)
        (check-equiv-replacement x equiv-term contexts state))
       ((unless check-ok)
        (try-equivalences x (cdr bvars) contexts pathcond bvar-db logicman state))
       ((mv ans pathcond) (logicman-pathcond-implies bfr-var pathcond logicman))
       ((when (if negp (eql ans 0) (eql ans 1)))
        (mv t repl pathcond))
       ((when (and iff-equiv-p ans))
        (mv t (eql ans 1) pathcond)))
      (try-equivalences x (cdr bvars) contexts pathcond bvar-db logicman state))
  ///
  (local (defthm fgl-object-bfrlist-of-boolean
           (implies (booleanp x)
                    (equal (fgl-object-bfrlist x) nil))
           :hints(("Goal" :in-theory (enable booleanp)))))
  (defret fgl-object-bfrlist-of-<fn>
    (implies (and (not (member v (bvar-db-bfrlist bvar-db)))
                  (bvar-list-okp$a bvars bvar-db))
             (not (member v (fgl-object-bfrlist new-x))))))


(define try-equivalences-loop ((x fgl-object-p)
                               (contexts equiv-contextsp)
                               (clk natp)
                               pathcond
                               bvar-db
                               logicman
                               state)
  :guard (equal (next-bvar bvar-db) (bfr-nvars))
  :measure (nfix clk)
  :returns (mv error
               (replacement fgl-object-p)
               (new-pathcond (equal new-pathcond (pathcond-fix pathcond))))
  (b* ((pathcond (pathcond-fix pathcond))
       ((when (zp clk)) (mv "try-equivalences ran out of clock -- equiv loop?"
                            (fgl-object-fix x)
                            pathcond))
       (equivs (get-term->equivs x bvar-db))
       ((mv ok repl pathcond)
        (try-equivalences x equivs contexts pathcond bvar-db logicman state))
       ((when ok)
        (try-equivalences-loop repl contexts (1- clk) pathcond bvar-db logicman state)))
    (mv nil (fgl-object-fix x) pathcond))
  ///
  (defret fgl-object-bfrlist-of-<fn>
    (implies (and (not (member v (bvar-db-bfrlist bvar-db)))
                  (not (member v (fgl-object-bfrlist x))))
             (not (member v (fgl-object-bfrlist replacement))))))


(define maybe-add-equiv-term ((test-obj fgl-object-p)
                              (bvar natp)
                              bvar-db
                              state)
  :guard (and (<= (base-bvar bvar-db) bvar)
              (< bvar (next-bvar bvar-db)))
  :returns (new-bvar-db)
  ;; We (maybe) add an association between some term and the generated Boolean
  ;; variable, saying that if the Boolean variable is assumed true or false,
  ;; that may imply some value of the test-obj.

  ;; In some cases we associate test-obj itself to bvar.  In this case the
  ;; association means if bvar is NIL, then normalize test-obj is NIL.
  ;; Otherwise test-obj is (equal x y) and we associate either x or y to bvar;
  ;; in this case, if bvar is true, normalize (respectively) x to y or y to x.
  (declare (ignorable state))
  (fgl-object-case test-obj
    :g-var (add-term-equiv test-obj bvar bvar-db)
    :g-apply (b* ((fn test-obj.fn)
                  (args test-obj.args)

                  ((unless (and (eq fn 'equal)
                                (equal (len args) 2)))
                   (add-term-equiv test-obj bvar bvar-db))
                  ((list a b) args)
                  ;; The rest is just a heuristic determination of which should rewrite to
                  ;; the other. Note: in many cases we don't rewrite either way!

                  ;; Heuristic 1: when a variable is equated with anything else, normalize var -> other.
                  ;; (Note this could loop, up to the user to prevent this)
                  (a-varp (fgl-object-case a :g-var))
                  (b-varp (fgl-object-case b :g-var))
                  ((when a-varp)
                   (if b-varp
                       (add-term-equiv test-obj bvar bvar-db)
                     (add-term-equiv a bvar bvar-db)))
                  ((when b-varp)
                   (add-term-equiv b bvar bvar-db))

                  ;; Heuristic 2: when one object has no free variables,
                  ;;              normalize other -> good obj.
                  (a-goodp (fgl-object-variable-free-p a))
                  ((when a-goodp)
                   (add-term-equiv b bvar bvar-db))
                  (b-goodp (fgl-object-variable-free-p b))
                  ((when b-goodp)
                   (add-term-equiv a bvar bvar-db)))

               ;; Neither heuristic applied -- don't normalize either way.
               (add-term-equiv test-obj bvar bvar-db))

    :otherwise (add-term-equiv test-obj bvar bvar-db))
  ///
  

  (defthm bvar-db-bfrlist-of-maybe-add-equiv-term
    (equal (bvar-db-bfrlist (maybe-add-equiv-term obj bvar bvar-db state))
           (bvar-db-bfrlist bvar-db))
    :hints(("Goal" :in-theory (enable maybe-add-equiv-term
                                      bvar-db-bfrlist
                                      add-term-equiv))))

  (defthm bvar-db-boundedp-of-maybe-add-equiv-term
    (implies (bvar-db-boundedp bvar-db logicman)
             (bvar-db-boundedp (maybe-add-equiv-term obj bvar bvar-db state) logicman))
    :hints (("goal" :expand ((bvar-db-boundedp (maybe-add-equiv-term obj bvar bvar-db state) logicman))
             :use ((:instance bvar-db-boundedp-necc
                    (var (bvar-db-boundedp-witness
                          (maybe-add-equiv-term obj bvar bvar-db state) logicman))))
             :in-theory (enable add-term-equiv))))

  (defthm next-bvar$a-of-maybe-add-equiv-term
    (equal (next-bvar$a (maybe-add-equiv-term x bvar bvar-db state))
           (next-bvar$a bvar-db))
    :hints(("Goal" :in-theory (enable maybe-add-equiv-term))))

  (defthm base-bvar$a-of-maybe-add-equiv-term
    (equal (base-bvar$a (maybe-add-equiv-term x bvar bvar-db state))
           (base-bvar$a bvar-db))
    :hints(("Goal" :in-theory (enable maybe-add-equiv-term))))

  (defthm get-bvar->term$a-of-maybe-add-equiv-term
    (equal (get-bvar->term$a n (maybe-add-equiv-term x bvar bvar-db state))
           (get-bvar->term$a n bvar-db)))

  (defthm get-term->bvar$a-of-maybe-add-equiv-term
    (equal (get-term->bvar$a obj (maybe-add-equiv-term x bvar bvar-db state))
           (get-term->bvar$a obj bvar-db))))



