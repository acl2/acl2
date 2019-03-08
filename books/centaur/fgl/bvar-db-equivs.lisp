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

(in-package "FGL")

(include-book "bvar-db")
(include-book "pathcond")
(include-book "contexts")



(define bvar-db-bfrlist-aux ((n natp) bvar-db)
  :returns (bfrs)
  :measure (nfix (- (nfix n) (base-bvar bvar-db)))
  :guard (and (<= (base-bvar bvar-db) n)
              (<= n (next-bvar bvar-db)))
  (if (zp (- (lnfix n) (base-bvar bvar-db)))
      nil
    (append (gl-object-bfrlist (get-bvar->term (1- (lnfix n)) bvar-db))
            (bvar-db-bfrlist-aux (1- (lnfix n)) bvar-db)))
  ///
  (defthm bfrlist-aux-of-get-bvar->term
    (implies (and (not (member v (bvar-db-bfrlist-aux n bvar-db)))
                  (< (nfix m) (nfix n))
                  (<= (base-bvar$a bvar-db) (nfix m)))
             (not (member v (gl-object-bfrlist (get-bvar->term$a m bvar-db))))))

  (defthm bfrlist-aux-of-add-term-bvar
    (implies (<= (nfix n) (next-bvar$a bvar-db))
             (equal (bvar-db-bfrlist-aux n (add-term-bvar$a obj bvar-db))
                    (bvar-db-bfrlist-aux n bvar-db))))

  (defthm bfrlist-aux-of-update-term-equivs
    (equal (bvar-db-bfrlist-aux n (update-term-equivs$a obj bvar-db))
           (bvar-db-bfrlist-aux n bvar-db)))

  (defthm subsetp-bfrlist-of-bvar-db-bfrlist-aux
    (implies (and (< (nfix m) (nfix n))
                  (<= (base-bvar$a bvar-db) (nfix m)))
             (subsetp (gl-object-bfrlist (get-bvar->term$a m bvar-db))
                      (bvar-db-bfrlist-aux n bvar-db)))
    :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw)))))

(define bvar-db-bfrlist (bvar-db)
  (bvar-db-bfrlist-aux (next-bvar bvar-db) bvar-db)
  ///
  (defthm bfrlist-of-get-bvar->term
    (implies (and (not (member v (bvar-db-bfrlist bvar-db)))
                  (< (nfix m) (next-bvar$a bvar-db))
                  (<= (base-bvar$a bvar-db) (nfix m)))
             (not (member v (gl-object-bfrlist (get-bvar->term$a m bvar-db))))))

  (defthm bvar-db-bfrlist-of-add-term-bvar
    (equal (bvar-db-bfrlist (add-term-bvar$a obj bvar-db))
           (append (gl-object-bfrlist obj)
                   (bvar-db-bfrlist bvar-db)))
    :hints (("goal" :in-theory (enable bvar-db-bfrlist-aux))))

  (defthm subsetp-bfrlist-of-bvar-db-bfrlist
    (implies (and (< (nfix m) (next-bvar$a bvar-db))
                  (<= (base-bvar$a bvar-db) (nfix m)))
             (subsetp (gl-object-bfrlist (get-bvar->term$a m bvar-db))
                      (bvar-db-bfrlist bvar-db))))

  (defthm bvar-db-bfrlist-of-add-term-bvar-unique
    (acl2::set-equiv (bvar-db-bfrlist (mv-nth 1 (add-term-bvar-unique obj bvar-db)))
                     (append (gl-object-bfrlist obj)
                             (bvar-db-bfrlist bvar-db)))
    :hints (("goal" :in-theory (e/d (add-term-bvar-unique)
                                    (bvar-db-bfrlist
                                     subsetp-bfrlist-of-bvar-db-bfrlist))
             :use ((:instance subsetp-bfrlist-of-bvar-db-bfrlist
                    (m (get-term->bvar$a obj bvar-db))))))))

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


(define check-equiv-replacement ((x gl-object-p)
                                 (equiv-term gl-object-p)
                                 (contexts equiv-contextsp)
                                 state)
  :returns (mv ok
               (equiv gl-object-p)
               negp)
  (declare (ignorable state))
  ;; BOZO fix these to work with context fixing terms, refinements, negated equivs, etc
  (b* (((when (hons-equal (gl-object-fix x)
                     (gl-object-fix equiv-term)))
        (mv t nil t))
       ((unless (gl-object-case equiv-term :g-apply))
        (mv nil nil nil))
       (equiv (g-apply->fn equiv-term))
       ((unless (or (eq equiv 'equal)
                    (member-eq equiv (equiv-contexts-fix contexts))))
        (mv nil nil nil))
       (args (g-apply->args equiv-term))
       ((unless (equal (len args) 2))
        (mv nil nil nil))
       ((when (hons-equal (car args) (gl-object-fix x)))
        (mv t (cadr args) nil))
       ((when (hons-equal (cadr args) (gl-object-fix x)))
        (mv t (car args) nil)))
    (mv nil nil nil))
  ///
  (defret gl-object-bfrlist-of-<fn>
    (implies (not (member v (gl-object-bfrlist equiv-term)))
             (not (member v (gl-object-bfrlist equiv))))))



(define try-equivalences ((x gl-object-p)
                          (bvars nat-listp)
                          (contexts equiv-contextsp)
                          pathcond
                          bvar-db
                          logicman
                          state)
  :guard (and (bvar-list-okp bvars bvar-db)
              (logicman-check-nvars (next-bvar bvar-db)))
  :returns (mv ok
               (new-x gl-object-p)
               (new-pathcond (equal new-pathcond (pathcond-fix pathcond))))
  (b* ((pathcond (pathcond-fix pathcond))
       ((when (atom bvars)) (mv nil nil pathcond))
       (bvar (lnfix (car bvars)))
       (bfr-var (bfr-var bvar logicman))
       (equiv-term (get-bvar->term bvar bvar-db))
       ((mv check-ok repl negp)
        (check-equiv-replacement x equiv-term contexts state))
       ((unless check-ok)
        (try-equivalences x (cdr bvars) contexts pathcond bvar-db logicman state))
       ((mv ans pathcond) (logicman-pathcond-implies bfr-var pathcond logicman)))
    (if (if negp (eql ans 0) (eql ans 1))
        (mv t repl pathcond)
      (try-equivalences x (cdr bvars) contexts pathcond bvar-db logicman state)))
  ///
  (defret gl-object-bfrlist-of-<fn>
    (implies (and (not (member v (bvar-db-bfrlist bvar-db)))
                  (bvar-list-okp$a bvars bvar-db))
             (not (member v (gl-object-bfrlist new-x))))))


(define try-equivalences-loop ((x gl-object-p)
                               (contexts equiv-contextsp)
                               (clk natp)
                               pathcond
                               bvar-db
                               logicman
                               state)
  :guard (logicman-check-nvars (next-bvar bvar-db))
  :measure (nfix clk)
  :returns (mv error
               (replacement gl-object-p)
               (new-pathcond (equal new-pathcond (pathcond-fix pathcond))))
  (b* ((pathcond (pathcond-fix pathcond))
       ((when (zp clk)) (mv "try-equivalences ran out of clock -- equiv loop?"
                            (gl-object-fix x)
                            pathcond))
       (equivs (get-term->equivs x bvar-db))
       ((mv ok repl pathcond)
        (try-equivalences x equivs contexts pathcond bvar-db logicman state))
       ((when ok)
        (try-equivalences-loop repl contexts (1- clk) pathcond bvar-db logicman state)))
    (mv nil (gl-object-fix x) pathcond))
  ///
  (defret gl-object-bfrlist-of-<fn>
    (implies (and (not (member v (bvar-db-bfrlist bvar-db)))
                  (not (member v (gl-object-bfrlist x))))
             (not (member v (gl-object-bfrlist replacement))))))


(define maybe-add-equiv-term ((test-obj gl-object-p)
                              (bvar natp)
                              bvar-db
                              state)
  :guard (and (<= (base-bvar bvar-db) bvar)
              (< bvar (next-bvar bvar-db)))
  :returns (new-bvar-db)
  (declare (ignorable state))
  (gl-object-case test-obj
    :g-var (add-term-equiv test-obj bvar bvar-db)
    :g-apply (b* ((fn test-obj.fn)
                  (args test-obj.args)

                  ((unless (and (eq fn 'equal)
                                (equal (len args) 2)))
                   (add-term-equiv test-obj bvar bvar-db))
                  ((list a b) args)
                  ;; The rest is just a heuristic determination of which should rewrite to
                  ;; the other. Note: in most cases we don't rewrite either way!
                  (a-goodp (gl-object-case a
                             :g-integer t :g-boolean t :g-concrete t :otherwise nil))
                  ((when a-goodp)
                   (add-term-equiv b bvar bvar-db))
                  (b-goodp (gl-object-case b
                             :g-integer t :g-boolean t :g-concrete t :otherwise nil))
                  ((when b-goodp)
                   (add-term-equiv a bvar bvar-db)))
               bvar-db)

    :otherwise bvar-db)
  ///
  

  (defthm bvar-db-bfrlist-of-maybe-add-equiv-term
    (equal (bvar-db-bfrlist (maybe-add-equiv-term obj bvar bvar-db state))
           (bvar-db-bfrlist bvar-db))
    :hints(("Goal" :in-theory (enable maybe-add-equiv-term
                                      bvar-db-bfrlist
                                      add-term-equiv))))

  (defthm next-bvar$a-of-maybe-add-equiv-term
    (equal (next-bvar$a (maybe-add-equiv-term x bvar bvar-db state))
           (next-bvar$a bvar-db))
    :hints(("Goal" :in-theory (enable maybe-add-equiv-term)))))



