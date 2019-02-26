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
    (mv nil nil nil)))



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
      (try-equivalences x (cdr bvars) contexts pathcond bvar-db logicman state))))


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
    (mv nil (gl-object-fix x) pathcond)))


(define maybe-add-equiv-term ((test-obj gl-object-p)
                              (bvar natp)
                              bvar-db
                              state)
  :guard (and (<= (base-bvar bvar-db) bvar)
              (< bvar (next-bvar bvar-db)))
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

    :otherwise bvar-db))

