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

;; Svex let abstraction -- display large svexes linearly, avoiding exponential
;; blowup in printing shared subexpressions.

(in-package "SV")
(include-book "rewrite-rules")
(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/cat" :dir :system)
(include-book "centaur/misc/hons-extra" :dir :system)

(defthm alist-keys-of-svex-key-alist
  (implies (svex-key-alist-p x)
           (svexlist-p (alist-keys x)))
  :hints(("Goal" :in-theory (enable alist-keys))))

(defines svex-multirefs-postorder
  :verify-guards nil
  (define svex-multirefs-postorder ((x svex-p)
                          (seen svex-key-alist-p)
                          (multiref svex-key-alist-p))
    :returns (mv (seen-out svex-key-alist-p)
                 (multiref-out svex-key-alist-p))
    :measure (svex-count x)
    (b* ((seen (svex-key-alist-fix seen))
         (multiref (svex-key-alist-fix multiref))
         (x (svex-fix x)))
      (svex-case x
        :call
        (b* ((seenp (hons-get x seen))
             ((when seenp)
              (mv seen (svex-set-multiref x multiref)))
             ((mv seen multiref)
              (svexlist-multirefs-postorder x.args seen multiref)))
          (mv (hons-acons x t seen) multiref))
        :otherwise (mv seen multiref))))
  (define svexlist-multirefs-postorder ((x svexlist-p)
                              (seen svex-key-alist-p)
                              (multiref svex-key-alist-p))
    :returns (mv (seen-out svex-key-alist-p)
                 (multiref-out svex-key-alist-p))
    :measure (svexlist-count x)
    (b* ((seen (svex-key-alist-fix seen))
         (multiref (svex-key-alist-fix multiref)))
      (if (atom x)
          (mv seen multiref)
        (b* (((mv seen multiref) (svex-multirefs-postorder (car x) seen multiref)))
          (svexlist-multirefs-postorder (cdr x) seen multiref)))))
  ///
  (verify-guards svex-multirefs-postorder)
  (deffixequiv-mutual svex-multirefs-postorder))


(define svex-key-alist-collect-ordered ((order svexlist-p)
                                        (alist svex-key-alist-p))
  :returns (ordered-keys svexlist-p)
  (if (atom order)
      nil
    (if (hons-get (svex-fix (car order))
                  (svex-key-alist-fix alist))
        (cons (svex-fix (car order))
              (svex-key-alist-collect-ordered (cdr order) alist))
      (svex-key-alist-collect-ordered (cdr order) alist))))


(define make-n-svars ((n natp)
                      (basename stringp)
                      (pkg-sym symbolp))
  :returns (vars svarlist-p)
  (if (zp n)
      nil
    (cons (make-svar :name
                     (intern-in-package-of-symbol
                      (cat basename (natstr (1- n)))
                      (mbe :logic (acl2::symbol-fix pkg-sym) :exec pkg-sym)))
          (make-n-svars (1- n) basename pkg-sym)))
  ///
  (defret len-of-make-n-svex-vars
    (equal (len vars) (nfix n))))



(fty::defalist svex-svex-alist :key-type svex :val-type svex)
        
(defines svex-replace-subterms
  (define svex-replace-subterms ((x svex-p)
                                 (subst svex-svex-alist-p))
    :measure (svex-count x)
    :returns (new-x svex-p)
    :verify-guards nil
    (b* ((x (svex-fix x))
         (subst (svex-svex-alist-fix subst))
         (look (hons-get x subst))
         ((when look) (cdr look)))
      (svex-case x
        :call (change-svex-call x :args (svexlist-replace-subterms x.args subst))
        :otherwise x)))
  (define svexlist-replace-subterms ((x svexlist-p)
                                     (subst svex-svex-alist-p))
    :measure (svexlist-count x)
    :returns (new-x svexlist-p)
    (b* (((when (atom x)) (svexlist-fix x))
         (car (svex-replace-subterms (car x) subst))
         (cdr (svexlist-replace-subterms (cdr x) subst)))
      (cons-with-hint car cdr x)))
  ///
  (verify-guards svex-replace-subterms)

  (defret consp-of-svexlist-replace-subterms
    (iff (consp new-x) (consp x))
    :hints (("goal" :expand ((svexlist-replace-subterms x subst))))
    :fn svexlist-replace-subterms))

(define svex-subst-alist-let*-abstract ((x svex-alist-p)
                                        (subst svex-svex-alist-p))
  :returns (new-x svex-alist-p)
  :measure (len (svex-alist-fix x))
  :hints(("Goal" :in-theory (enable len)))
  :hooks nil
  (b* ((x (svex-alist-fix x))
       ((when (atom x)) x)
       ((cons key val) (car x))
       (new-val (svex-case val
                  :call (change-svex-call val :args (svexlist-replace-subterms val.args subst))
                  :otherwise val)))
    (cons-with-hint
     (cons-with-hint key new-val (car x))
     (svex-subst-alist-let*-abstract (cdr x) subst)
     x)))

(defthm svex-svex-alist-p-of-pairlis$
  (implies (and (svexlist-p keys)
                (svexlist-p vals)
                (equal (len keys) (len vals)))
           (svex-svex-alist-p (pairlis$ keys vals)))
  :hints(("Goal" :in-theory (enable pairlis$))))

(define svexlist-let*-abstract ((x svexlist-p)
                                &key
                                ((basename stringp) '"__X_")
                                ((pkgsym symbolp) ''sv::foo)
                                (all-subtrees 'nil))
  :returns (mv (abs-alist svex-alist-p)
               (new-x svexlist-p))
  :hooks nil
  (b* (((mv seen multiref) (svexlist-multirefs-postorder x nil nil))
       (- (fast-alist-free seen))
       (multirefs (if all-subtrees
                      (alist-keys seen)
                    (svex-key-alist-collect-ordered (alist-keys seen) multiref)))
       (- (fast-alist-free multiref))
       (vars (make-n-svars (len multirefs) basename pkgsym))
       (subst (pairlis$ multirefs (svarlist->svexes vars)))
       ((with-fast subst))
       (new-x (svexlist-replace-subterms x subst))
       (alist (pairlis$ vars multirefs))
       (abstracted-alist (rev (svex-subst-alist-let*-abstract alist subst))))
    (mv abstracted-alist new-x))
  ///
  (defret consp-of-svexlist-let*-abstract
    (iff (consp new-x)
         (consp x)))

  (defret len-of-svexlist-let*-abstract
    (iff (len new-x)
         (len x))))


(define svexlist-let*-abstract-term ((x svexlist-p)
                                     &key
                                     ((basename stringp) '"__X_")
                                     ((pkgsym symbolp) ''sv::foo))
  :hooks nil
  (b* (((mv abs-alist new-x)
        (svexlist-let*-abstract x :basename basename :pkgsym pkgsym)))
    `(let* ,(pairlis$ (alist-keys abs-alist)
                      (pairlis$ (alist-vals abs-alist) nil))
       (list . ,new-x))))


(define svex-let*-eval-final-env ((x svex-alist-p)
                                  (env svex-env-p))
  :returns (final-env svex-env-p)
  :measure (len (svex-alist-fix x))
  :hints(("Goal" :in-theory (enable len)))
  (b* ((x (svex-alist-fix x))
       ((when (atom x))
        (svex-env-fix env))
       ((cons key val) (car x))
       (eval (svex-eval val env))
       (new-env (hons-acons key eval env))
       (- (clear-memoize-table 'svex-eval)))
    (svex-let*-eval-final-env (cdr x) new-env)))

#!sv
(define svex-let*-compose-alist ((x svex-alist-p)
                                 (res svex-alist-p))
  :returns (final-res svex-alist-p)
  :measure (len (svex-alist-fix x))
  :hints(("Goal" :in-theory (enable len)))
  (b* ((x (svex-alist-fix x))
       ((when (atom x))
        (svex-alist-fix res))
       ((cons key val) (car x))
       (comp (svex-compose val res))
       (new-res (hons-acons key comp res))
       (- (clear-memoize-table 'svex-compose)))
    (svex-let*-compose-alist (cdr x) new-res)))



(define svex-let*-abstract-term ((x svex-p)
                                 &key
                                 ((basename stringp) '"__X_")
                                 ((pkgsym symbolp) ''sv::foo))
  :hooks nil
  (b* (((mv abs-alist new-x)
        (svexlist-let*-abstract (list x) :basename basename :pkgsym pkgsym)))
    `(let* ,(pairlis$ (alist-keys abs-alist)
                      (pairlis$ (alist-vals abs-alist) nil))
       ,(car new-x))))

(define svex-let*-abstract-term-eval ((x svex-p)
                                      (env svex-env-p)
                                      &key
                                      ((basename stringp) '"__X_")
                                      ((pkgsym symbolp) ''sv::foo)
                                      (all-subtrees 'nil))
  (b* (((mv abs-alist (cons new-x &))
        (svexlist-let*-abstract (list x) :basename basename :pkgsym pkgsym :all-subtrees all-subtrees))
       (env (make-fast-alist env))
       (eval-env (svex-let*-eval-final-env abs-alist env))
       (eval-alist (svex-alist-eval abs-alist eval-env))
       (eval-x (svex-eval new-x eval-env))
       (- (fast-alist-free eval-env)))
    `(let* ,(pairlis$ (alist-keys abs-alist)
                      (pairlis$ (alist-vals eval-alist)
                                (pairlis$ (alist-vals abs-alist) nil)))
       ,eval-x
       ,new-x)))

(define svexlist-let*-abstract-term-eval ((x svexlist-p)
                                          (env svex-env-p)
                                          &key
                                          ((basename stringp) '"__X_")
                                          ((pkgsym symbolp) ''sv::foo))
  (b* (((mv abs-alist new-x)
        (svexlist-let*-abstract x :basename basename :pkgsym pkgsym))
       (env (make-fast-alist env))
       (eval-env (svex-let*-eval-final-env abs-alist env))
       (eval-alist (svex-alist-eval abs-alist eval-env))
       (eval-x (svexlist-eval new-x eval-env))
       (- (fast-alist-free eval-env)))
    `(let* ,(pairlis$ (alist-keys abs-alist)
                      (pairlis$ (alist-vals eval-alist)
                                (pairlis$ (alist-vals abs-alist) nil)))
       ,(pairlis$ eval-x (pairlis$ new-x nil)))))


