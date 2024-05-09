; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2022 Intel Corp.
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")

(include-book "rewrite-base")
(include-book "lists")
(include-book "svar-key-alist")
(include-book "std/basic/two-nats-measure" :Dir :System)
(local (include-book "centaur/misc/dfs-measure" :dir :system))


(fty::defmap fnsym-svexlistlist-alist :key-type fnsym :val-type svexlistlist :true-listp t)

(defconst *svex-clock-patterns-default*
  ;; Alist mapping leading function symbols to argument patterns.  For each
  ;; variable clk0, clk1, ... in a pattern, at least one of them must be a
  ;; clock for the signal to be a derived clock.  This omits the outer (concat
  ;; 1 x 0).
  '((bitand (clk0 clk1))
    (bitor  (clk0 clk1))
    (bitnot (clk0))))


(define svex-clock-patterns-default ()
  :returns (patterns fnsym-svexlistlist-alist-p)
  *svex-clock-patterns-default*
  ///
  (defret alistp-of-<fn>
    (alistp patterns))
  (in-theory (disable (svex-clock-patterns-default))))

(encapsulate
  (((svex-clock-patterns) => *
    :formals nil :guard t))

  (local (defun svex-clock-patterns ()
           (declare (xargs :guard t))
           nil))

  (defthm fnsym-svexlistlist-alist-p-of-svex-clock-patterns
    (fnsym-svexlistlist-alist-p (svex-clock-patterns))))

(defthm alistp-of-svex-clock-patterns
  (alistp (svex-clock-patterns))
  :hints (("goal" :use fnsym-svexlistlist-alist-p-of-svex-clock-patterns
           :in-theory (disable fnsym-svexlistlist-alist-p-of-svex-clock-patterns))))

(defattach svex-clock-patterns svex-clock-patterns-default)



(defines svex-assigns-find-clock-signals
  :prepwork (;; (local (in-theory (disable acl2::set-difference-of-cons-second)))
             (local (defthm alist-keys-of-cons
                      (equal (alist-keys (cons (cons key val) rest))
                             (cons key (alist-keys rest)))
                      :hints(("Goal" :in-theory (enable alist-keys)))))
             (local (defthm member-alist-keys
                      (iff (member-equal x (alist-keys y))
                           (hons-assoc-equal x y))
                      :hints(("Goal" :in-theory (enable alist-keys)))))
             (local (in-theory (disable (tau-system)))))
  (define svex-assigns-find-clock-signals ((var svar-p)
                                           (clock-alist svar-key-alist-p) ;; binds keys to T
                                           (seen svar-key-alist-p)
                                           (assigns svex-alist-p))
    :well-founded-relation acl2::nat-list-<
    :measure (list (len (set-difference-equal (svex-alist-keys assigns)
                                              (alist-keys (svar-key-alist-fix seen))))
                   0 0)
    :returns (mv clockp
                 (new-clock-alist svar-key-alist-p)
                 (new-seen svar-key-alist-p))
    :verify-guards nil
    (b* ((var (svar-fix var))
         (clock-alist (svar-key-alist-fix clock-alist))
         (seen (svar-key-alist-fix seen))
         (look (hons-get var clock-alist))
         ((when look)
          (mv (cdr look) clock-alist seen))
         ((when (hons-get var seen))
          ;; Circular ref, not a clock for our purposes
          ;; (b* ((clock-alist (hons-acons (svar-fix var) nil (svar-key-alist-fix clock-alist))))
          (mv nil clock-alist seen))
         (val (svex-fastlookup var assigns))
         ((unless val)
          ;; Undriven signal -- not a clock unless originally in the clock alist.
          (mv nil clock-alist seen))

         (seen (hons-acons var t seen))
         ;; Normal form for single bit signals is (concat 1 x 0).  So first of
         ;; all, we need to match that or we're not a clock.  Note this could
         ;; conceivablye change...
         ((mv concat-match concat-alist) (svex-unify '(concat 1 x 0) val nil))
         ((unless concat-match)
          (mv nil clock-alist seen))
         (x (svex-lookup 'x concat-alist)))

       
    (svex-case x
      :var
      ;; Var is a clock iff x is a clock
      (b* (((mv clockp clock-alist seen)
            (svex-assigns-find-clock-signals x.name clock-alist seen assigns))
           ((when clockp)
            (mv clockp (hons-acons var t clock-alist) seen)))
        (mv nil clock-alist seen))

      :quote (mv nil clock-alist seen)

      :call (b* ((rules (cdr (assoc-eq x.fn (svex-clock-patterns))))
                 ((mv clockp clock-alist seen)
                  (svex-assigns-find-clock-signals-rulelist x.args rules clock-alist seen assigns))
                 ((when clockp)
                  (mv clockp (hons-acons var t clock-alist) seen)))
              (mv nil clock-alist seen)))))

  (define svex-assigns-find-clock-signals-rulelist ((args svexlist-p)
                                                    (rule-args svexlistlist-p)
                                                    (clock-alist svar-key-alist-p) ;; binds keys to T
                                                    (seen svar-key-alist-p)
                                                    (assigns svex-alist-p))
    :measure (list (len (set-difference-equal (svex-alist-keys assigns)
                                              (alist-keys (svar-key-alist-fix seen))))
                   3 (len rule-args))
    :returns (mv clockp
                 (new-clock-alist svar-key-alist-p)
                 (new-seen svar-key-alist-p))
    (b* (((when (atom rule-args))
          (mv nil (svar-key-alist-fix clock-alist)
              (svar-key-alist-fix seen)))
         ((mv clockp1 clock-alist seen)
          (mbe :logic (b* ((seen-prev (svar-key-alist-fix seen))
                           ((mv clockp clock-alist seen)
                            (svex-assigns-find-clock-signals-rule args (car rule-args) clock-alist seen assigns)))
                        (mv clockp clock-alist
                            (if (< (len (set-difference-equal (svex-alist-keys assigns)
                                                              (alist-keys (svar-key-alist-fix seen-prev))))
                                   (len (set-difference-equal (svex-alist-keys assigns)
                                                              (alist-keys (svar-key-alist-fix seen)))))
                                seen-prev ;; impossible
                              seen)))
               :exec (svex-assigns-find-clock-signals-rule args (car rule-args) clock-alist seen assigns)))
         ((When clockp1)
          (mv t clock-alist seen)))
      (svex-assigns-find-clock-signals-rulelist args (cdr rule-args) clock-alist seen assigns)))

  (define svex-assigns-find-clock-signals-rule ((args svexlist-p)
                                                (rule-args svexlist-p)
                                                (clock-alist svar-key-alist-p) ;; binds keys to T
                                                (seen svar-key-alist-p)
                                                (assigns svex-alist-p))
  
    :measure (list (len (set-difference-equal (svex-alist-keys assigns)
                                              (alist-keys (svar-key-alist-fix seen))))
                   3 0)
    :returns (mv clockp
                 (new-clock-alist svar-key-alist-p)
                 (new-seen svar-key-alist-p))
    (b* (((mv unify-ok unify-alist) (svexlist-unify rule-args args nil))
         ((unless unify-ok)
          (mv nil (svar-key-alist-fix clock-alist)
              (svar-key-alist-fix seen))))
      (svex-assigns-find-clock-signals-rule-alternatives '(clk0 clk1 clk2) unify-alist clock-alist seen assigns)))
         
  (define svex-assigns-find-clock-signals-rule-alternatives ((clock-vars svarlist-p)
                                                             (unify-alist svex-alist-p)
                                                             (clock-alist svar-key-alist-p)
                                                             (seen svar-key-alist-p)
                                                             (assigns svex-alist-p))
  
    :measure (list (len (set-difference-equal (svex-alist-keys assigns)
                                              (alist-keys (svar-key-alist-fix seen))))
                   2 (len clock-vars))
    :returns (mv clockp
                 (new-clock-alist svar-key-alist-p)
                 (new-seen svar-key-alist-p))

    (b* (((when (atom clock-vars))
          (mv nil (svar-key-alist-fix clock-alist)
              (svar-key-alist-fix seen)))
         (expr (svex-lookup (car clock-vars) unify-alist))
         ((unless (and expr (svex-case expr :var)))
          (svex-assigns-find-clock-signals-rule-alternatives (cdr clock-vars) unify-alist clock-alist seen assigns))
         ((mv expr-clockp clock-alist seen)
          (mbe :logic (b* ((seen-prev (svar-key-alist-fix seen))
                           ((mv clockp clock-alist seen)
                            (svex-assigns-find-clock-signals (svex-var->name expr) clock-alist seen assigns)))
                        (mv clockp clock-alist
                            (if (< (len (set-difference-equal (svex-alist-keys assigns)
                                                              (alist-keys (svar-key-alist-fix seen-prev))))
                                   (len (set-difference-equal (svex-alist-keys assigns)
                                                              (alist-keys (svar-key-alist-fix seen)))))
                                seen-prev ;; impossible
                              seen)))
               :exec (svex-assigns-find-clock-signals (svex-var->name expr) clock-alist seen assigns)))
         ((when expr-clockp)
          (mv t clock-alist seen)))
      (svex-assigns-find-clock-signals-rule-alternatives (cdr clock-vars) unify-alist clock-alist seen assigns)))


  ///

  (local (in-theory (disable svex-assigns-find-clock-signals
                             svex-assigns-find-clock-signals-rulelist
                             svex-assigns-find-clock-signals-rule
                             svex-assigns-find-clock-signals-rule-alternatives)))
  
  (std::defret-mutual mv-list-of-svex-assigns-find-clock-signals
    (defret mv-list-of-<fn>
      (equal (list clockp new-clock-alist new-seen) <call>)
      :hints ('(:expand (<call>)))
      :fn svex-assigns-find-clock-signals)
    (defret mv-list-of-<fn>
      (equal (list clockp new-clock-alist new-seen) <call>)
      :hints ('(:expand (<call>)))
      :fn svex-assigns-find-clock-signals-rulelist)
    (defret mv-list-of-<fn>
      (equal (list clockp new-clock-alist new-seen) <call>)
      :hints ('(:expand (<call>)))
      :fn svex-assigns-find-clock-signals-rule)
    (defret mv-list-of-<fn>
      (equal (list clockp new-clock-alist new-seen) <call>)
      :hints ('(:expand (<call>)))
      :fn svex-assigns-find-clock-signals-rule-alternatives))

  (std::defret-mutual measure-decr-of-svex-assigns-find-clock-signals
    (defret measure-decr-of-<fn>
      (implies (svar-key-alist-p seen)
               (<= (len (set-difference-equal (svex-alist-keys assigns)
                                              (alist-keys new-seen)))
                   (len (set-difference-equal (svex-alist-keys assigns)
                                              (alist-keys seen)))))
      :hints ('(:expand (<call>)))
      :fn svex-assigns-find-clock-signals
      :rule-classes (:rewrite :linear))
    (defret measure-decr-of-<fn>
      (implies (svar-key-alist-p seen)
               (<= (len (set-difference-equal (svex-alist-keys assigns)
                                              (alist-keys new-seen)))
                   (len (set-difference-equal (svex-alist-keys assigns)
                                              (alist-keys seen)))))
      :hints ('(:expand (<call>)))
      :fn svex-assigns-find-clock-signals-rulelist
      :rule-classes (:rewrite :linear))
    (defret measure-decr-of-<fn>
      (implies (svar-key-alist-p seen)
               (<= (len (set-difference-equal (svex-alist-keys assigns)
                                              (alist-keys new-seen)))
                   (len (set-difference-equal (svex-alist-keys assigns)
                                              (alist-keys seen)))))
      :hints ('(:expand (<call>)))
      :fn svex-assigns-find-clock-signals-rule
      :rule-classes (:rewrite :linear))
    (defret measure-decr-of-<fn>
      (implies (svar-key-alist-p seen)
               (<= (len (set-difference-equal (svex-alist-keys assigns)
                                              (alist-keys new-seen)))
                   (len (set-difference-equal (svex-alist-keys assigns)
                                              (alist-keys seen)))))
      :hints ('(:expand (<call>)))
      :fn svex-assigns-find-clock-signals-rule-alternatives
      :rule-classes (:rewrite :linear)))
  
  (local (defthm assoc-eq-is-hons-assoc-equal-when-fnsym-svexlistlist-alist-p
           (implies (fnsym-svexlistlist-alist-p x)
                    (equal (assoc-equal k x) (hons-assoc-equal k x)))))

  (verify-guards svex-assigns-find-clock-signals))


(define svex-assigns-find-clock-signals-varlist ((vars svarlist-p)
                                                 (clock-alist svar-key-alist-p) ;; binds keys to T
                                                 (seen svar-key-alist-p)
                                                 (assigns svex-alist-p))
  :returns (mv (clock-vars svarlist-p)
               (clock-alist svar-key-alist-p)
               (seen svar-key-alist-p))
  (b* (((when (Atom vars))
        (mv nil (svar-key-alist-fix clock-alist)
            (svar-key-alist-fix seen)))
       ((mv clockp clock-alist seen)
        (svex-assigns-find-clock-signals (car vars) clock-alist seen assigns))
       ((unless clockp)
        (svex-assigns-find-clock-signals-varlist (cdr vars) clock-alist seen assigns))
       ((mv rest clock-alist seen)
        (svex-assigns-find-clock-signals-varlist (cdr vars) clock-alist seen assigns)))
    (mv (cons (svar-fix (car vars)) rest) clock-alist seen)))



#||
(b* ((assigns (make-fast-alist (flatnorm-res->assigns (svtv-data->flatnorm svtv-data))))
     ((mv clock-vars & &)
      (time$ (svex-assigns-find-clock-signals-varlist
              (svex-alist-keys assigns)
              (hons-acons "my_clk" t nil) nil assigns))))
  clock-vars)
||#
