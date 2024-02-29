; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2022 Intel Corporation
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

(include-book "svtv-data-obj-spec")
(include-book "svtv-stobj-export")
(include-book "override-common")
(include-book "override-envlist-defs")
(include-book "fsm-override-defs")
(local (include-book "std/alists/alist-keys" :dir :system))

(local (std::add-default-post-define-hook :fix))

(define alistlist-keys (x)
  (if (atom x)
      nil
    (cons (alist-keys (car x))
          (alistlist-keys (cdr x)))))


(define svtv-override-triplemap-refvar-keys ((x svtv-override-triplemap-p))
  (if (atom x)
      nil
    (if (and (mbt (and (consp (car x))
                       (svar-p (caar x))))
             (svtv-override-triple->refvar (cdar x)))
        (cons (caar x)
              (svtv-override-triplemap-refvar-keys (cdr x)))
      (svtv-override-triplemap-refvar-keys (cdr x))))
  ///
  (local (in-theory (enable svtv-override-triplemap-fix))))

(define svtv-override-triplemap-overridekeys-ok ((triplemap svtv-override-triplemap-p)
                                                 (namemap svtv-name-lhs-map-p)
                                                 (override-keys svarlist-p))
  ;; Checks whether all the keys of triplemap -- which are namemap keys as well
  ;; -- map in namemap to LHSes containing only vars that are in override-keys.
  :returns (ok)
  (acl2::hons-subset (svtv-name-lhs-map-vars
                      (fal-extract (svtv-override-triplemap-refvar-keys triplemap)
                                   (svtv-name-lhs-map-fix namemap)))
                     (svarlist-change-override override-keys nil)))

(define svtv-override-triplemaplist-overridekeys-ok ((triplemaps svtv-override-triplemaplist-p)
                                                     (namemap svtv-name-lhs-map-p)
                                                     (override-keys svarlist-p))
  (if (atom triplemaps)
      t
    (and (svtv-override-triplemap-overridekeys-ok (car triplemaps) namemap override-keys)
         (svtv-override-triplemaplist-overridekeys-ok (cdr triplemaps) namemap override-keys))))

(local (in-theory (disable acl2::hons-subset)))

(define svtv-override-triplemaplist-refvar-keys-subsetp ((triplemaps svtv-override-triplemaplist-p)
                                                         (test-alists svex-alistlist-p))
  :prepwork ((local (defthm hons-subset1-is-subsetp-alist-keys
                      (iff (acl2::hons-subset1 x a)
                           (subsetp-equal x (alist-keys a)))
                      :hints(("Goal" :in-theory (enable acl2::hons-subset1)))))
             (local (defthm alist-keys-when-svex-alist-p
                      (implies (svex-alist-p x)
                               (equal (alist-keys x)
                                      (svex-alist-keys x)))
                      :hints(("Goal" :in-theory (enable alist-keys svex-alist-keys))))))
  (if (atom triplemaps)
      t
    (and (mbe :logic (subsetp-equal (svtv-override-triplemap-refvar-keys (car triplemaps))
                                    (svex-alist-keys (car test-alists)))
              :exec (b* ((test-alist (car test-alists)))
                      (with-fast-alist test-alist
                        (acl2::hons-subset1 (svtv-override-triplemap-refvar-keys (car triplemaps)) test-alist))))
         (svtv-override-triplemaplist-refvar-keys-subsetp (cdr triplemaps) (cdr test-alists)))))

(define svtv-spec-override-syntax-checks ((spec svtv-spec-p)
                                          (overridekeys svarlist-p)
                                          (triplemaps svtv-override-triplemaplist-p))
  :returns (ok)
  (b* (((svtv-spec spec))
       (namemap spec.namemap)
       (in-alists spec.in-alists)
       (test-alists spec.override-test-alists)
       (val-alists spec.override-val-alists)
       (probes spec.probes)
       (outvars (svtv-probealist-outvars spec.probes))
       (my-in-alists (take (len outvars) in-alists))
       ((fsm spec.fsm)))
    (and (svtv-override-triplemaplist-syntax-check
          test-alists val-alists probes triplemaps)
         (equal (svex-alist-keys-list test-alists) (svex-alist-keys-list val-alists))
         (no-duplicatesp-each (svex-alist-keys-list test-alists))
         (no-duplicatesp-each (alistlist-keys (svtv-override-triplemaplist-fix triplemaps)))
         (svtv-override-triplemaplist-overridekeys-ok triplemaps namemap overridekeys)
         (svarlist-override-p (svtv-name-lhs-map-vars namemap) nil)
         (svtv-override-triplemaplist-refvar-keys-subsetp triplemaps test-alists)
         (svex-alistlist-check-monotonic my-in-alists)
         (<= (len test-alists) (len outvars))
         (svtv-cyclephaselist-unique-i/o-phase spec.cycle-phases)
         (svarlist-override-p (Svtv-cyclephaselist-keys spec.cycle-phases) nil)
         (svex-alist-check-monotonic spec.initst-alist)
         (svarlist-override-p (svex-alist-keys spec.fsm.nextstate) nil))))






;;; For each decomposition proof, we'll have a fixed set of signals overridden
;;; on both the spec and impl side.  On the spec side, this set of signals will
;;; likely be constant over several theorems that we want to compose together;
;;; this will be specified by svtv-override-triples-envs-match.  On the impl
;;; side, we'll have a more explicit env, not just a free variable with hyps
;;; but an alist constructed with cons/append/etc. We'll extract from this term
;;; a substitution which should contain all the constant bindings and bind all
;;; other variables to themselves, so that (svex-alist-eval subst env) ~= env.


;; The following functions say:
;; - Every triplemap test evaluated in env matches (1mask-equiv) its evaluation in spec.
;; - Every triplemap value evaluated in env is >>= its evaluation in spec.
(define svtv-override-triple-envs-match ((triple svtv-override-triple-p)
                                         (env svex-env-p)
                                         (spec svex-env-p))
  (b* (((svtv-override-triple triple)))
    (and (4vec-1mask-equiv (svex-eval triple.test env) (svex-eval triple.test spec))
         (4vec-<<= (svex-eval triple.val spec) (svex-eval triple.val env)))))

(define svtv-override-triplemap-envs-match ((triplemap svtv-override-triplemap-p)
                                            (env svex-env-p)
                                            (spec svex-env-p))
  :returns (ok)
  (if (atom triplemap)
      t
    (if (mbt (and (consp (car triplemap))
                  (svar-p (caar triplemap))))
        (and (svtv-override-triple-envs-match (cdar triplemap) env spec)
             (svtv-override-triplemap-envs-match (cdr triplemap) env spec))
      (svtv-override-triplemap-envs-match (cdr triplemap) env spec)))
  ///
  (defret <fn>-implies
    (implies (and ok
                  (svar-p key)
                  (hons-assoc-equal key triplemap))
             (b* ((triple (cdr (hons-assoc-equal key (svtv-override-triplemap-fix triplemap)))))
               (and (4vec-1mask-equiv (svex-eval (svtv-override-triple->test triple) env)
                           (svex-eval (svtv-override-triple->test triple) spec))
                    (4vec-<<= (svex-eval (svtv-override-triple->val triple) spec)
                              (svex-eval (svtv-override-triple->val triple) env)))))
    :hints(("Goal" :in-theory (enable svtv-override-triplemap-fix
                                      svtv-override-triple-envs-match))))

  (local (in-theory (enable svtv-override-triplemap-fix))))


(define svtv-override-triplemaplist-envs-match-aux ((triplemaps svtv-override-triplemaplist-p)
                                                    (env svex-env-p)
                                                    (spec svex-env-p))
  (if (atom triplemaps)
      t
    (and (svtv-override-triplemap-envs-match (car triplemaps) env spec)
         (svtv-override-triplemaplist-envs-match-aux (cdr triplemaps) env spec))))

;; BOZO see if we can disable this executable counterpart or something -- leads
;; to too many fast-alist discipline problems.
(define svtv-override-triplemaplist-envs-match ((triplemaps svtv-override-triplemaplist-p)
                                                (env svex-env-p)
                                                (spec svex-env-p))
  :parents (def-svtv-generalized-thm)
  :short "Checks that the given environment @('env') has values matching
@('spec') for the override test and value variables of the given triplemaplist
@('triplemaps')."
  :long "<p>An occurrence of this function is used by @(see
def-svtv-generalized-thm) as a hypothesis of the generalized theorems it
proves, serving to assume that the environment used in the SVTV run of the
theorem overrides exactly the signals it's supposed to, i.e. matching
@('spec').</p>

<p>This function returns true iff for every @(see svtv-override-triple) in
@('triplemaps'), the evaluation of the @('test') field on @('env') equals its
evaluation on @('spec'), and the evaluation of the @('val') field on @('spec')
is @(see 4vec-<<=) its evaluation on @('env'). In the current framework each
@('test') and @('val') expression is always either a constant or variable.  For
constants, the conditions are automatically true, and for variables the
bindings in @('env') and @('spec') must be compared.</p>

<p>When instantiating a generalized SVTV theorem (as produced by @(see
def-svtv-generalized-thm) to prove something about an SVTV run on a more
particular environment,  there are a couple of helpful rewriting strategies.</p>

<ul>

<li>@('svtv-override-triplemaplist-envs-match-simplify') applies when @('env')
is a term containing a list of pairs with constant keys and (as is usually the
case) @('spec') is a constant.  It simplifies the call of
@('svtv-override-triplemaplist-envs-match') to a call of
 @('svtv-override-triplelist-envs-match') on a smaller set of triples, only the ones
that couldn't be resolved by just examining the syntax of the @('env') and
@('spec') terms.  Then, @('svtv-override-triplelist-envs-match') has rules to
open up and solve the requirements for the remaining triples.</li>

<li>@('svtv-override-triplemaplist-envs-match-remove-irrelevant-pair-top') can
simplify @('env') terms containing irrelevant pairs, i.e. those that aren't
test or value variables of the triplemaps.</li>

</ul>"
  :verify-guards nil
  (mbe :logic (if (atom triplemaps)
                  t
                (and (svtv-override-triplemap-envs-match (car triplemaps) env spec)
                     (svtv-override-triplemaplist-envs-match (cdr triplemaps) env spec)))
       :exec (with-fast-alist env
               (with-fast-alist spec
                 (svtv-override-triplemaplist-envs-match-aux triplemaps env spec))))
  ///
  (local (defthm svtv-override-triplemaplist-envs-match-aux-elim
           (equal (svtv-override-triplemaplist-envs-match-aux triplemaps env spec)
                  (svtv-override-triplemaplist-envs-match triplemaps env spec))
           :hints(("Goal" :in-theory (enable svtv-override-triplemaplist-envs-match-aux)))))

  (verify-guards svtv-override-triplemaplist-envs-match))

(define svex-alist-noncall-p ((x svex-alist-p))
  (if (atom x)
      t
    (if (mbt (and (consp (car x)) (svar-p (caar x))))
        (and (not (svex-case (cdar x) :call))
             (svex-alist-noncall-p (cdr x)))
      (svex-alist-noncall-p (cdr x))))
  ///
  (local (in-theory (enable svex-alist-fix))))


(define svex-alistlist-noncall-p ((x svex-alistlist-p))
  (if (atom x)
      t
    (and (svex-alist-noncall-p (car x))
         (svex-alistlist-noncall-p (cdr x)))))



(define svtv-probealist-vars ((x svtv-probealist-p))
  :returns (vars svarlist-p)
  (if (atom x)
      nil
    (if (mbt (consp (car x)))
        (cons (svtv-probe->signal (cdar x))
              (svtv-probealist-vars (cdr x)))
      (svtv-probealist-vars (cdr x))))
  ///
  (local (in-theory (enable svtv-probealist-fix))))

(define svtv-spec-fsm-syntax-check ((x svtv-spec-p))
  (b* (((svtv-spec x))
       (len (len (svtv-probealist-outvars x.probes)))
       (x.in-alists (take len x.in-alists))
       (x.override-val-alists (take len x.override-val-alists))
       (x.override-test-alists (take len x.override-test-alists)))
    (and (svex-alistlist-noncall-p x.in-alists)
         (svex-alistlist-noncall-p x.override-val-alists)
         (svex-alistlist-noncall-p x.override-test-alists)
         (no-duplicatesp-each (svex-alist-keys-list x.in-alists))
         (no-duplicatesp-each (svex-alist-keys-list x.override-val-alists))
         (equal (svex-alist-keys-list x.override-val-alists)
                (svex-alist-keys-list x.override-test-alists))
         (svarlist-override-p (svtv-name-lhs-map-vars x.namemap) nil)
         (acl2::hons-subset (svtv-probealist-vars x.probes) (alist-keys x.namemap)))))


(define svex-alist-all-xes-p ((x svex-alist-p))
  (if (atom x)
      t
    (if (mbt (and (consp (car x)) (svar-p (caar x))))
        (and (svex-equiv (cdar x) (svex-x))
             (svex-alist-all-xes-p (cdr x)))
      (svex-alist-all-xes-p (cdr x))))
  ///
  (local (in-theory (enable svex-alist-fix))))



(local (in-theory (disable acl2::hons-union)))

(define svtv-overridekeys-full ((override-test-alists svex-alistlist-p)
                                (namemap svtv-name-lhs-map-p))
  (if (atom override-test-alists)
      nil
    (acl2::hons-union (svtv-name-lhs-map-vars
                       (fal-extract (svex-alist-keys (car override-test-alists))
                                    (svtv-name-lhs-map-fix namemap)))
                      (svtv-overridekeys-full (cdr override-test-alists) namemap))))



(define svtv-override-triplemaplist-overridekeys ((triplemaps svtv-override-triplemaplist-p)
                                                  (namemap svtv-name-lhs-map-p))
  (if (atom triplemaps)
      nil
    (acl2::hons-union (svtv-name-lhs-map-vars
                       (fal-extract (svtv-override-triplemap-refvar-keys (car triplemaps))
                                    (svtv-name-lhs-map-fix namemap)))
                      (svtv-override-triplemaplist-overridekeys (cdr triplemaps) namemap)))
  ///
  (local (in-theory (enable svtv-override-triplemaplist-fix))))

; Matt K. mod: Avoid ACL2(p) error.
(acl2::set-waterfall-parallelism nil)

(define 4vec-non-x-p ((x 4vec-p))
  (b* (((4vec x)))
    (equal (logandc2 x.upper x.lower) 0))
  ///
  (local (include-book "centaur/bitops/ihsext-basics" :dir :system))
  (local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
  (defthmd 4vec-<<=-when-4vec-non-x-p
    (implies (4vec-non-x-p x)
             (equal (4vec-<<= x y)
                    (4vec-equiv x y)))
    :hints(("Goal" :in-theory (enable 4vec-<<= 4vec-fix-is-4vec-of-fields))
           (bitops::logbitp-reasoning))))



(defthmd svex-env-lookup-when-non-x-p-and-<<=
  (implies (and (svex-env-<<= env1 env2)
                (4vec-non-x-p (svex-env-lookup k env1)))
           (equal (svex-env-lookup k env2)
                  (svex-env-lookup k env1)))
  :hints(("Goal" :use ((:instance svex-env-<<=-necc (x env1) (y env2) (var k)))
          :in-theory (e/d (4vec-<<=-when-4vec-non-x-p)
                          (svex-env-<<=-necc)))))

(define svex-env-non-x-p ((x svex-env-p))
  (if (atom x)
      t
    (and (or (not (mbt (and (consp (car x))
                            (svar-p (caar x)))))
             (4vec-non-x-p (cdar x)))
         (svex-env-non-x-p (cdr x))))
  ///
  (local (include-book "std/lists/sets" :dir :system))
  (defthmd lookup-when-svex-env-non-x-p
    (implies (and (svex-env-non-x-p x)
                  (svex-env-boundp k x))
             (4vec-non-x-p (svex-env-lookup k x)))
    :hints(("Goal" :in-theory (enable svex-env-boundp svex-env-lookup
                                      hons-assoc-equal))))


  (defthmd svex-env-reduce-when-svex-env-non-x-p-and-<<=
    (implies (and (svex-env-non-x-p (svex-env-reduce vars env1))
                  (svex-env-<<= env1 env2)
                  (set-equiv (alist-keys (svex-env-fix env1)) (alist-keys (svex-env-fix env2))))
             (equal (svex-env-reduce vars env1)
                    (svex-env-reduce vars env2)))
    :hints(("Goal" :in-theory (enable svex-env-reduce-redef
                                      svex-env-boundp-iff-member-alist-keys
                                      svex-env-lookup-when-non-x-p-and-<<=)
            :induct (len vars))))

  (local (in-theory (enable svex-env-fix))))



(define svarlist-delay-p ((x svarlist-p))
  (if (atom x)
      t
    (and (not (equal 0 (svar->delay (car x))))
         (svarlist-delay-p (cdr x))))
  ///
  (defthmd not-svarlist-delay-p-by-member
    (implies (and (equal xfix (svarlist-fix x))
                  (member-equal v xfix)
                  (equal 0 (svar->delay v)))
             (not (svarlist-delay-p x))))

  (defthmd not-svarlist-delay-p-by-member-nofix
    (implies (and (member-equal v x)
                  (equal 0 (svar->delay v)))
             (not (svarlist-delay-p x)))))


(define svarlist-nondelay-p ((x svarlist-p))
  (if (atom x)
      t
    (and (equal 0 (svar->delay (car x)))
         (svarlist-nondelay-p (cdr x))))
  ///
  (defthmd not-svarlist-nondelay-p-by-member
    (implies (and (equal xfix (svarlist-fix x))
                  (member-equal v xfix)
                  (not (equal 0 (svar->delay v))))
             (not (svarlist-nondelay-p x))))

  (defthmd not-svarlist-nondelay-p-by-member-nofix
    (implies (and (member-equal v x)
                  (not (equal 0 (svar->delay v))))
             (not (svarlist-nondelay-p x))))
  
  (defthmd intersectp-of-delay/nondelay
    (implies (and (svarlist-delay-p x)
                  (svarlist-nondelay-p y))
             (not (intersectp-equal x y)))
    :hints (("goal" :in-theory (e/d (not-svarlist-nondelay-p-by-member-nofix
                                     (:i svarlist-delay-p))
                                    ((:d svarlist-delay-p)
                                     (:d svarlist-nondelay-p)
                                     acl2::intersectp-equal-commute)))
            (and stable-under-simplificationp
                 '(:induct (svarlist-delay-p x)
                   :expand ((svarlist-delay-p x)
                            (intersectp-equal x y))))))

  (defthm svarlist-nondelay-p-of-append
    (iff (svarlist-nondelay-p (append x y))
         (and (svarlist-nondelay-p x)
              (svarlist-nondelay-p y)))))

