; Centaur SV Hardware Verification Tutorial
; Copyright (C) 2016 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "SV")
(include-book "resolve")
(include-book "expand")
(include-book "fsm-base")
(include-book "../svex/rewrite-base")
(include-book "std/alists/alist-defuns" :dir :system)
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/osets/element-list" :dir :system))
(local (deflist svarlist
         :elt-type svar
         :true-listp t
         :elementp-of-nil nil))
(local (std::add-default-post-define-hook :fix))


(local (in-theory (disable hons-dups-p)))




(define svtv-namemap->lhsmap ((x svtv-namemap-p
                                 "User-provided mapping.  An alist where the keys
                                  are arbitary names (svars, typically symbols)
                                  and the values are SystemVerilog-syntax hierarchical
                                  names (strings).")
                              (modidx natp)
                              (moddb moddb-ok)
                              (aliases))
  :parents (svtv-name-lhs-map)
  :short "Processes a list of nicknames for SystemVerilog-syntax signals into an internal form."
  :long "<p></p>"
  :guard (svtv-mod-alias-guard modidx moddb aliases)
  :returns (mv errs
               (lhses svtv-name-lhs-map-p))
  (b* (((when (atom x)) (mv nil nil))
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svtv-namemap->lhsmap (cdr x) modidx moddb aliases))
       ((mv err1 first) (svtv-wire->lhs! (cdar x) modidx moddb aliases))
       ((mv errs rest) (svtv-namemap->lhsmap (cdr x) modidx moddb aliases))
       ((when err1) (mv (append-without-guard err1 errs) rest)))
    (mv errs (cons (cons (caar x) first) rest)))
  ///
  (local (in-theory (enable svtv-namemap-fix))))


;; (define lhs-value/mask-to-svtv-assigns ((lhs lhs-p)
;;                                         (val 4vec-p)
;;                                         (mask 4vec-p)
;;                                         (updates svex-alist-p))
;;   :returns (assigns 4vec-assigns-p)
;;   (b* (((when (atom lhs))
;;         nil)
;;        ((lhrange x) (lhrange-fix (car lhs))))
;;     (lhatom-case x.atom
;;       :z (lhs-value-to-svtv-assigns (cdr lhs)
;;                                     (svex-rsh x.w val)
;;                                     updates)
;;       :var (b* ((overridep (svex-lookup x.atom.name updates))
;;                 ((unless overridep)
;;                  (cons (cons (list x)
;;                              (make-4vec-driver :value val))
;;                        (lhs-value/mask-to-svtv-assigns (cdr lhs)
;;                                                        (4vec-rsh x.w val)
;;                                                        updates))))
;;              (cons (cons (list (change-lhrange
;;                                 x
;;                                 :atom (change-lhatom-var
;;                                        x.atom
;;                                        :name (change-svar x.atom.name :override-test t))))
;;                          (make-driver :value -1))
;;                    (cons (cons (list (change-lhrange
;;                                       x
;;                                       :atom (change-lhatom-var
;;                                              x.atom
;;                                              :name (change-svar x.atom.name :override-val t))))
;;                                (make-driver :value val))
;;                          (lhs-value-to-svtv-assigns (cdr lhs)
;;                                                   (svex-rsh x.w val)
;;                                                   updates)))))))

(local (defthmd equal-of-svar->name
         (implies (and (svar-p x)
                       (svar-p y)
                       (equal (svar->delay x) (svar->delay y))
                       (equal (svar->nonblocking x) (svar->nonblocking y))
                       (equal (svar->override-val x) (svar->override-val y))
                       (equal (svar->override-test x) (svar->override-test y)))
                  (equal (equal (svar->name x) (svar->name y))
                         (equal x y)))
         :hints (("goal" :use ((:instance svar-fix-redef (x x))
                               (:instance svar-fix-redef (x y)))
                  :in-theory (disable svar-of-fields
                                      equal-of-svar)))))


(define lhs-to-overrideval-lhs ((lhs lhs-p)
                                (updates svex-alist-p))
  :returns (val-lhs lhs-p)
  (if (atom lhs)
      nil
    (b* (((lhrange x) (lhrange-fix (car lhs))))
      (lhatom-case x.atom
        :z (cons x (lhs-to-overrideval-lhs (cdr lhs) updates))
        :var (b* ((overridep (svex-fastlookup x.atom.name updates))
                  ;; ((unless overridep)
                  ;;  (cons x (lhs-to-overrideval-lhs (cdr lhs) updates)))
                  )
               (cons (change-lhrange x
                                     :atom (change-lhatom-var
                                            x.atom
                                            :name (change-svar x.atom.name
                                                               :override-val (and overridep t)
                                                               :override-test nil)))
                     (lhs-to-overrideval-lhs (cdr lhs) updates))))))
  ///
  

  ;; (defret vars-of-lhs-to-overrideval-lhs
  ;;   (implies (and (not (member x (lhs-vars lhs)))
  ;;                 (not (and (svar->override-val x)
  ;;                           (member (change-svar x :override-val nil) (lhs-vars lhs)))))
  ;;            (not (member x (lhs-vars val-lhs))))
  ;;   :hints(("Goal" :in-theory (enable lhs-vars lhatom-vars
  ;;                                     equal-of-svar->name))))

  (defret override-test-var-of-overrideval-lhs
    (implies (svar->override-test x)
             (not (member x (lhs-vars val-lhs))))
    :hints(("Goal" :in-theory (enable lhs-vars lhatom-vars))))

  (defcong svex-alist-eval-equiv equal (lhs-to-overrideval-lhs lhs updates) 2))



(define lhs-to-overridetest-lhs ((lhs lhs-p)
                                 (updates svex-alist-p))
  :returns (val-lhs lhs-p)
  (if (atom lhs)
      nil
    (b* (((lhrange x) (lhrange-fix (car lhs))))
      (lhatom-case x.atom
        :z (cons x (lhs-to-overridetest-lhs (cdr lhs) updates))
        :var (b* ((overridep (svex-fastlookup x.atom.name updates))
                  ((unless overridep)
                   (cons (change-lhrange x :atom (lhatom-z))
                         (lhs-to-overridetest-lhs (cdr lhs) updates))))
               (cons (change-lhrange x
                                     :atom (change-lhatom-var
                                            x.atom
                                            :name (change-svar x.atom.name :override-test t
                                                               :override-val nil)))
                     (lhs-to-overridetest-lhs (cdr lhs) updates))))))
  ///
  

  ;; (defret vars-of-lhs-to-overridetest-lhs
  ;;   (implies (and (not (member (change-svar x :override-test nil) (lhs-vars lhs)))
  ;;                 (not (member x (lhs-vars lhs))))
  ;;            (not (member x (lhs-vars val-lhs))))
  ;;   :hints(("Goal" :in-theory (enable lhs-vars lhatom-vars
  ;;                                     equal-of-svar->name))))

  (defret vars-of-lhs-to-overridetest-lhs-when-not-override
    (implies (not (svar->override-test x))
             (not (member x (lhs-vars val-lhs))))
    :hints(("Goal" :in-theory (enable lhs-vars lhatom-vars
                                      equal-of-svar->name))))

  (defcong svex-alist-eval-equiv equal (lhs-to-overridetest-lhs lhs updates) 2))


(define 4vec-assigns-to-overrideval-assigns ((x 4vec-assigns-p)
                                             (updates svex-alist-p))
  :returns (new-x 4vec-assigns-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (consp (car x))))
        (4vec-assigns-to-overrideval-assigns (cdr x) updates))
       ((cons lhs val) (car x)))
    (cons (cons (lhs-to-overrideval-lhs lhs updates) (4vec-driver-fix val))
          (4vec-assigns-to-overrideval-assigns (cdr x) updates)))
  ///
  (defret vars-of-<fn>
    (implies (svar->override-test v)
             (not (member v (lhslist-vars (alist-keys new-x)))))
    :hints(("Goal" :in-theory (enable lhslist-vars alist-keys))))

  (local (in-theory (enable 4vec-assigns-fix)))
  
  (defcong svex-alist-eval-equiv equal (4vec-assigns-to-overrideval-assigns x updates) 2))

(define 4vec-assigns-to-overridetest-assigns ((x 4vec-assigns-p)
                                             (updates svex-alist-p))
  :returns (new-x 4vec-assigns-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (consp (car x))))
        (4vec-assigns-to-overridetest-assigns (cdr x) updates))
       ((cons lhs val) (car x)))
    (cons (cons (lhs-to-overridetest-lhs lhs updates) (4vec-driver-fix val))
          (4vec-assigns-to-overridetest-assigns (cdr x) updates)))
  ///

  (defret vars-of-<fn>-when-not-override-test
    (implies (not (svar->override-test v))
             (not (member v (lhslist-vars (alist-keys new-x)))))
    :hints(("Goal" :in-theory (enable lhslist-vars alist-keys))))

  (local (in-theory (enable 4vec-assigns-fix)))
  (defcong svex-alist-eval-equiv equal (4vec-assigns-to-overridetest-assigns x updates) 2))

    





(local (defthmd member-lhs-vars-of-lookup-when-alist-vals-of-svtv-name-lhs-map
         (implies (and (not (member v (lhslist-vars (alist-vals (svtv-name-lhs-map-fix x)))))
                       (svar-p key))
                  (not (member-equal v (lhs-vars (cdr (hons-assoc-equal key x))))))
         :hints(("Goal" :in-theory (enable alist-vals svtv-name-lhs-map-fix
                                           lhslist-vars)))))


(define svtv-env-to-4vec-assigns
  ((env svex-env-p
        "The assignment given by the user -- keys are either named variables in the
         lhsmap, or else override-val svars that refer to raw wires not in the namemap.")
   (map svtv-name-lhs-map-p
        "Mapping from user names to canonical signal LHSes"))
  :returns (assigns 4vec-assigns-p)
  (b* (((when (atom env))
        nil)
       ((unless (mbt (and (consp (car env))
                          (svar-p (caar env)))))
        (svtv-env-to-4vec-assigns (cdr env) map))
       ((cons (svar var) val) (car env))
       ((when var.override-val)
        ;; This is intended as a raw input assignment, not a renamed one, and
        ;; is skipped for our purposes here.
        (svtv-env-to-4vec-assigns (cdr env) map))
       (look (hons-get var map))
       ((unless look)
        (er hard? 'svtv-env-to-4vec-assigns
            "No signal named ~x0 in map.")
        (svtv-env-to-4vec-assigns (cdr env) map))
       (lhs (lhs-fix (cdr look)))
       ;; (test-lhs (lhs-to-overridetest-lhs lhs updates))
       ;; (test-look (hons-assoc-equal var tests))
       ;; (test (if test-look (cdr test-look) -1))
       )
    (cons (cons lhs (make-4vec-driver :value val))
          ;; (cons (cons test-lhs (make-4vec-driver :value test))
          (svtv-env-to-4vec-assigns (cdr env) map)))
  ///
  (defret vars-of-<fn>
    (implies (not (member v (lhslist-vars (alist-vals (svtv-name-lhs-map-fix map)))))
             (not (member v (lhslist-vars (alist-keys assigns)))))
    :hints(("Goal" :in-theory (enable alist-keys lhslist-vars
                                      member-lhs-vars-of-lookup-when-alist-vals-of-svtv-name-lhs-map))))

  (local (in-theory (enable svex-env-fix))))


(define svtv-subst-to-assigns
  ((subst svex-alist-p
        "The substitution given by the user -- keys are named variables in the
         lhsmap.")
   (map svtv-name-lhs-map-p
        "Mapping from user names to canonical signal LHSes"))
  :returns (assigns assigns-p)
  (b* (((when (atom subst))
        nil)
       ((unless (mbt (and (consp (car subst))
                          (svar-p (caar subst)))))
        (svtv-subst-to-assigns (cdr subst) map))
       ((cons (svar var) val) (car subst))
       ((when var.override-val)
        (svtv-subst-to-assigns (cdr subst) map))
       (look (hons-get var map))
       ((unless look)
        (er hard? 'svtv-subst-to-assigns
            "No signal named ~x0 in map.")
        (svtv-subst-to-assigns (cdr subst) map))
       (lhs (lhs-fix (cdr look)))
       ;; (test-lhs (lhs-to-overridetest-lhs lhs updates))
       ;; (test-look (hons-assoc-equal var tests))
       ;; (test (if test-look (cdr test-look) -1))
       )
    (cons (cons lhs (make-driver :value val))
          ;; (cons (cons test-lhs (make-4vec-driver :value test))
          (svtv-subst-to-assigns (cdr subst) map)))
  ///
  (defret vars-of-<fn>
    (implies (not (member v (lhslist-vars (alist-vals (svtv-name-lhs-map-fix map)))))
             (not (member v (lhslist-vars (alist-keys assigns)))))
    :hints(("Goal" :in-theory (enable alist-keys lhslist-vars
                                      member-lhs-vars-of-lookup-when-alist-vals-of-svtv-name-lhs-map))))

  (defret svex-vars-of-<fn>
    (implies (not (member v (svex-alist-vars subst)))
             (not (member v (driverlist-vars (alist-vals assigns)))))
    :hints(("Goal" :in-theory (enable alist-vals svex-alist-vars driverlist-vars))))

  (defret eval-of-<fn>
    (equal (assigns-eval assigns env)
           (svtv-env-to-4vec-assigns (svex-alist-eval subst env) map))
    :hints(("Goal" :in-theory (enable svtv-env-to-4vec-assigns
                                      driver-eval
                                      svex-alist-eval assigns-eval))))

  (local (in-theory (enable svex-alist-fix))))


;; (define svtv-overridetests-to-4vec-assigns
;;   ((tests svex-env-p
;;           "Assignments to override test (mask) vectors given by the user.  These
;;            override the default behavior in which any variable present in env has
;;            its override test set to all 1s.  Any key of tests that is not a key
;;            of env will be ignored.")
;;    (map svtv-name-lhs-map-p
;;         "Mapping from user names to canonical signal LHSes")
;;    (updates svex-alist-p
;;             "Update functions for internal signals"))
;;   :returns (assigns 4vec-assigns-p)
;;   (b* (((when (atom tests))
;;         nil)
;;        ((unless (mbt (and (consp (car tests))
;;                           (svar-p (caar tests)))))
;;         (svtv-overridetests-to-4vec-assigns (cdr tests) map updates))
;;        ((cons var test) (car tests))
;;        (look (hons-get var map))
;;        ((unless look)
;;         (er hard? 'svtv-overridetests-to-4vec-assigns
;;             "No signal named ~x0 in map.")
;;         (svtv-overridetests-to-4vec-assigns (cdr tests) map updates))
;;        (lhs (cdr look))
;;        (test-lhs (lhs-to-overridetest-lhs lhs updates))
;;        ;; (test-lhs (lhs-to-overridetest-lhs lhs updates))
;;        ;; (test-look (hons-assoc-equal var tests))
;;        ;; (test (if test-look (cdr test-look) -1))
;;        )
;;     (cons (cons test-lhs (make-4vec-driver :value test))
;;           (svtv-overridetests-to-4vec-assigns (cdr tests) map updates)))
;;   ///
;;   (defret vars-of-<fn>
;;     (implies (and (not (member v (lhslist-vars (alist-vals (svtv-name-lhs-map-fix map)))))
;;                   (not (and (svar->override-test v)
;;                             (member (change-svar v :override-test nil)
;;                                     (lhslist-vars (alist-vals (svtv-name-lhs-map-fix map)))))))
;;              (not (member v (lhslist-vars (alist-keys assigns)))))
;;     :hints(("Goal" :in-theory (enable alist-keys lhslist-vars
;;                                       member-lhs-vars-of-lookup-when-alist-vals-of-svtv-name-lhs-map))))

;;   (local (in-theory (enable svex-env-fix))))


(define svtv-assignment-to-4vec-assigns
  ((env svex-env-p
        "The assignment given by the user -- keys are named variables in the
         lhsmap.")
   (tests svex-env-p
          "Assignments to override test (mask) vectors given by the user.  These
           override the default behavior in which any variable present in env has
           its override test set to all 1s.  Any key of tests that is not a key
           of env will be ignored.")
   (map svtv-name-lhs-map-p
        "Mapping from user names to canonical signal LHSes")
   (updates svex-alist-p
            "Update functions for internal signals"))
  :returns (assigns 4vec-assigns-p)
  (b* (((when (atom env))
        nil)
       ((unless (mbt (and (consp (car env))
                          (svar-p (caar env)))))
        (svtv-assignment-to-4vec-assigns (cdr env) tests map updates))
       ((cons var val) (car env))
       (look (hons-get var map))
       ((unless look)
        (er hard? 'svtv-assignment-to-4vec-assigns
            "No signal named ~x0 in map.")
        (svtv-assignment-to-4vec-assigns (cdr env) tests map updates))
       (lhs (cdr look))
       (val-lhs (lhs-to-overrideval-lhs lhs updates))
       (test-lhs (lhs-to-overridetest-lhs lhs updates))
       (test-look (hons-assoc-equal var tests))
       (test (if test-look (cdr test-look) -1)))
    (cons (cons val-lhs (make-4vec-driver :value val))
          (cons (cons test-lhs (make-4vec-driver :value test))
                (svtv-assignment-to-4vec-assigns (cdr env) tests map updates))))
  ///
  (local (in-theory (enable svex-env-fix))))
       

;; (define svtv-subst-to-assigns
;;   ((env svex-alist-p
;;         "The (symbolic) assignment given by the user -- keys are named variables
;;          in the lhsmap.")
;;    (tests svex-alist-p
;;           "(Symbolic) assignments to override test (mask) vectors given by the user.  These
;;            override the default behavior in which any variable present in env has
;;            its override test set to all 1s.  Any key of tests that is not a key
;;            of env will be ignored.")
;;    (map svtv-name-lhs-map-p
;;         "Mapping from user names to canonical signal LHSes")
;;    (updates svex-alist-p
;;             "Update functions for internal signals"))
;;   :returns (assigns assigns-p)
;;   (b* (((when (atom env))
;;         nil)
;;        ((unless (mbt (and (consp (car env))
;;                           (svar-p (caar env)))))
;;         (svtv-subst-to-assigns (cdr env) tests map updates))
;;        ((cons var val) (car env))
;;        (look (hons-get var map))
;;        ((unless look)
;;         (er hard? 'svtv-subst-to-assigns
;;             "No signal named ~x0 in map.")
;;         (svtv-subst-to-assigns (cdr env) tests map updates))
;;        (lhs (cdr look))
;;        (val-lhs (lhs-to-overrideval-lhs lhs updates))
;;        (test-lhs (lhs-to-overridetest-lhs lhs updates))
;;        (test-look (hons-assoc-equal var tests))
;;        (test (if test-look (cdr test-look) (svex-quote -1))))
;;     (cons (cons val-lhs (make-driver :value val))
;;           (cons (cons test-lhs (make-driver :value test))
;;                 (svtv-subst-to-assigns (cdr env) tests map updates))))
;;   ///
;;   (local (defthm hons-assoc-equal-of-svex-alist-eval
;;            (equal (hons-assoc-equal key (svex-alist-eval x env))
;;                   (and (svar-p key)
;;                        (let ((look (hons-assoc-equal key x)))
;;                          (and look
;;                               (cons key (svex-eval (cdr look) env))))))
;;            :hints(("Goal" :in-theory (enable svex-alist-eval)))))

;;   (defret <fn>-correct
;;     (equal (assigns-eval assigns ee)
;;            (svtv-assignment-to-4vec-assigns
;;             (svex-alist-eval env ee)
;;             (svex-alist-eval tests ee)
;;             map updates))
;;     :hints(("Goal" :in-theory (enable svex-alist-eval
;;                                       assigns-eval
;;                                       svtv-assignment-to-4vec-assigns)
;;             :induct t)
;;            (and stable-under-simplificationp
;;                 '(:in-theory (enable driver-eval)))))
  
;;   (local (in-theory (enable svex-alist-fix))))

(define lhs-nonoverride-p ((x lhs-p))
  (if (atom x)
      t
    (and (b* (((lhrange x1) (car x)))
           (lhatom-case x1.atom
             :z t
             :var (and (not (svar->override-test x1.atom.name))
                       (not (svar->override-val x1.atom.name)))))
         (lhs-nonoverride-p (cdr x))))
  ///
  (defthmd override-test-member-when-lhs-nonoverride-p
    (implies (and (svar->override-test v)
                  (lhs-nonoverride-p x))
             (not (member v (lhs-vars x))))
    :hints(("Goal" :in-theory (enable lhs-vars lhatom-vars))))

  (defthmd override-val-member-when-lhs-nonoverride-p
    (implies (and (svar->override-val v)
                  (lhs-nonoverride-p x))
             (not (member v (lhs-vars x))))
    :hints(("Goal" :in-theory (enable lhs-vars lhatom-vars)))))

(define lhslist-nonoverride-p ((x lhslist-p))
  (if (atom x)
      t
    (and (lhs-nonoverride-p (car x))
         (lhslist-nonoverride-p (cdr x))))
  ///
  (defthmd override-test-member-when-lhslist-nonoverride-p
    (implies (and (svar->override-test v)
                  (lhslist-nonoverride-p x))
             (not (member v (lhslist-vars x))))
    :hints(("Goal" :in-theory (enable lhslist-vars override-test-member-when-lhs-nonoverride-p))))

  (defthmd override-val-member-when-lhslist-nonoverride-p
    (implies (and (svar->override-val v)
                  (lhslist-nonoverride-p x))
             (not (member v (lhslist-vars x))))
    :hints(("Goal" :in-theory (enable lhslist-vars override-val-member-when-lhs-nonoverride-p)))))

(define lhs-nonoverride-fix ((x lhs-p))
  :returns (new-x lhs-p)
  (if (atom x)
      nil
    (cons (b* (((lhrange x1) (lhrange-fix (car x))))
            (lhatom-case x1.atom
              :z x1
              :var (change-lhrange x1
                                   :atom (change-lhatom-var x1.atom
                                                            :name
                                                            (change-svar x1.atom.name
                                                                         :override-val nil
                                                                         :override-test nil)))))
          (lhs-nonoverride-fix (cdr x))))
  ///
  (local (in-theory (enable lhs-nonoverride-p)))

  (defret lhs-nonoverride-p-of-<fn>
    (lhs-nonoverride-p new-x))

  (defret <fn>-when-lhs-nonoverride-p
    (implies (lhs-nonoverride-p x)
             (equal new-x (lhs-fix x)))))

(define lhslist-nonoverride-fix ((x lhslist-p))
  :returns (new-x lhslist-p)
  (if (atom x)
      nil
    (cons (lhs-nonoverride-fix (car x))
          (lhslist-nonoverride-fix (cdr x))))
  ///
  (local (in-theory (enable lhslist-nonoverride-p)))

  (defret lhslist-nonoverride-p-of-<fn>
    (lhslist-nonoverride-p new-x))

  (defret <fn>-when-lhslist-nonoverride-p
    (implies (lhslist-nonoverride-p x)
             (equal new-x (lhslist-fix x))))

  (defret len-of-<fn>
    (equal (len new-x) (len x))))

(local (defthm lhslist-p-of-alist-vals
         (implies (svtv-name-lhs-map-p x)
                  (lhslist-p (alist-vals x)))
         :hints(("Goal" :in-theory (enable svtv-name-lhs-map-p
                                           lhslist-p alist-vals)))))

(local (defthm svarlist-p-of-alist-keys
         (implies (svtv-name-lhs-map-p x)
                  (svarlist-p (alist-keys x)))
         :hints(("Goal" :in-theory (enable svtv-name-lhs-map-p
                                          alist-keys)))))

(local (defthm svtv-name-lhs-map-p-of-pairlis$
         (implies (and (svarlist-p keys) (lhslist-p vals))
                  (svtv-name-lhs-map-p (pairlis$ keys vals)))))

(local (defthm alist-vals-of-pairlis$
         (equal (alist-vals (pairlis$ x y))
                (take (len x) y))
         :hints(("Goal" :in-theory (enable alist-vals)))))


(local (defthm take-when-len-equal
         (implies (equal (len x) (nfix n))
                  (equal (take n x) (list-fix x)))))

(local (defthm len-alist-vals
         (equal (len (alist-vals x))
                (len (alist-keys x)))
         :hints(("Goal" :in-theory (enable alist-keys alist-vals)))))

(local (defthm pairlis-alist-keys-alist-vals
         (equal (pairlis$ (alist-keys x) (alist-vals x))
                (alist-fix x))
         :hints(("Goal" :in-theory (enable alist-fix alist-keys alist-vals)))))

(local (defthm alistp-of-svtv-name-lhs-map-fix
         (alistp (svtv-name-lhs-map-fix x))))

(define svtv-name-lhs-map-nonoverride-fix ((x svtv-name-lhs-map-p))
  :returns (new-x svtv-name-lhs-map-p)
  (b* ((x (svtv-name-lhs-map-fix x)))
    (pairlis$ (alist-keys x)
              (lhslist-nonoverride-fix (alist-vals x))))
  ///
  (defret lhslist-nonoverride-p-of-<fn>
    (lhslist-nonoverride-p (alist-vals new-x)))

  (defret <fn>-when-lhslist-nonoverride-p
    (implies (lhslist-nonoverride-p (alist-vals (svtv-name-lhs-map-fix x)))
             (equal new-x (svtv-name-lhs-map-fix x)))))


(local (include-book "tools/trivial-ancestors-check" :dir :system))


(local (acl2::use-trivial-ancestors-check))

(local (defthm svex-concat-of-quotes
         (implies (and (svex-case x :quote)
                       (svex-case y :quote))
                  (svex-case (svex-concat w x y) :quote))
         :hints(("Goal" :in-theory (enable svex-concat)))))

(local (defthm svex-rsh-of-quote
         (implies (svex-case x :quote)
                  (svex-case (svex-rsh w x) :quote))
         :hints(("Goal" :in-theory (enable svex-rsh)))))



(define svarlist-override-tests-match ((x svarlist-p) (val booleanp))
  (if (atom x)
      t
    (and (mbe :logic (iff (svar->override-test (car x)) val)
              :exec (eq (svar->override-test (car x)) val))
         (svarlist-override-tests-match (cdr x) val))))

(define svarlist-override-tests-match-badguy ((x svarlist-p) (val booleanp))
  :returns (badguy svar-p)
  (if (atom x)
      (make-svar :override-test (not val))
    (if (mbe :logic (iff (svar->override-test (car x)) val)
             :exec (eq (svar->override-test (car x)) val))
        (svarlist-override-tests-match-badguy (cdr x) val)
      (svar-fix (car x))))
  ///
  (local (in-theory (enable svarlist-override-tests-match)))

  (defret override-test-of-<fn>
    (equal (svar->override-test badguy)
           (not val)))

  (defret match-when-<fn>-nonmember
    (implies (not (member badguy (svarlist-fix x)))
             (svarlist-override-tests-match x val))))

(define assigns-to-overrideval-assigns ((x assigns-p)
                                        (updates svex-alist-p))
  :returns (new-x assigns-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (consp (car x))))
        (assigns-to-overrideval-assigns (cdr x) updates))
       ((cons lhs val) (car x)))
    (cons (cons (lhs-to-overrideval-lhs lhs updates) (driver-fix val))
          (assigns-to-overrideval-assigns (cdr x) updates)))
  ///
  (defret vars-of-<fn>
    (implies (svar->override-test v)
             (not (member v (lhslist-vars (alist-keys new-x)))))
    :hints(("Goal" :in-theory (enable lhslist-vars alist-keys))))

  (defret alist-vals-of-<fn>
    (equal (alist-vals new-x)
           (alist-vals (assigns-fix x)))
    :hints(("Goal" :in-theory (enable alist-vals assigns-fix))))

  (defret eval-of-<fn>
    (equal (assigns-eval new-x env)
           (4vec-assigns-to-overrideval-assigns (assigns-eval x env) updates))
    :hints(("Goal" :in-theory (enable 4vec-assigns-to-overrideval-assigns assigns-eval))))

  (local (in-theory (enable assigns-fix))))

(define assigns-to-overridetest-assigns ((x assigns-p)
                                         (updates svex-alist-p))
  :returns (new-x assigns-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (consp (car x))))
        (assigns-to-overridetest-assigns (cdr x) updates))
       ((cons lhs val) (car x)))
    (cons (cons (lhs-to-overridetest-lhs lhs updates) (driver-fix val))
          (assigns-to-overridetest-assigns (cdr x) updates)))
  ///
  ;; (defret vars-of-<fn>
  ;;   (implies (and (not (member (change-svar v :override-test nil) (lhslist-vars (alist-keys x))))
  ;;                 (not (member v (lhslist-vars (alist-keys x)))))
  ;;            (not (member v (lhslist-vars (alist-keys new-x)))))
  ;;   :hints(("Goal" :in-theory (enable lhslist-vars alist-keys))))

  (defret vars-of-<fn>-when-not-override-test
    (implies (not (svar->override-test v))
             (not (member v (lhslist-vars (alist-keys new-x)))))
    :hints(("Goal" :in-theory (enable lhslist-vars alist-keys))))

  

  (defret alist-vals-of-<fn>
    (equal (alist-vals new-x)
           (alist-vals (assigns-fix x)))
    :hints(("Goal" :in-theory (enable alist-vals assigns-fix))))

  (defret eval-of-<fn>
    (equal (assigns-eval new-x env)
           (4vec-assigns-to-overridetest-assigns (assigns-eval x env) updates))
    :hints(("Goal" :in-theory (enable 4vec-assigns-to-overridetest-assigns assigns-eval))))

  (local (in-theory (enable assigns-fix))))

(local (defthm hons-assoc-equal-of-svex-alist-eval
         (equal (hons-assoc-equal key (svex-alist-eval x env))
                (and (svar-p key)
                     (let ((look (hons-assoc-equal key x)))
                       (and look
                            (cons key (svex-eval (cdr look) env))))))
         :hints(("Goal" :in-theory (enable svex-alist-eval)))))

(defsection vars-of-assign-lhses

  (local (in-theory (disable fast-alist-clean)))
  (local (include-book "std/alists/fast-alist-clean" :dir :system))

  (defret keys-of-assign->netassigns
    (implies (and (not (member v (lhs-vars lhs)))
                  (not (hons-assoc-equal v (netassigns-fix acc))))
             (not (hons-assoc-equal v assigns)))
    :fn assign->netassigns
    :hints(("Goal" :in-theory (enable <fn> lhs-vars lhatom-vars))))


  (define netassigns-driver-vars ((x netassigns-p))
    :measure (len (netassigns-fix x))
    :returns (vars svarlist-p)
    (b* ((x (netassigns-fix x))
         ((when (atom x)) nil))
      (append (driverlist-vars (cdar x))
              (netassigns-driver-vars (cdr x))))
    ///
    (defret member-driverlist-vars-when-not-member-netassigns-driver-vars
      (implies (not (member v (netassigns-driver-vars x)))
               (not (member v (driverlist-vars (cdr (hons-assoc-equal k (netassigns-fix x)))))))
      :hints(("Goal" :in-theory (enable netassigns-fix))))

    (deffixequiv netassigns-driver-vars)

    (defthm netassigns-driver-vars-of-append
      (equal (netassigns-driver-vars (append x y))
             (append (netassigns-driver-vars x) (netassigns-driver-vars y)))
      :hints(("Goal" :in-theory (enable netassigns-fix)
              :induct (append x y)
              :expand ((netassigns-driver-vars (cons (car x) (append (cdr x) y)))))))

    (defthm netassigns-driver-vars-of-remove-assoc
      (implies (and (not (member v (netassigns-driver-vars x)))
                    (netassigns-p x))
               (not (member v (netassigns-driver-vars (acl2::hons-remove-assoc k x)))))
      :hints(("Goal" :in-theory (enable acl2::hons-remove-assoc))))

    (defthm netassign-driver-vars-of-fast-alist-clean
      (implies (and (not (member v (netassigns-driver-vars x)))
                    (netassigns-p x))
               (not (member v (netassigns-driver-vars (fast-alist-clean x)))))
      :hints(("Goal" :in-theory (e/d (acl2::fast-alist-clean-by-remove-assoc)
                                     (acl2::fast-alist-clean))))))
  

  (defret driver-vars-of-assign->netassigns
    (implies (and (not (member v (svex-vars (driver->value dr))))
                  (not (member v (netassigns-driver-vars acc))))
             (not (member v (netassigns-driver-vars assigns))))
    :fn assign->netassigns
    :hints(("Goal" :in-theory (enable <fn> netassigns-driver-vars driverlist-vars))))

  (defret keys-of-assigns->netassigns-aux
    (implies (and (not (member v (lhslist-vars (alist-keys (assigns-fix x)))))
                  (not (hons-assoc-equal v (netassigns-fix acc))))
             (not (hons-assoc-equal v netassigns)))
   :fn assigns->netassigns-aux
   :hints(("Goal" :in-theory (enable <fn> alist-keys lhslist-vars))))

  (defret driver-vars-of-assigns->netassigns-aux
    (implies (and (not (member v (driverlist-vars (alist-vals (assigns-fix x)))))
                  (not (member v (netassigns-driver-vars acc))))
             (not (member v (netassigns-driver-vars netassigns))))
    :fn assigns->netassigns-aux
    :hints(("Goal" :in-theory (enable <fn> driverlist-vars alist-vals))))


  (defret keys-of-assigns->netassigns
    (implies (and (not (member v (lhslist-vars (alist-keys (assigns-fix x))))))
             (not (hons-assoc-equal v netassigns)))
   :fn assigns->netassigns
   :hints(("Goal" :in-theory (enable <fn>))))

  (defret driver-vars-of-assigns->netassigns
    (implies (not (member v (driverlist-vars (alist-vals (assigns-fix x)))))
             (not (member v (netassigns-driver-vars netassigns))))
    :fn assigns->netassigns
    :hints(("Goal" :in-theory (enable <fn> driverlist-vars netassigns-driver-vars))))

  (local (defthm consp-car-of-netassigns-fix-fwd
           (implies (consp (netassigns-fix x))
                    (consp (car (netassigns-fix x))))
           :rule-classes :forward-chaining))

  (defret keys-of-netassigns->resolves
    (implies (not (hons-assoc-equal v (netassigns-fix x)))
             (not (hons-assoc-equal v assigns)))
   :fn netassigns->resolves
   :hints(("Goal" :in-theory (enable <fn>))))



  (defret svex-alist-vars-of-netassigns->resolves
    (implies (not (member v (netassigns-driver-vars x)))
             (not (member v (svex-alist-vars assigns))))
    :fn netassigns->resolves
    :hints(("Goal" :in-theory (enable <fn> svex-alist-vars netassigns-driver-vars)))))


(define svtv-env-filter-raw-values ((env svex-env-p))
  :returns (raw-env svex-env-p)
  (b* (((when (atom env)) nil)
       ((unless (mbt (and (consp (car env)) (svar-p (caar env)))))
        (svtv-env-filter-raw-values (cdr env)))
       ((cons (svar var) val) (car env))
       ((unless (and var.override-val (not var.override-test)))
        (svtv-env-filter-raw-values (cdr env))))
    (cons (cons (change-svar var :override-val nil) (4vec-fix val))
          (svtv-env-filter-raw-values (cdr env))))
  ///
  (defret hons-assoc-equal-of-<fn>
    (equal (hons-assoc-equal var raw-env)
           (let* ((orig (change-svar var :override-val t))
                  (look (hons-assoc-equal orig (svex-env-fix env))))
             (and (svar-p var)
                  (not (svar->override-val var))
                  (not (svar->override-test var))
                  look
                  (cons var (cdr look))))))

  (defret boundp-of-<fn>
    (equal (svex-env-boundp var raw-env)
           (let ((orig (change-svar var :override-val t)))
             (and (not (svar->override-val var))
                  (not (svar->override-test var))
                  (svex-env-boundp orig env))))
    :hints(("Goal" :in-theory (e/d (svex-env-boundp) (hons-assoc-equal <fn>)))))

  (defret lookup-in-<fn>
    (equal (svex-env-lookup var raw-env)
           (let ((orig (change-svar var :override-val t)))
             (if (and (not (svar->override-val var))
                      (not (svar->override-test var))
                      (svex-env-boundp orig env))
                 (svex-env-lookup orig env)
               (4vec-x))))
    :hints(("Goal" :in-theory (e/d (svex-env-boundp svex-env-lookup) (hons-assoc-equal <fn>)))))

  (local (in-theory (enable svex-env-fix))))

(define svtv-subst-filter-raw-values ((env svex-alist-p))
  :returns (raw-subst svex-alist-p)
  (b* (((when (atom env)) nil)
       ((unless (mbt (and (consp (car env)) (svar-p (caar env)))))
        (svtv-subst-filter-raw-values (cdr env)))
       ((cons (svar var) val) (car env))
       ((unless (and var.override-val (not var.override-test)))
        (svtv-subst-filter-raw-values (cdr env))))
    (cons (cons (change-svar var :override-val nil) (svex-fix val))
          (svtv-subst-filter-raw-values (cdr env))))
  ///

  (defret hons-assoc-equal-of-<fn>
    (equal (hons-assoc-equal var raw-subst)
           (let* ((orig (change-svar var :override-val t))
                  (look (hons-assoc-equal orig (svex-alist-fix env))))
             (and (svar-p var)
                  (not (svar->override-val var))
                  (not (svar->override-test var))
                  look
                  (cons var (cdr look))))))

  (defret lookup-in-<fn>
    (equal (svex-lookup var raw-subst)
           (let ((orig (change-svar var :override-val t)))
             (and (not (svar->override-val var))
                  (not (svar->override-test var))
                  (svex-lookup orig env))))
    :hints(("Goal" :in-theory (e/d (svex-lookup) (hons-assoc-equal <fn>)))))

  (defret svex-alist-eval-of-<fn>
    (equal (svex-alist-eval raw-subst env2)
           (svtv-env-filter-raw-values (svex-alist-eval env env2)))
    :hints(("Goal" :in-theory (enable svtv-env-filter-raw-values svex-alist-eval))))

  (local (in-theory (enable svex-alist-fix))))


(local (defthm hons-assoc-equal-of-append
         (equal (hons-assoc-equal v (append a b))
                (or (hons-assoc-equal v a)
                    (hons-assoc-equal v b)))))

(define svtv-subst-to-values ((subst svex-alist-p)
                              (map svtv-name-lhs-map-p)
                              (updates svex-alist-p))
  ;; :guard (lhslist-nonoverride-p (alist-vals map))
  :returns (val-subst svex-alist-p)
  (append (svtv-subst-filter-raw-values subst)
          (netassigns->resolves
           (assigns->netassigns
            (assigns-to-overrideval-assigns
             (svtv-subst-to-assigns subst map)
             updates))))
  ///

  (defret override-test-keys-of-<fn>
    (implies (svar->override-test v)
             (not (hons-assoc-equal v val-subst)))
    :hints(("Goal" :in-theory (enable override-test-member-when-lhslist-nonoverride-p))))

  ;; (local (defthm svex-lookup-of-append
  ;;          (equal (svex-lookup v (append a b))
  ;;                 (or (svex-lookup v a)
  ;;                     (svex-lookup v b)))
  ;;          :hints(("Goal" :in-theory (enable svex-lookup)))))

  (defret override-test-key-lookup-of-<fn>
    (implies (svar->override-test v)
             (not (svex-lookup v val-subst)))
    :hints(("Goal" :in-theory (e/d (svex-lookup) (<fn>)))))

  ;; (defret svex-alist-vars-of-<fn>
  ;;   (implies (and (not (member v (svex-alist-vars subst)))
  ;;                 (not (member (change-svar v :override-val t) (svex-alist-vars subst))))
  ;;            (not (member v (svex-alist-vars val-subst)))))

  ;; (defret svex-alist-eval-of-<fn>
  ;;   (implies (and (equal subst-vals (svex-env-to-alist (svex-alist-eval subst env)))
  ;;                 (syntaxp (not (equal subst-vals subst))))
  ;;            (equal (svex-alist-eval val-subst env)
  ;;                   (svex-alist-eval (svtv-subst-to-values
  ;;                                     subst-vals map updates)
  ;;                                    nil))))
  )




(define svtv-env-to-values ((env svex-env-p)
                            (map svtv-name-lhs-map-p)
                            (updates svex-alist-p))
  ;; :guard (lhslist-nonoverride-p (alist-vals map))
  :returns (val-inputs svex-env-p)
  (append (svtv-env-filter-raw-values env)
          (4vec-netassigns->resolves
           (4vec-assigns->netassigns
            (4vec-assigns-to-overrideval-assigns
             (svtv-env-to-4vec-assigns
              env (make-fast-alist map))
             (make-fast-alist updates)))))
  ;; (svex-alist-eval-likely-all-quotes
  ;;  (svtv-subst-to-values (svex-env-to-alist env) map updates)
  ;;  nil)
  ///

  (defret override-test-keys-of-<fn>
    (implies (svar->override-test v)
             (not (hons-assoc-equal v val-inputs)))
    :hints(("Goal" :in-theory (enable override-test-member-when-lhslist-nonoverride-p))))

  (defret svex-env-boundp-override-test-of-<fn>
    (implies (svar->override-test v)
             (not (svex-env-boundp v val-inputs)))
    :hints(("Goal" :in-theory (e/d (svex-env-boundp)
                                   (<fn>)))))

  (defthm eval-of-svtv-subst-to-values
    (equal (svex-alist-eval (svtv-subst-to-values subst map updates) env)
           (svtv-env-to-values (svex-alist-eval subst env) map updates))
    :hints(("Goal" :in-theory (enable svtv-subst-to-values))))

  (defcong svex-alist-eval-equiv equal (svtv-env-to-values env map updates) 3))




(define svtv-subst-to-tests ((tests svex-alist-p)
                              (map svtv-name-lhs-map-p)
                              (updates svex-alist-p))
  ;; :guard (lhslist-nonoverride-p (alist-vals map))
  :returns (test-subst svex-alist-p)
  (netassigns->resolves
   (assigns->netassigns
    (assigns-to-overridetest-assigns
     (svtv-subst-to-assigns tests map)
     updates)))
  ///
  (defret non-override-test-keys-of-<fn>
    (implies (not (svar->override-test v))
             (not (hons-assoc-equal v test-subst)))
    :hints(("Goal" :in-theory (enable override-test-member-when-lhslist-nonoverride-p))))

  (defret non-override-test-key-lookup-of-<fn>
    (implies (not (svar->override-test v))
             (not (svex-lookup v test-subst)))
    :hints(("Goal" :in-theory (e/d (svex-lookup) (<fn>)))))

  (defret svex-alist-vars-of-<fn>
    (implies (not (member v (svex-alist-vars tests)))
             (not (member v (svex-alist-vars test-subst)))))

  ;; (defret svex-alist-eval-of-<fn>
  ;;   (implies (and (equal tests-vals (svex-env-to-alist (svex-alist-eval tests env)))
  ;;                 (syntaxp (not (equal tests-vals tests))))
  ;;            (equal (svex-alist-eval test-subst env)
  ;;                   (svex-alist-eval (svtv-subst-to-tests
  ;;                                     tests-vals map updates)
  ;;                                    nil))))
  )


(define svtv-env-to-tests ((tests svex-env-p)
                            (map svtv-name-lhs-map-p)
                            (updates svex-alist-p))
  ;; :guard (lhslist-nonoverride-p (alist-vals map))
  :returns (test-inputs svex-env-p)
  (4vec-netassigns->resolves
   (4vec-assigns->netassigns
    (4vec-assigns-to-overridetest-assigns
     (svtv-env-to-4vec-assigns
      tests map)
     updates)))
  ;; (svex-alist-eval-likely-all-quotes
  ;;  (svtv-subst-to-tests (svex-env-to-alist tests) map updates)
  ;;  nil)
  ///

  (defret non-override-test-keys-of-<fn>
    (implies (not (svar->override-test v))
             (not (hons-assoc-equal v test-inputs)))
    :hints(("Goal" :in-theory (enable override-test-member-when-lhslist-nonoverride-p))))

  (defret svex-env-boundp-non-override-test-of-<fn>
    (implies (not (svar->override-test v))
             (not (svex-env-boundp v test-inputs)))
    :hints(("Goal" :in-theory (e/d (svex-env-boundp)
                                   (<fn>)))))

  (defthm eval-of-svtv-subst-to-tests
    (equal (svex-alist-eval (svtv-subst-to-tests subst map updates) env)
           (svtv-env-to-tests (svex-alist-eval subst env) map updates))
    :hints(("Goal" :in-theory (enable svtv-subst-to-tests))))

  (defcong svex-alist-eval-equiv equal (svtv-env-to-tests tests map updates) 3)

  (defthm svtv-env-to-tests-of-nil
    (equal (svtv-env-to-tests nil map updates) nil)
    :hints(("Goal" :in-theory (enable svtv-env-to-4vec-assigns
                                      4vec-assigns-to-overridetest-assigns)))))



(define svex-env-override-tests-filter ((x svex-env-p) (val booleanp))
  :returns (new-x svex-env-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svex-env-override-tests-filter (cdr x) val))
       ((cons var 4vec) (car x))
       ((unless (mbe :logic (iff (svar->override-test var) val) :exec (eq (svar->override-test var) val)))
        (svex-env-override-tests-filter (cdr x) val)))
    (cons (cons var (4vec-fix 4vec))
          (svex-env-override-tests-filter (cdr x) val)))
  ///
  (local (in-theory (enable svarlist-override-tests-match alist-keys)))
  (defret svarlist-override-tests-match-of-<fn>
    (svarlist-override-tests-match (alist-keys new-x) val))

  (defret <fn>-when-svarlist-override-tests-match
    (implies (svarlist-override-tests-match (alist-keys (svex-env-fix x)) val)
             (equal new-x (svex-env-fix x)))
    :hints(("Goal" :in-theory (enable svex-env-fix))))

  (local (in-theory (disable svarlist-override-tests-match alist-keys member-equal)))

  (defret lookup-in-<fn>
    (equal (hons-assoc-equal key new-x)
           (and (iff (svar->override-test key) val)
                (hons-assoc-equal key (svex-env-fix x))))
    :hints(("Goal" :induct t :expand ((svex-env-fix x)))))

  (defret svex-env-lookup-of-<fn>
    (equal (svex-env-lookup key new-x)
           (if (iff (svar->override-test key) val)
               (svex-env-lookup key x)
             (4vec-x)))
    :hints(("Goal" :in-theory (e/d (svex-env-lookup)
                                   (<fn>)))))

  (defret svex-env-boundp-of-<fn>
    (equal (svex-env-boundp key new-x)
           (and (iff (svar->override-test key) val)
                (svex-env-boundp key x)))
    :hints(("Goal" :in-theory (e/d (svex-env-boundp)
                                   (<fn>)))))

  (defthm svex-env-override-tests-filter-of-nil
    (equal (svex-env-override-tests-filter nil val) nil))

  (local (in-theory (enable svex-env-fix))))

(local (defthm svex-env-lookup-when-not-boundp
         (implies (not (svex-env-boundp key x))
                  (equal (svex-env-lookup key x) (4vec-x)))
         :hints(("Goal" :in-theory (enable svex-env-lookup svex-env-boundp)))))


;; (local (defthm svex-env-lookup-of-append
;;          (equal (svex-env-lookup key (append x y))
;;                 (if (svex-env-boundp key x)
;;                     (svex-env-lookup key x)
;;                   (svex-env-lookup key y)))
;;          :hints(("Goal" :in-theory (enable svex-env-lookup svex-env-boundp)))))



(local (defthm svarlist-p-keys-of-svex-env
         (implies (svex-env-p x)
                  (svarlist-p (alist-keys x)))
         :hints(("Goal" :in-theory (enable svex-env-p alist-keys)))))

(define join-val/test-envs ((vals svex-env-p)
                            (tests svex-env-p))
  :guard (and (svarlist-override-tests-match (alist-keys vals) nil)
              (svarlist-override-tests-match (alist-keys tests) t))
  :returns (env svex-env-p)
  (append (mbe :logic (svex-env-override-tests-filter vals nil) :exec vals)
          (mbe :logic (svex-env-override-tests-filter tests t) :exec tests))
  ///
  (defret lookup-in-join-val/test-envs
    (equal (svex-env-lookup key env)
           (if (svar->override-test key)
               (svex-env-lookup key tests)
             (svex-env-lookup key vals)))))

(local (defthmd member-alist-keys-is-hons-assoc-equal
         (iff (member v (alist-keys x))
              (hons-assoc-equal v x))
         :hints(("Goal" :in-theory (enable alist-keys)))))
                           
(define svtv-assignment-to-phase-inputs ((env svex-env-p)
                                         (tests svex-env-p)
                                         (map svtv-name-lhs-map-p)
                                         (updates svex-alist-p))
  ;; :guard (lhslist-nonoverride-p (alist-vals map))
  :guard-hints (("goal" :in-theory (enable member-alist-keys-is-hons-assoc-equal)))
  :returns (inputs svex-env-p)
  (b* ((val-env (svtv-env-to-values env map updates))
       (test-env (svtv-env-to-tests tests map updates)))
    (join-val/test-envs val-env test-env))
  ///
  

  (defcong svex-alist-eval-equiv equal (svtv-assignment-to-phase-inputs vals tests map updates) 4))



(define svex-alist-override-tests-filter ((x svex-alist-p) (val booleanp))
  :returns (new-x svex-alist-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svex-alist-override-tests-filter (cdr x) val))
       ((cons var svex) (car x))
       ((unless (mbe :logic (iff (svar->override-test var) val) :exec (eq (svar->override-test var) val)))
        (svex-alist-override-tests-filter (cdr x) val)))
    (cons (cons var (svex-fix svex))
          (svex-alist-override-tests-filter (cdr x) val)))
  ///
  (local (in-theory (enable svarlist-override-tests-match svex-alist-keys)))
  (defret svarlist-override-tests-match-of-<fn>
    (svarlist-override-tests-match (svex-alist-keys new-x) val))

  (defret <fn>-when-svarlist-override-tests-match
    (implies (svarlist-override-tests-match (svex-alist-keys x) val)
             (equal new-x (svex-alist-fix x)))
    :hints(("Goal" :in-theory (enable svex-alist-fix))))

  (local (in-theory (disable svarlist-override-tests-match svex-alist-keys member-equal)))

  (defret lookup-in-<fn>
    (equal (hons-assoc-equal key new-x)
           (and (iff (svar->override-test key) val)
                (hons-assoc-equal key (svex-alist-fix x))))
    :hints(("Goal" :induct t :expand ((svex-alist-fix x)))))

  (defret svex-lookup-of-<fn>
    (equal (svex-lookup key new-x)
           (and (iff (svar->override-test key) val)
               (svex-lookup key x)))
    :hints(("Goal" :in-theory (e/d (svex-lookup)
                                   (<fn>)))))

  (defret eval-of-<fn>
    (equal (svex-alist-eval new-x env)
           (svex-env-override-tests-filter (svex-alist-eval x env) val))
    :hints(("Goal" :in-theory (enable svex-env-override-tests-filter svex-alist-eval))))

  (local (in-theory (enable svex-alist-fix))))

;; (local (defthm svarlist-p-keys-of-svex-alist
;;          (implies (svex-alist-p x)
;;                   (svarlist-p (alist-keys x)))))

(local (defthm svex-lookup-of-append
         (equal (svex-lookup key (append x y))
                (or (svex-lookup key x)
                    (svex-lookup key y)))
         :hints(("Goal" :in-theory (enable svex-lookup)))))

(define join-val/test-alists ((vals svex-alist-p)
                            (tests svex-alist-p))
  :guard (and (svarlist-override-tests-match (svex-alist-keys vals) nil)
              (svarlist-override-tests-match (svex-alist-keys tests) t))
  :returns (alist svex-alist-p)
  (append (mbe :logic (svex-alist-override-tests-filter vals nil) :exec vals)
          (mbe :logic (svex-alist-override-tests-filter tests t) :exec tests))
  ///
  (defret lookup-in-join-val/test-alists
    (equal (svex-lookup key alist)
           (if (svar->override-test key)
               (svex-lookup key tests)
             (svex-lookup key vals))))

  (defret eval-of-<fn>
    (equal (svex-alist-eval alist env)
           (join-val/test-envs (svex-alist-eval vals env)
                               (svex-alist-eval tests env)))
    :hints(("Goal" :in-theory (enable join-val/test-envs)))))


(define svtv-subst-to-phase-inputs ((vals svex-alist-p)
                                    (tests svex-alist-p)
                                    (map svtv-name-lhs-map-p)
                                    (updates svex-alist-p))
;;   :guard (lhslist-nonoverride-p (alist-vals map))
  :guard-hints (("goal" :in-theory (enable member-alist-keys-is-hons-assoc-equal)))
  :returns (inputs svex-alist-p)
  (b* ((val-alists (svtv-subst-to-values vals map updates))
       (test-alists (svtv-subst-to-tests tests map updates)))
    (join-val/test-alists val-alists test-alists))

  ///
  (defret eval-of-<fn>
    (equal (svex-alist-eval inputs env)
           (svtv-assignment-to-phase-inputs
            (svex-alist-eval vals env)
            (svex-alist-eval tests env) map updates))
    :hints(("Goal" :in-theory (enable svtv-assignment-to-phase-inputs
                                      svtv-env-to-values
                                      svtv-env-to-tests)))))







(define lhs-check-conflicts ((x lhs-p) (masks 4vmask-alist-p) (conf-acc 4vmask-alist-p))
  ;; Same as lhs-check-masks (from lhs.lisp) but doesn't accumulate onto the
  ;; masks, just checks for a conflict with them.
  :verbosep t
  :measure (len x)
  :returns (conf-acc1 4vmask-alist-p)
  (b* ((masks (4vmask-alist-fix masks))
       (conf-acc (4vmask-alist-fix conf-acc))
       ((mv first rest) (lhs-decomp x))
       ((unless first) conf-acc)
       ((lhrange first) first)
       ((when (eq (lhatom-kind first.atom) :z))
        (lhs-check-conflicts rest masks conf-acc))
       ((lhatom-var first.atom) first.atom)
       (firstmask (sparseint-concatenate first.atom.rsh 0 (sparseint-concatenate first.w -1 0)))
       (varmask (or (cdr (hons-get first.atom.name masks)) 0))
       (conflict (sparseint-bitand varmask firstmask))
       (conf-acc (if (sparseint-bit 0 conflict)
                     conf-acc
                   (hons-acons first.atom.name
                               (sparseint-bitor conflict
                                                (or (cdr (hons-get first.atom.name conf-acc))
                                                    0))
                               conf-acc))))
    (lhs-check-conflicts rest masks conf-acc)))


(define svtv-names-diagnose-conflict-aux ((conflicting-name svar-p)
                                          (possible-names svarlist-p)
                                          (map svtv-name-lhs-map-p)
                                          (masks 4vmask-alist-p))
  :returns (errmsg)
  (b* (((when (atom possible-names)) nil)
       (name (svar-fix (car possible-names)))
       (lhs (cdr (hons-get name map))) ;; must exist
       (conf (lhs-check-conflicts lhs masks nil))
       ((when conf)
        (fast-alist-free conf)
        (msg "~x0 and ~x1 overlap: ~x2" (svar-fix conflicting-name) name conf)))
    (svtv-names-diagnose-conflict-aux conflicting-name (cdr possible-names) map masks)))


(define svtv-names-diagnose-conflict ((conflicting-name svar-p)
                                      (conflicting-lhs lhs-p
                                                       "the LHS corresponding to conflicting-name")
                                      (possible-names svarlist-p)
                                      (map svtv-name-lhs-map-p))
  :returns (errmsg)
  (b* (((mv masks conf) (lhs-check-masks conflicting-lhs nil nil))
       ((when conf)
        (fast-alist-free masks)
        (fast-alist-free conf)
        (msg "~x0 is self-overlapping: ~x1" (svar-fix conflicting-name) conf))
       (ans (svtv-names-diagnose-conflict-aux conflicting-name possible-names map masks)))
    (fast-alist-free masks)
    ans))
       

(define svtv-names-check-errors ((names svarlist-p)
                                 (map svtv-name-lhs-map-p)
                                 (names-acc svarlist-p)
                                 (mask-acc 4vmask-alist-p))
  :returns (errmsg)
  (b* (((when (atom names))
        (fast-alist-free mask-acc)
        nil)
       (name (svar-fix (car names)))
       (lhs-look (hons-get name map))
       ((unless lhs-look)
        (fast-alist-free mask-acc)
        (msg "~x0 is not a recognized signal name~%" name))
       (lhs (cdr lhs-look))
       ((mv mask-acc conf) (lhs-check-masks lhs mask-acc nil))
       ((when conf)
        (fast-alist-free conf)
        (fast-alist-free mask-acc)
        (svtv-names-diagnose-conflict name lhs names-acc map)))
    (svtv-names-check-errors
     (cdr names) map (cons name names-acc) mask-acc)))



(define svtv-fsm-env ((inputs svex-env-p)
                              (override-tests svex-env-p)
                              (x svtv-fsm-p))
  :returns (env svex-env-p)
  (b* (((svtv-fsm x)))
    (with-fast-alist x.namemap
      (with-fast-alist x.values
        (make-fast-alist
         (svtv-assignment-to-phase-inputs inputs override-tests
                                          x.namemap x.values)))))
  ///
  (defcong svtv-fsm-eval/namemap-equiv equal (svtv-fsm-env tests map updates) 3))

(define svtv-fsm-subst ((inputs svex-alist-p)
                                (override-tests svex-alist-p)
                                (x svtv-fsm-p))
  :returns (subst svex-alist-p)
  (b* (((svtv-fsm x)))
    (with-fast-alist x.namemap
      (with-fast-alist x.values
        (svtv-subst-to-phase-inputs inputs override-tests
                                    x.namemap x.values))))
  ///
  (defret eval-of-<fn>
    (equal (svex-alist-eval subst env)
           (svtv-fsm-env
            (svex-alist-eval inputs env)
            (svex-alist-eval override-tests env)
            x))
    :hints(("Goal" :in-theory (enable svtv-fsm-env)))))

(define svtv-fsm-step-env ((inputs svex-env-p)
                                   (override-tests svex-env-p)
                                   (prev-st svex-env-p)
                                   (x svtv-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :returns (env svex-env-p)
  (base-fsm-step-env (svtv-fsm-env inputs override-tests x)
                     prev-st (svtv-fsm->base-fsm x))
  ///
  (defret svtv-fsm-step-env-of-extract-states
    (equal (svtv-fsm-step-env
            inputs override-tests
            (svex-env-extract (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm x))) prev-st)
            x)
           env))

  (defcong svtv-fsm-eval/namemap-equiv svex-envs-equivalent (svtv-fsm-step-env inputs override-tests prev-st x) 4)
  
  (defcong svex-envs-similar svex-envs-equivalent
    (svtv-fsm-step-env inputs override-tests prev-st x) 3))
    


(define svtv-name-lhs-map-eval ((x svtv-name-lhs-map-p) (env svex-env-p))
  :returns (res svex-env-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svtv-name-lhs-map-eval (cdr x) env)))
    (cons (cons (caar x) (lhs-eval-zero (cdar x) env))
          (svtv-name-lhs-map-eval (cdr x) env)))
  ///
  (defret lookup-in-<fn>
    (equal (hons-assoc-equal var res)
           (let ((pair (hons-assoc-equal var (svtv-name-lhs-map-fix x))))
             (and pair
                  (cons var (lhs-eval-zero (cdr pair) env))))))

  (defcong svex-envs-similar equal (lhs-eval-zero x env) 2
    :hints(("Goal" :in-theory (enable lhs-eval-zero lhrange-eval lhatom-eval))))

  (defcong svex-envs-similar equal (svtv-name-lhs-map-eval x env) 2)

  (local (in-theory (enable svtv-name-lhs-map-fix))))

(define lhatom-subst ((x lhatom-p) (subst svex-alist-p))
  :returns (val svex-p)
  (lhatom-case x
    :z (svex-z)
    :var (svex-rsh x.rsh
                   (or (svex-lookup x.name subst) (svex-x))))
  ///
  (defret eval-of-<fn>
    (equal (svex-eval val env)
           (lhatom-eval x (svex-alist-eval subst env)))
    :hints(("Goal" :in-theory (enable svex-apply lhatom-eval)))))
                      
(define lhs-subst-zero ((x lhs-p) (subst svex-alist-p))
  :returns (val svex-p)
  (if (atom x)
      (svex-quote 0)
    (b* (((lhrange x1) (car x)))
      (svex-concat x1.w
                   (lhatom-subst x1.atom subst)
                   (lhs-subst-zero (cdr x) subst))))
  ///
  (defret eval-of-<fn>
    (equal (svex-eval val env)
           (lhs-eval-zero x (svex-alist-eval subst env)))
    :hints(("Goal" :in-theory (enable svex-apply lhs-eval-zero lhrange-eval)))))

(define svtv-name-lhs-map-subst ((x svtv-name-lhs-map-p) (subst svex-alist-p))
  :returns (res svex-alist-p)
    (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svtv-name-lhs-map-subst (cdr x) subst)))
    (cons (cons (caar x) (lhs-subst-zero (cdar x) subst))
          (svtv-name-lhs-map-subst (cdr x) subst)))
  ///
  (defret lookup-in-<fn>
    (equal (svex-lookup var res)
           (let ((pair (hons-assoc-equal (svar-fix var) (svtv-name-lhs-map-fix x))))
             (and pair
                  (lhs-subst-zero (cdr pair) subst))))
    :hints(("Goal" :in-theory (enable svex-lookup))))

  (defret eval-of-<fn>
    (equal (svex-alist-eval res env)
           (svtv-name-lhs-map-eval x (svex-alist-eval subst env)))
    :hints(("Goal" :in-theory (enable svex-alist-eval
                                      svtv-name-lhs-map-eval))))

  (local (in-theory (enable svtv-name-lhs-map-fix))))



(define lhatom-compose ((x lhatom-p) (compose svex-alist-p))
  :returns (val svex-p)
  (lhatom-case x
    :z (svex-z)
    :var (svex-rsh x.rsh
                   (or (svex-lookup x.name compose)
                       (svex-var x.name))))
  ///
  (local (defthm svex-eval-of-svex-var
           (equal (svex-eval (svex-var name) env)
                  (svex-env-lookup name env))
           :hints(("Goal" :in-theory (enable svex-eval)))))

  (defret eval-of-<fn>
    (equal (svex-eval val env)
           (lhatom-eval x (append (svex-alist-eval compose env) env)))
    :hints(("Goal" :in-theory (enable svex-apply lhatom-eval)))))
                      
(define lhs-compose-zero ((x lhs-p) (compose svex-alist-p))
  :returns (val svex-p)
  (if (atom x)
      (svex-quote 0)
    (b* (((lhrange x1) (car x)))
      (svex-concat x1.w
                   (lhatom-compose x1.atom compose)
                   (lhs-compose-zero (cdr x) compose))))
  ///
  (defret eval-of-<fn>
    (equal (svex-eval val env)
           (lhs-eval-zero x (append (svex-alist-eval compose env) env)))
    :hints(("Goal" :in-theory (enable svex-apply lhs-eval-zero lhrange-eval)))))

(define svtv-name-lhs-map-compose ((x svtv-name-lhs-map-p) (subst svex-alist-p))
  :returns (res svex-alist-p)
    (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svtv-name-lhs-map-compose (cdr x) subst)))
    (cons (cons (caar x) (lhs-compose-zero (cdar x) subst))
          (svtv-name-lhs-map-compose (cdr x) subst)))
  ///
  (defret lookup-in-<fn>
    (equal (svex-lookup var res)
           (let ((pair (hons-assoc-equal (svar-fix var) (svtv-name-lhs-map-fix x))))
             (and pair
                  (lhs-compose-zero (cdr pair) subst))))
    :hints(("Goal" :in-theory (enable svex-lookup))))

  (defret eval-of-<fn>
    (equal (svex-alist-eval res env)
           (svtv-name-lhs-map-eval x (append (svex-alist-eval subst env) env)))
    :hints(("Goal" :in-theory (enable svex-alist-eval
                                      svtv-name-lhs-map-eval))))

  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys res)
           (alist-keys (svtv-name-lhs-map-fix x)))
    :hints(("Goal" :in-theory (enable svex-alist-keys alist-keys svtv-name-lhs-map-fix))))

  (defcong svex-alist-eval-equiv svex-alist-eval-equiv!
    (svtv-name-lhs-map-compose x subst) 2
    :hints (("goal" :use ((:instance svex-envs-equivalent-implies-alist-eval-equiv
                           (x (svtv-name-lhs-map-compose x subst))
                           (y (svtv-name-lhs-map-compose x subst-equiv))))
             :in-theory (enable svex-alist-eval-equiv!-when-svex-alist-eval-equiv)
             :do-not-induct t)))

  (local (in-theory (enable svtv-name-lhs-map-fix))))



(define svtv-fsm->renamed-fsm ((x svtv-fsm-p))
  :returns (base-fsm base-fsm-p)
  (b* (((svtv-fsm x))
       (renamed-values
        (with-fast-alist x.values
          (svtv-name-lhs-map-compose x.namemap x.values))))
    (make-base-fsm :nextstate x.nextstate :values renamed-values))
  ///
  (memoize 'svtv-fsm->renamed-fsm)

  (defcong svtv-fsm-eval/namemap-equiv base-fsm-eval-equiv
    (svtv-fsm->renamed-fsm x) 1
    :hints(("Goal" :in-theory (enable svtv-fsm-eval/namemap-equiv
                                      base-fsm-eval-equiv)))))

(define svtv-fsm->renamed-values ((x svtv-fsm-p))
  :returns (res svex-alist-p)
  :enabled t
  (base-fsm->values (svtv-fsm->renamed-fsm x)))

(define svtv-name-lhs-map-to-svex-alist ((x svtv-name-lhs-map-p))
  :returns (alist svex-alist-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svtv-name-lhs-map-to-svex-alist (cdr x))))
    (cons (cons (caar x)
                (lhs->svex-zero (cdar x)))
          (svtv-name-lhs-map-to-svex-alist (cdr x))))
  ///
  (defret lookup-in-<fn>
    (equal (svex-lookup var alist)
           (b* ((look (hons-assoc-equal (svar-fix var) x)))
             (and look
                  (lhs->svex-zero (cdr look)))))
    :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix))))

  (defret svex-alist-eval-of-<fn>
    (equal (svex-alist-eval alist env)
           (svtv-name-lhs-map-eval x env))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval svex-alist-eval))))

  (local (in-theory (enable svtv-name-lhs-map-fix))))

(encapsulate nil
  (local (defthm svar-p-when-lookup-in-name-svex-alist
           (implies (and (svex-alist-p x)
                         (not (svar-p key)))
                    (not (hons-assoc-equal key x)))))
  (local (defthm svar-p-when-lookup-in-name-svtv-name-lhs-map
           (implies (and (svtv-name-lhs-map-p x)
                         (not (svar-p key)))
                    (not (hons-assoc-equal key x)))))
  (local (defthm car-of-hons-assoc-equal
           (equal (car (hons-assoc-equal k x))
                  (and (hons-assoc-equal k x)
                       k))))
  (defthm svex-alist-p-of-fal-extract
    (implies (svex-alist-p x)
             (svex-alist-p (fal-extract keys x)))
    :hints(("Goal" :in-theory (enable fal-extract))))

  (defthm svtv-name-lhs-map-p-of-fal-extract
    (implies (svtv-name-lhs-map-p x)
             (svtv-name-lhs-map-p (fal-extract keys x)))
    :hints(("Goal" :in-theory (enable fal-extract))))

  (local (defthm hons-assoc-equal-of-fal-extract
           (equal (hons-assoc-equal key (fal-extract keys al))
                  (and (member-equal key keys)
                       (hons-assoc-equal key al)))
           :hints(("Goal" :in-theory (enable fal-extract hons-assoc-equal)))))

  (defthm svex-lookup-of-fal-extract
    (equal (svex-lookup var (fal-extract vars alist))
           (and (member-equal (svar-fix var) vars)
                (svex-lookup var alist)))
    :hints(("Goal" :in-theory (enable svex-lookup)
            :do-not-induct t))))


;; (defines svex-subst-fal
;;   :verify-guards nil
;;   (define svex-subst-fal
;;     :parents (svex-subst)
;;     :short "Substitution for @(see svex)es, identical to @(see svex-subst),
;; except that we memoize the results."
;;     ((pat svex-p)
;;      (al  svex-alist-p "Need not be fast; we still use slow lookups."))
;;     :returns (x (equal x (svex-subst pat al))
;;                 :hints ((and stable-under-simplificationp
;;                              '(:expand ((svex-subst pat al))))))
;;     :measure (svex-count pat)
;;     (svex-case pat
;;       :var (or (svex-fastlookup pat.name al)
;;                (svex-quote (4vec-x)))
;;       :quote (svex-fix pat)
;;       :call (svex-call pat.fn (svexlist-subst-fal pat.args al))))
;;   (define svexlist-subst-fal ((pat svexlist-p) (al svex-alist-p))
;;     :returns (x (equal x (svexlist-subst pat al))
;;                 :hints ((and stable-under-simplificationp
;;                              '(:expand ((svexlist-subst pat al))))))
;;     :measure (svexlist-count pat)
;;     (if (atom pat)
;;         nil
;;       (cons (svex-subst-fal (car pat) al)
;;             (svexlist-subst-fal (cdr pat) al))))
;;   ///
;;   (verify-guards svex-subst-fal))

;; (define svex-alist-subst-fal-nrev ((x svex-alist-p)
;;                                  (a svex-alist-p)
;;                                  (nrev))
;;   :hooks nil
;;   (if (atom x)
;;       (acl2::nrev-fix nrev)
;;     (if (mbt (and (consp (car x)) (svar-p (caar x))))
;;         (b* ((nrev (acl2::nrev-push (cons (caar x) (svex-subst-fal (cdar x) a)) nrev)))
;;           (svex-alist-subst-fal-nrev (cdr x) a nrev))
;;       (svex-alist-subst-fal-nrev (cdr x) a nrev))))

;; (define svex-alist-subst-fal ((x svex-alist-p) (a svex-alist-p))
;;   :prepwork ((local (in-theory (enable svex-alist-p))))
;;   :returns (xx)
;;   :verify-guards nil
;;   (if (atom x)
;;       nil
;;     (acl2::with-local-nrev
;;       (svex-alist-subst-fal-nrev x a acl2::nrev)))
;;   ///
;;   (local (defthm svex-alist-subst-fal-nrev-elim
;;            (equal (svex-alist-subst-fal-nrev x a nrev)
;;                   (append nrev (svex-alist-subst x a)))
;;            :hints(("Goal" :in-theory (e/d (svex-alist-subst-fal-nrev
;;                                            svex-alist-subst
;;                                            acl2::rcons
;;                                            svex-acons))))))
;;   (defret svex-alist-subst-fal-is-svex-alist-subst
;;     (equal xx (svex-alist-subst x a))
;;     :hints(("Goal" :in-theory (enable svex-alist-subst))))
;;   (verify-guards svex-alist-subst-fal))






(define svtv-fsm-outexprs ((outvars svarlist-p)
                                   (x svtv-fsm-p))
  :returns (outs svex-alist-p)
  (svex-alist-extract outvars (svtv-fsm->renamed-values x))
  ///
  ;; (local (defthm svex-lookup-of-svex-alist-subst+
  ;;          (equal (svex-lookup var (svex-alist-subst x subst))
  ;;                 (b* ((look (svex-lookup var x)))
  ;;                   (and look
  ;;                        (svex-subst look subst))))
  ;;          :hints(("Goal" :in-theory (enable svex-alist-subst svex-lookup svex-acons)))))

  (local (defcong svex-envs-similar equal (lhs-eval-zero x env) 2
           :hints(("Goal" :in-theory (enable lhs-eval-zero lhrange-eval lhatom-eval)))))


  (defcong svtv-fsm-eval/namemap-equiv svex-alist-eval-equiv
    (svtv-fsm-outexprs outvars x) 2
    :hints ((witness) (witness))))




(define svtv-fsm-step ((inputs svex-env-p)
                               (override-tests svex-env-p)
                               (prev-st svex-env-p)
                               (x svtv-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :returns (nextstate svex-env-p)
  (b* ((env (svtv-fsm-step-env inputs override-tests prev-st x)))
    (with-fast-alist env
      (svex-alist-eval (svtv-fsm->nextstate x) env)))
  ///
  (defret alist-keys-of-<fn>
    (equal (alist-keys nextstate)
           (svex-alist-keys (svtv-fsm->nextstate x))))

  (defret svtv-fsm-step-of-extract-states
    (equal (svtv-fsm-step
            inputs override-tests
            (svex-env-extract (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm x))) prev-st)
            x)
           nextstate))

  (defcong svtv-fsm-eval/namemap-equiv svex-envs-equivalent
    (svtv-fsm-step inputs override-tests prev-st x) 4)

  (defcong svex-envs-similar svex-envs-equivalent
    (svtv-fsm-step inputs override-tests prev-st x) 3))




(define svtv-fsm-step-outs ((inputs svex-env-p)
                                         (override-tests svex-env-p)
                                         (prev-st svex-env-p)
                                         (x svtv-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :returns (outs svex-env-p)
  (b* ((env (svtv-fsm-step-env inputs override-tests prev-st x)))
    (with-fast-alist env
      (svex-alist-eval
       (svtv-fsm->renamed-values x) env)))
  ///
  (defret svtv-fsm-step-outs-of-extract-states
    (equal (svtv-fsm-step-outs
            inputs override-tests
            (svex-env-extract (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm x))) prev-st)
            x)
           outs)))

(define svtv-fsm-step-extracted-outs ((inputs svex-env-p)
                                    (override-tests svex-env-p)
                                    (outvars svarlist-p)
                                    (prev-st svex-env-p)
                                    (x svtv-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :returns (outs svex-env-p)
  (b* ((env (svtv-fsm-step-env inputs override-tests prev-st x)))
    (with-fast-alist env
      (svex-alist-eval
       (svtv-fsm-outexprs outvars x)
       env)))
  ///
  (defret svtv-fsm-step-extracted-outs-of-extract-states
    (equal (svtv-fsm-step-extracted-outs
            inputs override-tests outvars
            (svex-env-extract (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm x))) prev-st)
            x)
           outs))

  (defcong svtv-fsm-eval/namemap-equiv svex-envs-equivalent
    (svtv-fsm-step-extracted-outs inputs override-tests outvars prev-st x) 5)

  (defcong svex-envs-similar svex-envs-equivalent
    (svtv-fsm-step-extracted-outs inputs override-tests outvars prev-st x) 4)

  (defretd <fn>-in-terms-of-full-outs
    (equal outs
           (svex-env-extract outvars (svtv-fsm-step-outs inputs override-tests prev-st x)))
    :hints(("Goal" :in-theory (enable svtv-fsm-step-outs svtv-fsm-outexprs)))))


;; (define svtv-fsm-step-output-signals ((outvars svarlist-p)
;;                                               (x svtv-fsm-p))
;;   :prepwork ((local (defthm len-equal-const
;;                       (implies (syntaxp (quotep n))
;;                                (equal (equal (len x) n)
;;                                       (if (atom x)
;;                                           (equal n 0)
;;                                         (and (posp n)
;;                                              (equal (len (cdr x)) (1- n))))))))
;;              (local (in-theory (disable len)))
             
;;              (local (defthm vars-of-svex-concat
;;                       (implies (and (posp w)
;;                                     (not (svex-case x
;;                                            :call (or (eq x.fn 'concat)
;;                                                      (eq x.fn 'signx)
;;                                                      (eq x.fn 'zerox))
;;                                            :otherwise nil)))
;;                                (set-equiv (svex-vars (svex-concat w x y))
;;                                           (append (svex-vars x) (svex-vars y))))
;;                       :hints(("Goal" :in-theory (enable svex-concat
;;                                                         svexlist-vars
;;                                                         match-concat
;;                                                         match-ext)))))
;;              ;; BOZO replace vars-of-lhs->svex with this
;;              (local (defthm vars-of-lhs->svex-strict
;;                       (set-equiv (svex-vars (lhs->svex-zero x))
;;                                  (lhs-vars x))
;;                       :hints(("Goal" :in-theory (enable svex-vars lhs->svex-zero lhs-vars
;;                                                         lhatom-vars lhatom->svex svex-rsh
;;                                                         match-concat match-ext match-rsh)
;;                               :induct (lhs->svex-zero x)
;;                               ;; :expand ((SVEX-CONCAT (LHRANGE->W (CAR X))
;;                               ;;                       '(0 . -1)
;;                               ;;                       (LHS->SVEX (CDR X))))
;;                               ;; :expand ((:free (x y) (svex-rsh x y)))
;;                               ;; :expand
;;                               ;; ((:free (w x y) (svex-concat w x y)))
;;                               ))))

;;              (local (defthm equal-of-mergesort
;;                       (equal (equal (mergesort x) y)
;;                              (and (setp y)
;;                                   (set-equiv x y)))))

;;              (local (defthm svex-alist-vars-of-svtv-name-lhs-map-to-svex-alist
;;                       (set-equiv (svex-alist-vars (svtv-name-lhs-map-to-svex-alist x))
;;                                  (lhslist-vars (alist-vals (svtv-name-lhs-map-fix x))))
;;                       :hints(("Goal" :in-theory (enable svtv-name-lhs-map-to-svex-alist
;;                                                         svtv-name-lhs-map-fix
;;                                                         svex-alist-vars
;;                                                         lhslist-vars
;;                                                         alist-vals)))))

;;              )
;;   :returns (signals svarlist-p)
;;   (b* (((svtv-fsm x))
;;        (out-alist1 (acl2::fal-extract (svarlist-fix outvars) x.namemap)))
;;     (mbe :logic (set::mergesort (svex-alist-vars (svtv-name-lhs-map-to-svex-alist out-alist1)))
;;          :exec (set::mergesort (lhslist-vars (alist-vals out-alist1))))))


;; (define svtv-fsm-step-extract-outs ((outvars svarlist-p)
;;                                             (full-outs svex-env-p)
;;                                             (x svtv-fsm-p))
;;   :returns (outs svex-env-p)
;;   (b* (((svtv-fsm x))
;;        (out-alist1 (acl2::fal-extract (svarlist-fix outvars) x.namemap)))
;;     (with-fast-alist full-outs
;;       (svex-alist-eval
;;        (svtv-name-lhs-map-to-svex-alist out-alist1) full-outs)))
;;   ///
;;   (defthmd svtv-fsm-step-extracted-outs-is-extract-of-full-outs
;;     (equal (svtv-fsm-step-extracted-outs inputs override-tests outvars prev-st x)
;;            (svtv-fsm-step-extract-outs outvars
;;                                                (svtv-fsm-step-outs
;;                                                 inputs override-tests prev-st x)
;;                                                x))
;;     :hints(("Goal" :in-theory (enable svtv-fsm-step-outs
;;                                       svtv-fsm-step-extracted-outs
;;                                       svtv-fsm-outexprs))))

;;   (local (defthm svexlist-vars-of-svex-alist-vals
;;            (equal (svexlist-vars (svex-alist-vals x))
;;                   (svex-alist-vars x))
;;            :hints(("Goal" :in-theory (enable svex-alist-vals svex-alist-vars
;;                                              svexlist-vars)))))

;;   (defthmd svtv-fsm-step-extracted-outs-is-extract-of-step-outs
;;     (equal (svtv-fsm-step-extracted-outs inputs override-tests outvars prev-st x)
;;            (svtv-fsm-step-extract-outs
;;             outvars
;;             (svex-env-extract (svtv-fsm-step-output-signals outvars x)
;;                               (base-fsm-step-outs (svtv-fsm-env inputs override-tests x)
;;                                                   prev-st (svtv-fsm->base-fsm x)))
;;             x))
;;     :hints(("Goal" :in-theory (enable svtv-fsm-step-output-signals
;;                                       base-fsm-step-outs
;;                                       svtv-fsm-step-env
;;                                       svtv-fsm-step-extracted-outs
;;                                       svtv-fsm-outexprs))))

;;   (local (defthm car-of-hons-assoc-equal
;;            (equal (car (hons-assoc-equal key x))
;;                   (and (hons-assoc-equal key x)
;;                        key))))

;;   (local (defthm hons-assoc-equal-of-fal-extract
;;            (equal (hons-assoc-equal key (fal-extract vars al))
;;                   (and (member-equal key vars)
;;                        (hons-assoc-equal key al)))
;;            :hints(("Goal" :in-theory (enable fal-extract hons-assoc-equal)))))

;;   (defretd lookup-of-<fn>
;;     (equal (svex-env-lookup var outs)
;;            (let ((look (hons-assoc-equal (svar-fix var) (svtv-fsm->namemap x))))
;;              (if (and (member-equal (svar-fix var) (svarlist-fix outvars))
;;                       look)
;;                  (lhs-eval-zero (cdr look) full-outs)
;;                (4vec-x))))))





(define svtv-fsm-run-input-envs ((inputs svex-envlist-p)
                                         (override-tests svex-envlist-p)
                                         (x svtv-fsm-p))
  :returns (ins svex-envlist-p)
  (if (atom inputs)
      nil
    (cons (svtv-fsm-env (car inputs) (car override-tests) x)
          (svtv-fsm-run-input-envs (cdr inputs) (cdr override-tests) x)))
  ///
  (defret len-of-<fn>
    (equal (len ins) (len inputs))))


(define svtv-fsm-run-input-substs ((inputs svex-alistlist-p)
                                           (override-tests svex-alistlist-p)
                                           (x svtv-fsm-p))
  :returns (substs svex-alistlist-p)
  (if (atom inputs)
      nil
    (cons (svtv-fsm-subst (car inputs) (car override-tests) x)
          (svtv-fsm-run-input-substs (cdr inputs) (cdr override-tests) x)))
  ///
  (defret eval-of-<fn>
    (equal (svex-alistlist-eval substs env)
           (svtv-fsm-run-input-envs
            (svex-alistlist-eval inputs env)
            (svex-alistlist-eval override-tests env)
            x))
    :hints(("Goal" :in-theory (enable svtv-fsm-run-input-envs
                                      svex-alistlist-eval
                                      svex-alist-eval)))))




(define svtv-fsm-final-state ((inputs svex-envlist-p)
                                      (override-tests svex-envlist-p)
                                      (prev-st svex-env-p)
                                      (x svtv-fsm-p))
  :returns (final-st svex-env-p)
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  (if (atom inputs)
      (mbe :logic (svex-env-extract (svex-alist-keys (svtv-fsm->nextstate x)) prev-st)
           :exec prev-st)
    (svtv-fsm-final-state (cdr inputs)
                                  (cdr override-tests)
                                  (svtv-fsm-step (car inputs)
                                                         (car override-tests)
                                                         prev-st x)
                                  x))
  ///
  (defretd <fn>-is-svtv-fsm-final-state-of-input-envs
    (equal final-st
           (base-fsm-final-state (svtv-fsm-run-input-envs inputs override-tests x)
                                 prev-st (svtv-fsm->base-fsm x)))
    :hints(("Goal" :in-theory (enable base-fsm-final-state svtv-fsm-run-input-envs
                                      svtv-fsm-step
                                      svtv-fsm-step-env
                                      base-fsm-step))))

  (defret svtv-fsm-final-state-of-extract-states
    (equal (svtv-fsm-final-state
            inputs override-tests
            (svex-env-extract (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm x))) prev-st)
            x)
           final-st))

  (defretd svtv-fsm-final-state-open-rev
    (implies (and (consp inputs)
                  (no-duplicatesp (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm x)))))
             (equal final-st
                    (b* ((len (len inputs)))
                      (svtv-fsm-step (nth (+ -1 len) inputs)
                                             (nth (+ -1 len) override-tests)
                                             (svtv-fsm-final-state
                                              (take (+ -1 len) inputs)
                                              (take (+ -1 len) override-tests)
                                              prev-st x)
                                             x))))
    :hints(("Goal" :in-theory (enable svtv-fsm-final-state
                                      ;; svtv-fsm-eval
                                      take acl2::default-car
                                      )
            :expand ((len inputs))
            :induct <call>)
           (and stable-under-simplificationp
                '(:expand ((nth (len (cdr inputs)) inputs)))))))


;; (defsection svtv-fsm-open-nth
;;   (local (defun svtv-fsm-ind (n ins overrides initst svtv)
;;            (if (zp n)
;;                (list ins initst)
;;              (svtv-fsm-ind (1- n) (cdr ins) (cdr overrides)
;;                            (svtv-fsm-step (car ins) (car overrides) initst svtv)
;;                            svtv))))

;;   ;; (defthm svtv-fsm-step-outs-of-env-extract
;;   ;;   (equal (svtv-fsm-step-outs ins overrides
;;   ;;                                           (svex-env-extract
;;   ;;                                                (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm svtv)))
;;   ;;                                                prev-st)
;;   ;;                                           svtv)
;;   ;;          (svtv-fsm-step-outs ins overrides prev-st svtv))
;;   ;;   :hints(("Goal" :in-theory (enable svtv-fsm-step-outs))))

;;   ;; (defthm svtv-fsm-step-of-env-extract
;;   ;;   (equal (svtv-fsm-step ins overrides
;;   ;;                                 (svex-env-extract
;;   ;;                                  (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm svtv)))
;;   ;;                                  prev-st)
;;   ;;                         svtv)
;;   ;;          (svtv-fsm-step ins overrides prev-st svtv))
;;   ;;   :hints(("Goal" :in-theory (enable svtv-fsm-step))))

;;   (defthm env-extract-of-svtv-fsm-step
;;     (implies (no-duplicatesp (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm svtv))))
;;              (equal (svex-env-extract (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm svtv)))
;;                                       (svtv-fsm-step ins overrides prev-st svtv))
;;                     (svtv-fsm-step ins overrides prev-st svtv)))
;;     ;; :hints(("Goal" :in-theory (enable svtv-fsm-step)))
;;     )

;;   (defthmd svtv-fsm-eval-open-nth
;;     (implies (< (nfix n) (len ins))
;;              (equal (nth n (svtv-fsm-eval ins overrides initst svtv))
;;                     (svtv-fsm-step-outs
;;                      (nth n ins)
;;                      (nth n overrides)
;;                      (svtv-fsm-final-state (take n ins) (take n overrides) initst svtv)
;;                      svtv)))
;;     :hints(("Goal" :in-theory (enable svtv-fsm-final-state
;;                                       svtv-fsm-eval  ;; -when-consp-ins
;;                                       take)
;;             :expand ((len ins)
;;                      (:free (a b) (nth n (cons a b))))
;;             :induct (svtv-fsm-ind n ins overrides initst svtv))))

;;   (defthmd svtv-fsm-final-state-open-rev
;;     (implies (and (consp ins)
;;                   (no-duplicatesp (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm svtv)))))
;;              (equal (svtv-fsm-final-state ins overrides initst svtv)
;;                     (svtv-fsm-step (nth (+ -1 (len ins)) ins)
;;                                            (nth (+ -1 (len ins)) overrides)
;;                                            (svtv-fsm-final-state
;;                                             (take (+ -1 (len ins)) ins)
;;                                             (take (+ -1 (len ins)) overrides)
;;                                             initst svtv)
;;                                            svtv)))
;;     :hints(("Goal" :in-theory (enable svtv-fsm-final-state
;;                                       ;; svtv-fsm-eval
;;                                       take acl2::default-car
;;                                       )
;;             :expand ((len ins))
;;             :induct (svtv-fsm-final-state ins overrides initst svtv))
;;            (and stable-under-simplificationp
;;                 '(:expand ((nth (len (cdr ins)) ins)))))))




          





(defsection nth-of-base-fsm-eval
  (local (defun nth-of-sfe-ind (n ins prev-st x)
           (if (atom ins)
               (list n prev-st)
             (nth-of-sfe-ind (1- n) (cdr ins)
                             (base-fsm-step (car ins) prev-st x)
                             x))))
  (defthmd nth-of-base-fsm-eval
    (equal (nth n (base-fsm-eval ins prev-st x))
           (and (< (nfix n) (len ins))
                (b* ((st (base-fsm-final-state (take n ins) prev-st x)))
                  (base-fsm-step-outs (nth n ins) st x))))
    :hints(("Goal" :in-theory (enable base-fsm-final-state
                                      base-fsm-eval nth)
            :induct (nth-of-sfe-ind n ins prev-st x)))))






(define svtv-fsm-eval ((inputs svex-envlist-p)
                               (override-tests svex-envlist-p)
                               (prev-st svex-env-p)
                               (x svtv-fsm-p))
  :returns (outs svex-envlist-p)
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable svtv-fsm-step-extracted-outs
                                          svtv-fsm-step))))
  (if (atom inputs)
      nil
    (b* (((mv outs nextst)
          (mv (svtv-fsm-step-outs
               (car inputs)
               (car override-tests)
               prev-st x)
              (svtv-fsm-step (car inputs)
                                     (car override-tests)
                                     prev-st x))))
      (cons outs
            (svtv-fsm-eval (cdr inputs)
                                   (cdr override-tests)
                                   nextst
                                   x))))
  ///
  (defretd <fn>-is-svtv-fsm-eval-of-input-envs
    (equal outs
           (base-fsm-eval (svtv-fsm-run-input-envs inputs override-tests x)
                          prev-st
                          (svtv-fsm->renamed-fsm x)))
    :hints(("Goal" :in-theory (enable base-fsm-eval svtv-fsm-run-input-envs
                                      svtv-fsm-step-outs
                                      svtv-fsm-step
                                      svtv-fsm->renamed-fsm
                                      base-fsm-step-env
                                      svtv-fsm-step-env
                                      base-fsm-step
                                      base-fsm-step-outs))))

  
  (defret <fn>-of-extract-states
    (equal (svtv-fsm-eval
            inputs override-tests
            (svex-env-extract (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm x))) prev-st)
            x)
           outs))

  (local (defun svtv-fsm-ind (n ins overrides initst svtv)
           (if (zp n)
               (list ins initst)
             (svtv-fsm-ind (1- n) (cdr ins) (cdr overrides)
                           (svtv-fsm-step (car ins) (car overrides) initst svtv)
                           svtv))))

  (defretd svtv-fsm-eval-open-nth
    (implies (< (nfix n) (len inputs))
             (equal (nth n outs)
                    (svtv-fsm-step-outs
                     (nth n inputs)
                     (nth n override-tests)
                     (svtv-fsm-final-state (take n inputs) (take n override-tests) prev-st x)
                     x)))
    :hints(("Goal" :in-theory (enable svtv-fsm-final-state
                                      svtv-fsm-eval  ;; -when-consp-ins
                                      take)
            :expand ((len inputs)
                     (:free (a b) (nth n (cons a b)))
                     <call>)
            :induct (svtv-fsm-ind n inputs override-tests prev-st x)))))

;; (define svtv-fsm-run-extract-outs ((outvars svarlist-list-p)
;;                                            (full-outs svex-envlist-p)
;;                                            (x svtv-fsm-p))
;;   :returns (outs svex-envlist-p)
;;   (if (atom outvars)
;;       nil
;;     (cons (svtv-fsm-step-extract-outs (car outvars) (car full-outs) x)
;;           (svtv-fsm-run-extract-outs (cdr outvars) (cdr full-outs) x)))
;;   ///
;;   (local (defun ind (n outvars full-outs)
;;            (if (zp n)
;;                (list outvars full-outs)
;;              (ind (1- n) (cdr outvars) (cdr full-outs)))))
;;   (defret nth-of-<fn>
;;     (equal (nth n outs)
;;            (svtv-fsm-step-extract-outs
;;             (nth n outvars) (nth n full-outs) x))
;;     :hints (("goal" :induct (ind n outvars full-outs) :in-theory (enable nth))
;;             (and stable-under-simplificationp
;;                  '(:in-theory (enable svtv-fsm-step-extract-outs fal-extract svex-alist-eval))))))

;; (define svtv-fsm-run-output-signals ((outvars svarlist-list-p)
;;                                              (x svtv-fsm-p))
;;   :returns (outs svarlist-list-p)
;;   (if (atom outvars)
;;       nil
;;     (cons (svtv-fsm-step-output-signals (car outvars) x)
;;           (svtv-fsm-run-output-signals (cdr outvars) x))))


(define svtv-fsm-run ((inputs svex-envlist-p)
                              (override-tests svex-envlist-p)
                              (prev-st svex-env-p)
                              (x svtv-fsm-p)
                              (outvars svarlist-list-p))
  :returns (outs svex-envlist-p)
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable svtv-fsm-step-extracted-outs
                                          svtv-fsm-step))))
  (if (atom outvars)
      nil
    (b* (((mv outs nextst)
          (mbe :logic 
               (mv (svtv-fsm-step-extracted-outs (car inputs)
                                               (car override-tests)
                                               (car outvars)
                                               prev-st x)
                   (svtv-fsm-step (car inputs)
                                          (car override-tests)
                                          prev-st x))
               :exec
               (b* ((env (svtv-fsm-step-env (car inputs)
                                                    (car override-tests)
                                                    prev-st x))
                    ((mv outs nextst)
                     (with-fast-alist env
                       (mv (svex-alist-eval
                            (svtv-fsm-outexprs (car outvars) x)
                            env)
                           (svex-alist-eval (svtv-fsm->nextstate x) env)))))
                 (fast-alist-free env)
                 (mv outs nextst)))))
      (cons outs
            (svtv-fsm-run (cdr inputs)
                                  (cdr override-tests)
                                  nextst
                                  x
                                  (cdr outvars)))))
  ///
  (local (defun nth-of-fn-induct (n inputs override-tests outvars prev-st x)
           (if (atom outvars)
               (list n inputs prev-st)
             (nth-of-fn-induct
              (1- n)
              (cdr inputs)
              (cdr override-tests)
              (cdr outvars)
              (svtv-fsm-step (car inputs) (car override-tests) prev-st x)
              x))))

  (local (defthm svtv-fsm-step-extracted-outs-of-no-outvars
           (equal (svtv-fsm-step-extracted-outs ins overrides nil prev-st x)
                  nil)
           :hints(("Goal" :in-theory (enable svtv-fsm-step-extracted-outs
                                             svtv-fsm-outexprs
                                             svex-env-extract
                                             svex-alist-eval)))))
  

  (defretd nth-of-<fn>
    (equal (nth n outs)
           (b* ((st (svtv-fsm-final-state (take n inputs)
                                                  (take n override-tests)
                                                  prev-st x)))
             (svtv-fsm-step-extracted-outs (nth n inputs)
                                         (nth n override-tests)
                                         (nth n outvars)
                                         st x)))
    :hints(("Goal" :in-theory (enable svtv-fsm-final-state
                                      nth)
            :induct (nth-of-fn-induct n inputs override-tests outvars prev-st x))))

  ;; (local (defthm svex-alist-eval-of-fal-extract
  ;;          (equal (svex-alist-eval (fal-extract vars x) env)
  ;;                 (svex-env-extract

  (defretd <fn>-is-extract-of-eval
    (equal outs
           (svex-envlist-extract
            outvars
            (svtv-fsm-eval (take (len outvars) inputs) override-tests prev-st x)))
    :hints(("Goal" :in-theory (e/d (;; svtv-fsm-run-extract-outs
                                    svtv-fsm-eval
                                    svtv-fsm-step-extracted-outs
                                    svtv-fsm-step-outs
                                    svex-envlist-extract
                                    svtv-fsm-outexprs
                                    ;; svtv-fsm-step-extracted-outs-is-extract-of-full-outs
                                    )
                                   (acl2::take-of-too-many))
            :induct <call>)))

  (defret <fn>-of-extract-states
    (equal (svtv-fsm-run
            inputs override-tests (svex-env-extract (svex-alist-keys (svtv-fsm->nextstate x)) prev-st)
            x
            outvars)
           outs))


  (defretd <fn>-is-base-fsm-run
    (equal outs
           (base-fsm-run
            (svtv-fsm-run-input-envs
             (take (len outvars) inputs)
             override-tests x)
            prev-st
            (svtv-fsm->renamed-fsm x)
            outvars))
    :hints(("Goal" :in-theory (enable base-fsm-run
                                      svex-envlist-extract
                                      base-fsm-eval
                                      base-fsm-step-env
                                      svtv-fsm->renamed-fsm
                                      ;; svtv-fsm-run-output-signals
                                      svtv-fsm-run-input-envs
                                      ;; svtv-fsm-run-extract-outs
                                      ;; svtv-fsm-step-extracted-outs-is-extract-of-step-outs
                                      svtv-fsm-step
                                      svtv-fsm-step-extracted-outs
                                      svtv-fsm-outexprs
                                      base-fsm-step-outs
                                      base-fsm-step
                                      svtv-fsm-step-env)
            :induct <call>)))

  (defcong svex-envlists-equivalent svex-envlists-equivalent (cons a b) 2
    :hints ((witness)))

  (local (defun svtv-fsm-run-prev-st-cong-ind (inputs override-tests
                                                              prev-st prev-st-equiv
                                                              x outvars)
           (if (atom outvars)
               (list inputs override-tests prev-st prev-st-equiv x)
             (b* ((nextst1
                   (svtv-fsm-step (car inputs)
                                          (car override-tests)
                                          prev-st x))
                  (nextst2
                   (svtv-fsm-step (car inputs)
                                          (car override-tests)
                                          prev-st-equiv x)))
               (svtv-fsm-run-prev-st-cong-ind (cdr inputs)
                                                      (cdr override-tests)
                                                      nextst1 nextst2
                                                      x
                                                      (cdr outvars))))))

  (defcong svex-envs-similar svex-envlists-equivalent
    (svtv-fsm-run inputs override-tests prev-st x outvars) 3
    :hints (("goal" :induct (svtv-fsm-run-prev-st-cong-ind inputs override-tests prev-st prev-st-equiv x outvars)
             :expand ((:free (prev-st) (svtv-fsm-run inputs override-tests prev-st x outvars))))))

  (defcong svtv-fsm-eval/namemap-equiv svex-envlists-equivalent
    (svtv-fsm-run inputs override-tests prev-st x outvars) 4
    :hints (("goal" :induct (svtv-fsm-run inputs override-tests prev-st x outvars)
             :expand ((:free (x) (svtv-fsm-run inputs override-tests prev-st x outvars))))))

  (defret len-of-<fn>
    (equal (len outs) (len outvars))))


(define svtv-fsm-run-states ((inputs svex-envlist-p)
                              (override-tests svex-envlist-p)
                              (prev-st svex-env-p)
                              (x svtv-fsm-p)
                              (statevars svarlist-list-p))
  :returns (states svex-envlist-p)
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable svtv-fsm-step-extracted-outs
                                          svtv-fsm-step))))
  (if (atom statevars)
      nil
    (b* ((nextst
          (svtv-fsm-step (car inputs)
                         (car override-tests)
                         prev-st x)))
      (cons (svex-env-extract (car statevars) nextst)
            (svtv-fsm-run-states (cdr inputs)
                                 (cdr override-tests)
                                 nextst x
                                 (cdr statevars)))))
  ///
  
  (defretd <fn>-is-base-fsm-run-states
    (equal states
           (base-fsm-run-states
            (svtv-fsm-run-input-envs
             (take (len statevars) inputs)
             override-tests x)
            prev-st
            (svtv-fsm->renamed-fsm x)
            statevars))
    :hints(("Goal" :in-theory (enable base-fsm-run-states
                                      svex-envlist-extract
                                      base-fsm-eval
                                      base-fsm-step-env
                                      svtv-fsm->renamed-fsm
                                      ;; svtv-fsm-run-output-signals
                                      svtv-fsm-run-input-envs
                                      ;; svtv-fsm-run-extract-outs
                                      ;; svtv-fsm-step-extracted-outs-is-extract-of-step-outs
                                      svtv-fsm-step
                                      svtv-fsm-step-extracted-outs
                                      svtv-fsm-outexprs
                                      base-fsm-step-outs
                                      base-fsm-step
                                      svtv-fsm-step-env)
            :induct <call>)))

  (defret len-of-<fn>
    (equal (len states) (len statevars))))


(define svtv-fsm-run-outs-and-states ((inputs svex-envlist-p)
                                      (override-tests svex-envlist-p)
                                      (prev-st svex-env-p)
                                      (x svtv-fsm-p)
                                      &key
                                      ((out-signals svarlist-list-p) 'nil)
                                      ((state-signals svarlist-list-p) 'nil))
  ;; :measure (Max (len out-signals) (len state-signals))
  :guard-hints (("goal" :in-theory (enable svtv-fsm-run svtv-fsm-run-states
                                           svtv-fsm-run-outs-and-states-fn)
                 :do-not-induct t)
                (and stable-under-simplificationp
                     '(:in-theory (enable svtv-fsm-step-extracted-outs
                                          svtv-fsm-step))))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :enabled t
  :returns (mv outs states)
  (mbe :logic (mv (svtv-fsm-run inputs override-tests prev-st x out-signals)
                  (svtv-fsm-run-states inputs override-tests prev-st x state-signals))
       :exec
       (if (and (atom out-signals) (atom state-signals))
           (mv nil nil)
         (b* (((mv outs nextst)
               (mbe :logic 
                    (mv (svtv-fsm-step-extracted-outs (car inputs)
                                                      (car override-tests)
                                                      (car out-signals)
                                                      prev-st x)
                        (svtv-fsm-step (car inputs)
                                       (car override-tests)
                                       prev-st x))
                    :exec
                    (b* ((env (svtv-fsm-step-env (car inputs)
                                                 (car override-tests)
                                                 prev-st x))
                         ((mv outs nextst)
                          (with-fast-alist env
                            (mv (svex-alist-eval
                                 (svtv-fsm-outexprs (car out-signals) x)
                                 env)
                                (svex-alist-eval (svtv-fsm->nextstate x) env)))))
                      (fast-alist-free env)
                      (mv outs nextst))))
              ((mv rest-outs rest-states)
               (svtv-fsm-run-outs-and-states (cdr inputs)
                                             (cdr override-tests)
                                             nextst x
                                             :out-signals (cdr out-signals)
                                             :state-signals (cdr state-signals))))
           (mv (and (consp out-signals) (cons outs rest-outs))
               (and (consp state-signals)
                    (cons (svex-env-extract (car state-signals) nextst)
                          rest-states))))))
  ///
  
  (local (defthm true-listp-when-svex-envlist-p-rewrite
           (implies (svex-envlist-p x)
                    (true-listp x))))

  (local (defthm take-of-same-len
           (implies (equal len (len x))
                    (equal (take len x) (true-list-fix x)))))

  (local (defthm take-of-svtv-fsm-run-input-envs
           (implies (<= (nfix len) (len inputs))
                    (equal (take len (svtv-fsm-run-input-envs inputs override-tests x))
                           (svtv-fsm-run-input-envs (take len inputs) override-tests x)))
           :hints(("Goal" :in-theory (enable svtv-fsm-run-input-envs)))))

  (local (defthmd base-fsm-run-when-outvars-Shorter-than-inputs-lemma
           (implies (<= (len outvars) (len inputs))
                    (equal (base-fsm-run inputs prev-st fsm outvars)
                           (base-fsm-run (take (len outvars) inputs) prev-st fsm outvars)))
           :hints(("Goal" :in-theory (enable base-fsm-run)))))

  (local (defthm base-fsm-run-when-outvars-Shorter-than-inputs
           (implies (and (equal outs-len (len outvars))
                         (<= outs-len (len inputs))
                         (equal inputs2 (take outs-len inputs))
                         (syntaxp (not (case-match inputs2
                                         (('take len &) (equal len outs-len))
                                         (&  (equal inputs2 inputs))))))
                    (equal (base-fsm-run inputs prev-st fsm outvars)
                           (base-fsm-run inputs2 prev-st fsm outvars)))
           :hints(("Goal" :in-theory (enable base-fsm-run-when-outvars-Shorter-than-inputs-lemma)))))

  (local (defthmd base-fsm-run-states-when-outvars-Shorter-than-inputs-lemma
           (implies (<= (len outvars) (len inputs))
                    (equal (base-fsm-run-states inputs prev-st fsm outvars)
                           (base-fsm-run-states (take (len outvars) inputs) prev-st fsm outvars)))
           :hints(("Goal" :in-theory (enable base-fsm-run-states)))))

  (local (defthm base-fsm-run-states-when-outvars-Shorter-than-inputs
           (implies (and (equal outs-len (len outvars))
                         (<= outs-len (len inputs))
                         (equal inputs2 (take outs-len inputs))
                         (syntaxp (not (case-match inputs2
                                         (('take len &) (equal len outs-len))
                                         (&  (equal inputs2 inputs))))))
                    (equal (base-fsm-run-states inputs prev-st fsm outvars)
                           (base-fsm-run-states inputs2 prev-st fsm outvars)))
           :hints(("Goal" :in-theory (enable base-fsm-run-states-when-outvars-Shorter-than-inputs-lemma)))))

  (local (defthm len-of-take
           (equal (len (take n x)) (nfix n))))

  (defretd <fn>-is-base-fsm-run-outs-and-states
    (equal <call>
           (b* (((mv outs states)
                 (base-fsm-run-outs-and-states
                  (svtv-fsm-run-input-envs
                   (take (max (len out-signals) (len state-signals)) inputs)
                   override-tests x)
                  prev-st
                  (svtv-fsm->renamed-fsm x)
                  :out-signals out-signals
                  :state-signals state-signals)))
             (mv (take (len out-signals) outs)
                 (take (len state-signals) states))))
    :hints(("Goal" :in-theory (enable svtv-fsm-run-is-base-fsm-run
                                      base-fsm-run-outs-and-states
                                      svtv-fsm-run-states-is-base-fsm-run-states)
            :do-not-induct t))
    :otf-flg t))





(define svtv-fsm-mod-alias-guard ((top modname-p)
                                  (moddb moddb-ok) aliases)
  :enabled t
  (b* ((modidx (moddb-modname-get-index top moddb)))
    (and modidx
         (svtv-mod-alias-guard modidx moddb aliases))))


(define svtv-fsm-add-names ((names svtv-namemap-p)
                            (x svtv-fsm-p)
                            &key
                            ((top modname-p) 'nil)
                            ((moddb moddb-ok) 'moddb)
                            (aliases 'aliases))
  :guard (svtv-fsm-mod-alias-guard top moddb aliases)
  :returns (mv err
               (new-fsm (implies (not err) (svtv-fsm-p new-fsm))))
  (b* (((svtv-fsm x))
       ((mv errs lhsmap)
        (svtv-namemap->lhsmap
         names 
         (moddb-modname-get-index top moddb)
         moddb aliases))
       ((when errs)
        (mv (msg-list errs) nil)))
    (mv nil
        (change-svtv-fsm x :namemap (append lhsmap x.namemap)))))



