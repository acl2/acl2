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
; Updated by:      Mertcan Temel (8/29/2019)

(in-package "CMR")

(Include-book "misc/beta-reduce" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "tools/templates" :dir :system)
(include-book "std/lists/list-defuns" :dir :system)
(include-book "std/strings/cat-base" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "centaur/misc/evaluator-metatheorems" :dir :system)

(defun function-deps (fn wrld)
  (b* ((body (getpropc fn 'acl2::unnormalized-body nil wrld)))
    (acl2::all-fnnames body)))

(defun function-deps-lst (fns wrld acc)
  (if (atom fns)
      acc
    (b* ((body (getpropc (car fns) 'acl2::unnormalized-body nil wrld)))
      (function-deps-lst (cdr fns) wrld (acl2::all-fnnames1 nil body acc)))))

(mutual-recursion
 ;; any function that has a dependency on a fn given in skip list will
 ;; be returned in a separate list with the same name. Also, for anything given
 ;; in skip, their  dependencies will not be  determined. For example,
 ;; if skip='(apply$), then  we don't want to attempt to  find all the
 ;; children functions of apply$, and we want to know which functions depend on
 ;; apply$. Those that depend on apply$ will be returned as the 3rd value.
 (defun collect-toposort-function-deps (fn wrld skip seen toposort)
   (declare (xargs :mode :program))
   (b* (((when (or (member-eq fn seen)
                   (member-eq fn skip)))
         (mv seen toposort skip))
        (clique (or (getpropc fn 'acl2::recursivep nil wrld) (list fn)))
        (deps (function-deps-lst clique wrld nil))
        (seen (append clique seen))
        ((mv seen toposort skip)
         (collect-toposort-function-deps-list deps wrld skip seen toposort))
        (skip (if (intersection$ skip deps)
                  (append clique skip)
                skip)))
     (mv seen (append clique toposort) skip)))
 (defun collect-toposort-function-deps-list (fns wrld skip seen toposort)
   (b* (((when (atom fns)) (mv seen toposort skip))
        ((mv seen toposort skip)
         (collect-toposort-function-deps (car fns) wrld skip seen toposort)))
     (collect-toposort-function-deps-list (cdr fns) wrld skip seen toposort))))

(defun formula-check-tests (formulas state)
  (declare (xargs :stobjs state :mode :program))
  (if (atom formulas)
      nil
    (cons `(equal (meta-extract-formula ',(car formulas) state)
                  ',(meta-extract-formula (car formulas) state))
          (formula-check-tests (cdr formulas) state))))

(defun def-formula-checker-fn (name formulas state)
  (declare (xargs :stobjs state :mode :program))
  `(define ,name (state)
     :returns (ok)
     (and . ,(formula-check-tests formulas state))
     ///
     (table formula-checkers ',name ',formulas)))

(defmacro def-formula-checker (name formulas)
  `(make-event
    (def-formula-checker-fn ',name ',formulas state)))

(defun formula-checks-lemmas (name formulas state)
  (declare (xargs :stobjs state :mode :program))
  (if (atom formulas)
      nil
    (cons `(defthm ,(intern-in-package-of-symbol
                     (concatenate 'string "META-EXTRACT-FORMULA-" (symbol-name (car formulas))
                                  "-WHEN-" (symbol-name name))
                     name)
             (implies (,name state)
                      (equal (meta-extract-formula ',(car formulas) state)
                             ',(meta-extract-formula (car formulas) state)))
             :hints(("Goal" :in-theory (enable ,name))))
          (formula-checks-lemmas name (cdr formulas) state))))

(defun def-formula-checker-lemmas-fn (name formulas state)
  (declare (xargs :stobjs state :mode :program))
  `(defsection ,(intern-in-package-of-symbol
                 (concatenate 'string (symbol-name name) "-LEMMAS")
                 name)
     . ,(formula-checks-lemmas name formulas state)))

(defmacro def-formula-checker-lemmas (name formulas)
  `(make-event
    (def-formula-checker-lemmas-fn ',name ',formulas state)))

(defun formals-subsubsts (formals)
  (declare (xargs :mode :program))
  (if (atom formals)
      nil
    (cons (acl2::make-tmplsubst :atoms `((<formal> . ,(car formals))))
          (formals-subsubsts (cdr formals)))))

(defun def-formula-check-definition-thm-fn-aux (name-lst evl flags
                                                         equivs-thm
                                                         formula-check switch-hyps wrld)
  (declare (xargs :mode :program))
  (cond
   ((atom name-lst)
    (mv nil nil nil))
   (t
    (b* ((name (car name-lst))
         (formals (acl2::formals name wrld))
         ((mv rest-lemma rest-hint rest-defthm)
          (def-formula-check-definition-thm-fn-aux
            (cdr name-lst) evl flags equivs-thm formula-check switch-hyps wrld))
         (flag (if flags `(:flag ,(cdr (assoc-equal name flags))) nil))

         ((list lemma hint defthm)
          (acl2::template-subst
           `((defthmd <evl>-of-<name>-lemma
               (implies ,(if switch-hyps
                             '(and (<evl>-meta-extract-global-facts)
                                   (<formula-check> state))
                           '(and (<formula-check> state)
                                 (<evl>-meta-extract-global-facts)))
                        (equal (<evl> '(<name> . <formals>)
                                      (list (:@proj <formals> (cons '<formal> <formal>))))
                               (<name> . <formals>)))
               :hints ('(:use ((:instance <evl>-meta-extract-formula
                                (acl2::name '<name>)
                                (acl2::a
                                 (list (:@proj <formals> (cons '<formal> <formal>))))
                                (acl2::st state))))
                       (and stable-under-simplificationp
                            (let* ((hints (acl2::just-expand-cp-parse-hints
                                           '((:free <formals>
                                              (<name> . <formals>)))
                                           (w state))))
                              `(:computed-hint-replacement
                                ('(:in-theory (enable <evl>-of-fncall-args
                                                      acl2::expand-marked-meta
                                                      <equiv-thm>)))
                                :clause-processor (acl2::mark-expands-cp
                                                   clause '(t nil ,hints))))))
               ,@flag)

             (:instance <evl>-meta-extract-formula
                        (acl2::name '<name>)
                        (acl2::a
                         (list (:@proj <formals> (cons '<formal> <formal>))))
                        (acl2::st state))

             (defthm <evl>-of-<name>-when-<formula-check>
               (implies (and (<formula-check> state)
                             (<evl>-meta-extract-global-facts))
                        (equal (<evl> (list '<name> . <formals>) env)
                               (<name> (:@proj <formals>
                                               (<evl> <formal> env)))))
               :hints(("Goal" :use ((:instance <evl>-of-<name>-lemma
                                               (:@proj <formals> (<formal> (<evl> <formal> env)))))
                       :in-theory (enable <evl>-of-fncall-args)))))
           :str-alist `(("<NAME>" . ,(symbol-name name))
                        ("<EVL>" . ,(symbol-name evl))
                        ("<FORMULA-CHECK>" . ,(symbol-name formula-check)))
           :atom-alist `((<name> . ,name)
                         (<evl> . ,evl)
                         (<formula-check> . ,formula-check)
                         (<formals> . ,formals)
                         (<equiv-thm> . ,equivs-thm))
           :subsubsts `((<formals> . ,(formals-subsubsts formals)))
           :pkg-sym formula-check)))
      (mv (cons lemma rest-lemma)
          (cons hint rest-hint)
          (cons defthm rest-defthm))))))

(defun def-formula-check-definition-thm-fn (name evl formula-check switch-hyps wrld)
  (declare (xargs :mode :program))
  (b* ((recursivep (fgetprop name 'acl2::recursivep nil wrld))
       (formals (acl2::formals name wrld)))
    (acl2::template-subst
     (cond
      ((equal recursivep nil)
       '(defthm <evl>-of-<name>-when-<formula-check>
          (implies (:@ :switch-hyps
                       (and (<evl>-meta-extract-global-facts)
                            (<formula-check> state)))
                   (:@ (not :switch-hyps)
                       (and (<formula-check> state)
                            (<evl>-meta-extract-global-facts)))
                   (equal (<evl> (list '<name> . <formals>) env)
                          (<name> (:@proj <formals>
                                          (<evl> <formal> env)))))
          :hints(("Goal" :in-theory '(acl2::assoc-equal-of-cons-when-keys-known
                                      formula-checker-lemmas)
                  :use ((:instance <evl>-meta-extract-formula
                                   (acl2::name '<name>)
                                   (acl2::a (list (:@proj <formals>
                                                          (CONS '<formal> (<evl> <formal> env)))))
                         (acl2::st state))))
                 (and stable-under-simplificationp
                      (let* ((hints (acl2::just-expand-cp-parse-hints
                                     '((:free <formals>
                                        (<name> . <formals>)))
                                     (w state))))
                        `(:computed-hint-replacement
                          ('(:in-theory (enable <evl>-of-fncall-args
                                                acl2::expand-marked-meta)))
                          :clause-processor (acl2::mark-expands-cp
                                             clause '(t nil ,hints))))))))
      ((equal (len recursivep) 1)
       '(encapsulate nil
          (local (defthmd <evl>-of-<name>-lemma
                   (implies (and (<formula-check> state)
                                 (<evl>-meta-extract-global-facts))
                            (equal (<evl> '(<name> . <formals>)
                                          (list (:@proj <formals> (cons '<formal> <formal>))))
                                   (<name> . <formals>)))
                   :hints(("Goal" :in-theory (enable (:i <name>))
                           :induct (<name> . <formals>)
                           :do-not-induct t)
                          (let* ((hints (acl2::just-expand-cp-parse-hints
                                         '((<name> . <formals>))
                                         (w state))))
                            `(:clause-processor (acl2::mark-expands-cp
                                                 clause '(t nil ,hints))))
                          '(:use ((:instance <evl>-meta-extract-formula
                                             (acl2::name '<name>)
                                             (acl2::a
                                              (list (:@proj <formals> (cons '<formal> <formal>))))
                                   (acl2::st state))))
                          
                          (and stable-under-simplificationp
                               '(:in-theory (e/d (<evl>-of-fncall-args
                                                       acl2::expand-marked-meta)))))))

          (defthm <evl>-of-<name>-when-<formula-check>
            (implies (:@ :switch-hyps
                         (and (<evl>-meta-extract-global-facts)
                              (<formula-check> state)))
                     (:@ (not :switch-hyps)
                         (and (<formula-check> state)
                              (<evl>-meta-extract-global-facts)))
                     (equal (<evl> (list '<name> . <formals>) env)
                            (<name> (:@proj <formals>
                                            (<evl> <formal> env)))))
            :hints(("Goal"
                    :do-not-induct t
                    :use ((:instance <evl>-of-<name>-lemma
                                     (:@proj <formals> (<formal> (<evl> <formal> env)))))
                    :in-theory (enable <evl>-of-fncall-args))))))
      (t
       (b* ((flag-fns (table-alist 'flag::flag-fns wrld))
            (entry (assoc-equal (car recursivep) flag-fns))
            (- (if entry nil
                 (hard-error 'def-formula-checks
                             "You need to have make-flag for ~p0 ~%"
                             (list (cons #\0 recursivep)))))
            (flag-fn (nth 1 entry))
            (flags (nth 2 entry))
            (macro-name (nth 3 entry))
            (equivs-thm (nth 4 entry))
            ((mv lemmas ?lemma-hints defthms)
             (def-formula-check-definition-thm-fn-aux
               recursivep evl flags equivs-thm formula-check switch-hyps wrld)))
         `(encapsulate
            nil
            (local
             (,macro-name
              ,@lemmas
              :hints (("Goal"
                       :do-not-induct t
                       :in-theory (e/d ((:i ,flag-fn)
                                        acl2::assoc-equal-of-cons-when-keys-known
                                      formula-checker-lemmas) ()))
                      ;; '(:use ,lemma-hints
                      ;;        :in-theory (e/d (<evl>-of-fncall-args
                      ;;                         . ,recursivep) ())
                      ;;        :do-not-induct t)
                      )))
            ,@defthms))))
     :str-alist `(("<NAME>" . ,(symbol-name name))
                  ("<EVL>" . ,(symbol-name evl))
                  ("<FORMULA-CHECK>" . ,(symbol-name formula-check)))
     :atom-alist `((<name> . ,name)
                   (<evl> . ,evl)
                   (<formula-check> . ,formula-check)
                   (<formals> . ,formals))
     :subsubsts `((<formals> . ,(formals-subsubsts formals)))
     :features (and switch-hyps '(:switch-hyps))
     :pkg-sym formula-check)))

(defmacro def-formula-check-definition-thm (name evl formula-check &optional switch-hyps)
  `(make-event
    (def-formula-check-definition-thm-fn ',name ',evl ',formula-check ',switch-hyps (w state))))

(defun def-formula-check-definition-only-body-thm-fn (name evl formula-check switch-hyps skip wrld)
  (declare (xargs :mode :program))
  (declare (ignorable skip))
  (b* (;;(recursivep (fgetprop name 'acl2::recursivep nil wrld))
       (formals (acl2::formals name wrld))

       (body (getpropc name 'acl2::unnormalized-body nil wrld))
       ;;(body (acl2::beta-reduce-pseudo-termp body))

       (eval-rules
        ;; ideally, everything evaluator symbol should have evaluator's package
        ;; but not doing that  has been ok so far. The below  list of rules are
        ;; added long after def-formula-checks has started  to be used. So I am
        ;; making sure that they are in evaluator's package.
        (acl2::template-subst
         `(<evl>-of-equal-call
           <evl>-of-variable
           <evl>-of-fncall-args

           ;; BOZO: the lst version of an evaluator should be
           ;; taken from  the user or pulled  from ACL2 world
           ;; if possible.  Here, I am assuming that  its name
           ;; would be <evl>-lst
           <evl>-LST-OF-ATOM
           <evl>-LST-OF-CONS)
         :str-alist `(("<EVL>" . ,(symbol-name evl)))
         :pkg-sym evl)))
    (acl2::template-subst
     `(defthmd <evl>-of-<name>-when-<formula-check>
        (implies (:@ :switch-hyps
                     (and (<evl>-meta-extract-global-facts)
                          (<formula-check> state)))
                 (:@ (not :switch-hyps)
                     (and (<formula-check> state)
                          (<evl>-meta-extract-global-facts)))
                 (equal (<evl> (list '<name> . <formals>) env)
                        (<evl> '<body> (list (:@proj <formals>
                                                     (CONS '<formal> (<evl> <formal> env)))))))
        :hints(("Goal"
                :in-theory '(meta-extract-formula-<name>-when-<formula-check>
                             (:definition synp)
                             (:definition assoc-equal)
                             (:executable-counterpart car)
                             (:executable-counterpart cdr)
                             (:executable-counterpart equal)
                             (:rewrite car-cons)
                             (:rewrite cdr-cons)
                             ,@eval-rules)
                :use ((:instance <evl>-meta-extract-formula
                                 (acl2::name '<name>)
                                 (acl2::a (list (:@proj <formals>
                                                        (CONS '<formal> (<evl> <formal> env)))))
                                 #|(acl2::a env)|#
                                 (acl2::st state))))))
     :str-alist `(("<NAME>" . ,(symbol-name name))
                  ("<EVL>" . ,(symbol-name evl))
                  ("<FORMULA-CHECK>" . ,(symbol-name formula-check)))
     :atom-alist `((<name> . ,name)
                   (<evl> . ,evl)
                   (<formula-check> . ,formula-check)
                   (<body> . ,body)
                   (<formals> . ,formals))
     :subsubsts `((<formals> . ,(formals-subsubsts formals)))
     :features (and switch-hyps '(:switch-hyps))
     :pkg-sym formula-check)))

(defmacro def-formula-check-definition-only-body-thm (name evl formula-check &optional switch-hyps skip)
  `(make-event
    (def-formula-check-definition-only-body-thm-fn ',name ',evl ',formula-check ',switch-hyps ',skip  (w state))))

(defun def-formula-checks-definition-thm-list-fn (x evl name switch-hyps skip)
  (if (atom x)
      nil
    (cons (if (member-equal (car x) skip)
              `(def-formula-check-definition-only-body-thm ,(car x) ,evl ,name ,switch-hyps ,skip)
            `(def-formula-check-definition-thm ,(car x) ,evl ,name ,switch-hyps))
          (def-formula-checks-definition-thm-list-fn (cdr x) evl name switch-hyps skip))))

(defun def-formula-check-warrant-thm-fn (warranted-fn evl formula-check switch-hyps )
  (declare (xargs :mode :program))
  (b* (((list warrant-definition warrant-name witness-name)
        (acl2::template-subst
         '(apply$-warrant-<fn>-definition
           apply$-warrant-<fn>
           apply$-warrant-<fn>-witness)
         :pkg-sym warranted-fn
         :str-alist `(("<FN>" . ,(symbol-name warranted-fn))))))
    (acl2::template-subst
     `(defthm <evl>-of-<name>-when-<formula-check>
        (implies (and (:@ :switch-hyps
                          (<evl>-meta-extract-global-facts)
                          (<formula-check> state))
                      (:@ (not :switch-hyps)
                          (<formula-check> state)
                          (<evl>-meta-extract-global-facts))
                      (force (<evl> '(,warrant-name) env)))
                 (,warrant-name))
        :hints(("Goal" :in-theory (e/d (<evl>-of-fncall-args
                                        <evl>-of-apply$-call
                                        <evl>-of-badge-userfn-call
                                        <evl>-of-apply$-userfn-call
                                        )
                                       (<evl>-meta-extract-formula))
                :use ((:instance ,warrant-definition)
                      (:instance <evl>-meta-extract-formula
                                 (acl2::name '<name>)
                                 (acl2::a (list
                                           (cons 'args
                                                 (,witness-name))))
                                 (acl2::st state))))))
     :str-alist `(("<NAME>" . ,(symbol-name warrant-name))
                  ("<EVL>" . ,(symbol-name evl))
                  ("<FORMULA-CHECK>" . ,(symbol-name formula-check)))
     :atom-alist `((<name> . ,warrant-name)
                   (<evl> . ,evl)
                   (<formula-check> . ,formula-check))
     :features (and switch-hyps '(:switch-hyps))
     :pkg-sym evl)))

(defmacro def-formula-check-warrant-thm-list (warranted-fns evl formula-check switch-hyps)
  `(make-event
    `(progn ,@(loop$ for x in ',warranted-fns collect
                     `(make-event
                       (def-formula-check-warrant-thm-fn ',x ',',evl ',',formula-check ,,switch-hyps))))))

(defmacro def-formula-checks-definition-thm-list (x evl name &optional switch-hyps skip)
  `(make-event
    (cons 'progn (def-formula-checks-definition-thm-list-fn ,x ',evl ',name ',switch-hyps ',skip))))

(defun filter-defined-functions (fns wrld)
  (if (atom fns)
      nil
    (if (fgetprop (car fns) 'acl2::def-bodies nil wrld)
        (cons (car fns) (filter-defined-functions (cdr fns) wrld))
      (filter-defined-functions (cdr fns) wrld))))

(defun formula-checks-get-warranted-fns-lemma-names (warranted-fns)
  (declare (xargs :mode :program))
  (if (atom warranted-fns)
      nil
    (list* (intern-in-package-of-symbol
            (str::cat "APPLY$-" (symbol-name (car warranted-fns)))
            (car warranted-fns))
           (intern-in-package-of-symbol
            (str::cat "APPLY$-WARRANT-" (symbol-name (car warranted-fns)))
            (car warranted-fns))
           (formula-checks-get-warranted-fns-lemma-names (cdr warranted-fns)))))

(defthmd assoc-equal-of-pairlis$-known-keys
  (implies (and (syntaxp (quotep k))
                (consp keys)
                (equal key1 (car keys))
                (syntaxp (quotep key1)))
           (equal (cdr (assoc-equal k (pairlis$ keys vals)))
                  (if (equal k key1)
                      (car vals)
                    (cdr (assoc-equal k (pairlis$ (cdr keys) (Cdr vals)))))))
  :hints(("Goal" :in-theory (enable assoc-equal pairlis$))))

(defun def-formula-checks-fn (name fns warranted-fns evl evl-base-fns switch-hyps skip wrld)
  (declare (xargs :mode :program))
  (b* ((evl-base-fns (if evl-base-fns evl-base-fns
                       (cdr (assoc-equal 'evl-base-fns
                                         (table-alist 'formula-checks-eval wrld)))))
       (evl (if evl evl (cdr (assoc-equal 'evl (table-alist 'formula-checks-eval wrld)))))
       (evl-lst (b* ((sibs (fgetprop evl 'acl2::siblings nil wrld))
                     (sib (remove-eq evl sibs)))
                  (and (not (and (consp sib)
                                 (symbolp (car sib))
                                 (not (cdr sib))))
                       (er hard? 'def-formula-checks-fn "Unexpected siblings for evaluator ~x0: ~x1~%" evl sibs))
                  (car sib)))
       (formula-alist (acl2::ev-collect-apply-lemmas evl evl-lst wrld))
       (skip (loop$ for s in skip ;; avoid skippping a fn if it is in evl-base-fns
                    when (not (member-equal s evl-base-fns))
                    collect s))
       (fns (append warranted-fns fns))
       ;; skip will grow after collect-toposort-function-deps-list to have
       ;; everything that depends on the original skip list.
       ((mv ?seen deps ?skip)
        (collect-toposort-function-deps-list fns wrld skip evl-base-fns nil))
       (deps (acl2::rev deps))
       ;; BOZO. Someday we could deal with constrained functions more
       ;; generally.  For now, we hope that any constrained functions that fns
       ;; depend on will end up being irrelevant.
       (defined-deps (filter-defined-functions deps wrld))

       (warranted-fns-lemmas (formula-checks-get-warranted-fns-lemma-names warranted-fns)))
    `(encapsulate
       nil
       ;; (local
       ;;  (in-theory (disable ,@defined-deps)))
       ;; (local
       ;;  (in-theory (enable assoc-equal)))
       (local (in-theory '(,(cdr (assoc :lst-atom formula-alist))
                           ,(cdr (assoc :lst-cons formula-alist))
                           ,(cdr (assoc :quote formula-alist))
                           ,(cdr (assoc :lookup-var formula-alist))
                           ,(cdr (assoc :expand-fncall formula-alist))
                           ,(cdr (assoc :lambda formula-alist))
                           car-cons cdr-cons
                           ;; functions treated specially by
                           ;; remove-guard-holders -- may be more
                           return-last mv-list cons-with-hint
                           THE-CHECK 
                           acl2::assoc-equal-of-cons-when-keys-known
                           assoc-equal-of-pairlis$-known-keys
                           (kwote-lst))))
       (local (acl2::def-evaluator-expander ,evl))
       (def-formula-checker ,name ,(append warranted-fns-lemmas defined-deps))
       (local (deflabel def-formula-checks-pre-checker-lemmas))
       (local (def-formula-checker-lemmas ,name ,(append warranted-fns-lemmas defined-deps)))
       (local (deftheory formula-checker-lemmas
                (acl2::set-difference-theories (current-theory :here)
                                               (current-theory 'def-formula-checks-pre-checker-lemmas))))
       (def-formula-checks-definition-thm-list ',defined-deps ,evl ,name ,switch-hyps ,skip)
       (def-formula-check-warrant-thm-list ,warranted-fns ,evl ,name ,switch-hyps))))

(defmacro def-formula-checks (name fns &key
                                   (warranted-fns 'nil)
                                   (evl 'nil)
                                   (evl-base-fns 'nil)
                                   (switch-hyps 'nil)
                                   (skip ''(apply$ loop$)))
  `(make-event
    (def-formula-checks-fn ',name ',fns ',warranted-fns
      ',evl ,evl-base-fns ,switch-hyps ,skip (w state))))

(defmacro def-formula-checks-default-evl (evl evl-base-fns)
  `(progn
     (table formula-checks-eval
            'evl ',evl)
     (table formula-checks-eval
            'evl-base-fns ,evl-base-fns)))
#|
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; EXAMPLE USE

;; Let's define the base function set to create the evaluator.
(defconst
*ex-evl-base-fns*
'(acl2-numberp binary-* binary-+
unary-- unary-/ < char-code characterp
code-char complex complex-rationalp
coerce consp denominator imagpart
integerp intern-in-package-of-symbol
numerator rationalp realpart
stringp symbol-name symbol-package-name
symbolp
equal not if iff
return-last synp cons car cdr
typespec-check implies))

;; Create the evaluator. It has to be created with :namedp t.
(make-event
`(defevaluator ex-evl ex-evl-list
,(b* ((w (w state))) (loop$ for x in *ex-evl-base-fns*
collect (cons x (acl2::formals x w))))
:namedp t))

;; Create meta-extract
(acl2::def-meta-extract ex-evl ex-evl-list)

;; Option 1 to create def-formula-checks
(def-formula-checks
example-formula-checks-1
(subsetp-equal
assoc-equal)
:evl ex-evl
:evl-base-fns *ex-evl-base-fns*)

;; Option 2: You can set the evaluator to be the default to be used by def-formula-checks
(def-formula-checks-default-evl
ex-evl ;;evaluator name
*ex-evl-base-fns*) ;;base functions of the evaluator.

(include-book "std/lists/rev" :dir :system)

(encapsulate
nil
;; Sometimes some rewrite rules may cause def-formula-checks to fail. So we disable them.
(local
(in-theory (disable
acl2::revappend-removal
acl2::rev-when-not-consp
acl2::rev-of-cons)))
(def-formula-checks
example-formula-checks-2
(acl2::rev)))

;; revappend is a function used by rev. Under these hypotheses, now ex-evl
;; recognize revappend.
;; Note that (example-formula-checks-2 state) is executable and can be called
;; in meta-rule/clause-processor functions.

(defthm ex-evl-rev-test
(implies (and (ex-evl-meta-extract-global-facts)
(example-formula-checks-2 state))
(equal (ex-evl `(revappend ,x ,y) a)
(revappend (ex-evl x a)
(ex-evl y a)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
|#
