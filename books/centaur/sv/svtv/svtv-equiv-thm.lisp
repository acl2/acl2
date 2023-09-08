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
; Original author: Mertcan Temel <mert.temel@intel.com>
;; This file is copied over from svtv-generalized-thm.lisp and updated to fit the needs

(in-package "SV")

(include-book "svtv-generalize")

(std::def-primitive-aggregate svtv-equiv-thm-data
  (name
   override-vars-1
   override-vars-2
   input-vars-1
   input-vars-2
   input-var-bindings-1
   input-var-bindings-2
   override-var-bindings-1
   override-var-bindings-2
   output-vars-1
   output-vars-2
   hyp
   concl
   svtv-1
   svtv-2
   triples-name-1
   triples-name-2
   triples-val-1
   triples-val-2
   enable
   lemma-defthm
   lemma-args
   no-lemmas
   no-integerp
   hints
   free-env-var-1
   free-env-var-2
   pkg-sym))

(program)

(define svtv-equiv-thm-suffix-index-to-var (var pkg-sym index &key (ignorable 'nil))
  (intern-in-package-of-symbol (str::cat (if ignorable "?" "")
                                         (symbol-name var)
                                         "-"
                                         (str::int-to-dec-string index))
                               pkg-sym))

(defun svtv-equiv-thm-suffix-index-to-vars-for-svassocs (vars pkg-sym index)
  (if (atom vars)
      nil
    (cons `(,(svtv-equiv-thm-suffix-index-to-var (car vars) pkg-sym index :ignorable t)
            ',(car vars))
          (svtv-equiv-thm-suffix-index-to-vars-for-svassocs (cdr vars) pkg-sym index))))

(defun svtv-equiv-thm-override-svassocs (override-valnames triple-val-alist triples-name pkg-sym index)
  (b* (((when (Atom override-valnames)) nil)
       (valvar  (Car override-valnames))
       (trip (cdr (hons-get valvar triple-val-alist)))
       ((unless trip) (er hard? 'def-svtv-generalized-thm "Override name not present in triples ~x0: ~x1~%"
                          (list triples-name) valvar))
       ((svtv-override-triple trip)))
    (cons `(,(svtv-equiv-thm-suffix-index-to-var valvar pkg-sym index :ignorable t) ',trip.refvar)
          (svtv-equiv-thm-override-svassocs (cdr override-valnames) triple-val-alist triples-name pkg-sym index))))

(defun svtv-equiv-thm-override-test-alist (override-valnames triple-val-alist triples-name)
  (b* (((when (Atom override-valnames)) nil)
       (trip (cdr (hons-get (Car override-valnames) triple-val-alist)))
       ((unless trip) (er hard? 'def-svtv-equiv-thm "Override name not present in triples ~x0: ~x1~%"
                          (list triples-name) (car override-valnames)))
       ((svtv-override-triple trip)))
    (if (svex-case trip.test :var)
        (cons (cons (svex-var->name trip.test) -1)
              (svtv-equiv-thm-override-test-alist (cdr override-valnames) triple-val-alist triples-name))
      (svtv-equiv-thm-override-test-alist (cdr override-valnames) triple-val-alist triples-name))))

(defun svtv-equiv-thm-suffix-index-to-vars (vars pkg-sym index)
  (if (atom vars)
      nil
    (cons (svtv-equiv-thm-suffix-index-to-var (car vars) pkg-sym index)
          (svtv-equiv-thm-suffix-index-to-vars (cdr vars) pkg-sym index))))

(defun svtv-equiv-thm-suffix-index-to-bindings (bindings pkg-sym index)
  (b* ((vars (svtv-equiv-thm-suffix-index-to-vars (strip-cars bindings) pkg-sym index)))
    (pairlis$ vars (strip-cdrs bindings))))

(defun svtv-equiv-thm-suffix-index-to-hyps (masks pkg-sym index)
  (if (atom masks)
      nil
    (b* ((rest (svtv-equiv-thm-suffix-index-to-hyps (cdr masks) pkg-sym index))
         (cur (car masks)))
      (case-match cur
        (('unsigned-byte-p num var)
         (b* ((new-var (svtv-equiv-thm-suffix-index-to-var var pkg-sym index)))
           (cons `(unsigned-byte-p ,num ,new-var)
                 rest)))
        (&
         rest)))))

(defun svtv-equiv-thm-input-vars-to-alist (input-vars pkg-sym index)
  (if (atom input-vars)
      nil
    (cons `(cons
            ',(car input-vars)
            ,(svtv-equiv-thm-suffix-index-to-var (car input-vars) pkg-sym index))
          (svtv-equiv-thm-input-vars-to-alist (cdr input-vars) pkg-sym index))))


(progn
  ;; put  the env  of  svtv to  a  normalized  form.  It  will  be useful  when
  ;; :free-env-var-1 and/or  :free-env-var-2 is set  to nil. In such  cases, we
  ;; can create a better rw rule from the final lemma when the env is collected into a fixed form.
  (mutual-recursion
   ;; this is  kind of a dumb  function and for  example, it is not  very smart
   ;; about the definition of append and list.  It assumes the input term to be
   ;; in some certain form to work correctly...
   (defun svtv-equiv-thm-normalize-fixed-env-collect (term)
     (case-match term
       (('append . lst)
        (svtv-equiv-thm-normalize-fixed-env-collect-lst lst))
       (('list . lst)
        (svtv-equiv-thm-normalize-fixed-env-collect-lst lst))
       (('quote quoted)
        (mv nil quoted))
       (('cons key value)
        (if (and (quotep key)
                 (or (integerp value)
                     (quotep value)))
            (mv nil (list (cons (unquote key) (if (quotep value) (Unquote value) value))))
          (mv (list (list key value)) nil)))
       (& (mv (hard-error 'svtv-equiv-thm-normalize-fixed-env-collect "unexpected" nil) nil))))
   (defun svtv-equiv-thm-normalize-fixed-env-collect-lst (lst)
     (if (atom lst)
         (mv nil nil)
       (b* (((mv cur-terms cur-quoted)
             (svtv-equiv-thm-normalize-fixed-env-collect (car lst)))
            ((mv rest-terms rest-quoted)
             (svtv-equiv-thm-normalize-fixed-env-collect-lst (cdr lst))))
         (mv (append cur-terms rest-terms)
             (append cur-quoted
                     rest-quoted))))))

  (defun svtv-equiv-thm-normalize-fixed-env (term)
    (b* (((mv terms quoteds)
          (svtv-equiv-thm-normalize-fixed-env-collect term))
         (terms (acl2::merge-sort-lexorder terms))
         (quoteds (acl2::merge-sort-lexorder quoteds)))
      `(list* ,@(loop$ for x in terms collect
                       `(cons . ,x))
              ',quoteds))))

;; (svtv-equiv-thm-normalize-fixed-env
;;  '(APPEND (LIST (CONS 'FMA-PWRDN_OVRD 1)
;;                 (CONS 'WB_UOPCODE_VALID_VX5 1))
;;           (LIST (CONS 'RS_VECP_CTRL RS_VECP_CTRL-1)
;;                 (CONS 'WB_UOPCODE_VX5 WB_UOPCODE_VX5-1)
;;                 (CONS 'MXCSR MXCSR-1)
;;                 (CONS 'IMM IMM-1))
;;           '((SRCA-OVR . -1)
;;             (SRCB-OVR . -1)
;;             (SRCD-OVR . -1))
;;           (LIST (CONS 'SRCA SRCA-1)
;;                 (CONS 'SRCB SRCB-1)
;;                 (CONS 'SRCD SRCD-1))
;;           '((SRCA-OVR2 . -1)
;;             (SRCB-OVR2 . -1)
;;             (SRCD-OVR2 . -1))))
;; ==
;; (LIST* (CONS 'IMM IMM-1)
;;        (CONS 'MXCSR MXCSR-1)
;;        (CONS 'RS_VECP_CTRL RS_VECP_CTRL-1)
;;        (CONS 'SRCA SRCA-1)
;;        (CONS 'SRCB SRCB-1)
;;        (CONS 'SRCD SRCD-1)
;;        (CONS 'WB_UOPCODE_VX5 WB_UOPCODE_VX5-1)
;;        '((FMA-PWRDN_OVRD . 1)
;;          (SRCA-OVR . -1)
;;          (SRCA-OVR2 . -1)
;;          (SRCB-OVR . -1)
;;          (SRCB-OVR2 . -1)
;;          (SRCD-OVR . -1)
;;          (SRCD-OVR2 . -1)
;;          (WB_UOPCODE_VALID_VX5 . 1)))

(defun svtv-equiv-thm-initial-override-lemma (x)
  (declare (Xargs :mode :program))
  (b* (((svtv-equiv-thm-data x))
       (template '(<defthm> <name>-equiv-lemma
                            (implies <hyp>
                                     (b* ((run-1 (svtv-run (<svtv-1>)
                                                           <env-1>
                                                           #|(append <input-bindings-1>
                                                           <input-vars-1> ;
                                                           <override-tests-1> ;
                                                           <override-vals-1>)|#
                                                           :include '<outputs-list-1>))
                                          (run-2 (svtv-run (<svtv-2>)
                                                           <env-2>
                                                           #|(append <input-bindings-2>
                                                           <input-vars-2> ;
                                                           <override-tests-2> ;
                                                           <override-vals-2>)|#
                                                           :include '<outputs-list-2>))
                                          ((svassocs <outputs-1>) run-1)
                                          ((svassocs <outputs-2>) run-2))
                                       (and <integerp-concls>
                                            <concl>)))
                            <args>)))
    (acl2::template-subst
     template
     :atom-alist `((<defthm> . ,x.lemma-defthm)
                   (<hyp> . ,x.hyp)
                   (<concl> . ,x.concl)
                   (<svtv-1> . ,x.svtv-1)
                   (<svtv-2> . ,x.svtv-2)

                   (<env-1>
                    . ,(svtv-equiv-thm-normalize-fixed-env
                        `(append
                          ;; <input-bindings-1>
                          (list ,@(svtv-genthm-input-var-bindings-alist-termlist x.input-var-bindings-1)
                                ,@(svtv-genthm-input-var-bindings-alist-termlist x.override-var-bindings-1))
                          ;; <input-vars-1>
                          (list . ,(svtv-equiv-thm-input-vars-to-alist x.input-vars-1 x.pkg-sym 1))
                          ;; <override-tests-1>
                          ',(svtv-equiv-thm-override-test-alist
                             (append x.override-vars-1 (strip-cars x.override-var-bindings-1))
                             x.triples-val-1 x.triples-name-1)
                          ;; <override-vals-1>
                          (list . ,(svtv-equiv-thm-input-vars-to-alist x.override-vars-1 x.pkg-sym 1)))))
                   (<env-2>
                    . ,(svtv-equiv-thm-normalize-fixed-env
                        `(append
                          ;; <input-bindings-2>
                          (list ,@(svtv-genthm-input-var-bindings-alist-termlist x.input-var-bindings-2)
                                ,@(svtv-genthm-input-var-bindings-alist-termlist x.override-var-bindings-2))
                          ;; <input-vars-2>
                          (list . ,(svtv-equiv-thm-input-vars-to-alist x.input-vars-2 x.pkg-sym 2))
                          ;; <override-tests-2>
                          ',(svtv-equiv-thm-override-test-alist
                             (append x.override-vars-2 (strip-cars x.override-var-bindings-2))
                             x.triples-val-2 x.triples-name-2)
                          ;; <override-vals-2>
                          (list . ,(svtv-equiv-thm-input-vars-to-alist x.override-vars-2 x.pkg-sym 2)))))

                   ;; (<input-bindings-1>
                   ;;  . (list ,@(svtv-genthm-input-var-bindings-alist-termlist x.input-var-bindings-1)
                   ;;          ,@(svtv-genthm-input-var-bindings-alist-termlist x.override-var-bindings-1)))
                   ;; (<input-bindings-2>
                   ;;  . (list ,@(svtv-genthm-input-var-bindings-alist-termlist x.input-var-bindings-2)
                   ;;          ,@(svtv-genthm-input-var-bindings-alist-termlist x.override-var-bindings-2)))
                   ;; (<input-vars-1> . (list . ,(svtv-equiv-thm-input-vars-to-alist x.input-vars-1 x.pkg-sym 1)))
                   ;; (<input-vars-2> . (list . ,(svtv-equiv-thm-input-vars-to-alist x.input-vars-2 x.pkg-sym 2)))
                   ;; (<override-tests-1> . ',(svtv-equiv-thm-override-test-alist
                   ;;                          (append x.override-vars-1 (strip-cars x.override-var-bindings-1))
                   ;;                          x.triples-val-1 x.triples-name-1))
                   ;; (<override-vals-1> . (list . ,(svtv-equiv-thm-input-vars-to-alist x.override-vars-1 x.pkg-sym 1)))
                   ;; (<override-tests-2> . ',(svtv-equiv-thm-override-test-alist
                   ;;                          (append x.override-vars-2 (strip-cars x.override-var-bindings-2))
                   ;;                          x.triples-val-2 x.triples-name-2))
                   ;; (<override-vals-2> . (list . ,(svtv-equiv-thm-input-vars-to-alist x.override-vars-2 x.pkg-sym 2)))

                   (<outputs-list-1> . ,x.output-vars-1)
                   (<outputs-list-2> . ,x.output-vars-2)
                   )
     :splice-alist `((<outputs-1>
                      . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs x.output-vars-1 x.pkg-sym 1))
                     (<outputs-2>
                      . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs x.output-vars-2 x.pkg-sym 2)) ;;;;
                     (<integerp-concls>
                      . ,(and (not x.no-integerp)
                              (svtv-genthm-integerp-conclusions-aux (append
                                                                     (svtv-equiv-thm-suffix-index-to-vars
                                                                      x.output-vars-1 x.pkg-sym 1)
                                                                     (svtv-equiv-thm-suffix-index-to-vars
                                                                      x.output-vars-2 x.pkg-sym 2)))))
                     (<args> . ,x.lemma-args))
     :str-alist `(("<NAME>" . ,(symbol-name x.name)))
     :pkg-sym x.pkg-sym)))

(defun svtv-equiv-thm-input-binding-hyp-termlist (input-var-bindings pkg-sym index)
  (b* (((when (atom input-var-bindings)) nil)
       ((list name term) (car input-var-bindings)))
    (cons `(equal ,(svtv-equiv-thm-suffix-index-to-var name pkg-sym index) ,term)
          (svtv-equiv-thm-input-binding-hyp-termlist (cdr input-var-bindings) pkg-sym index))))

(defun svtv-equiv-mono-lemma (x i)
  (b* (((svtv-equiv-thm-data x))
       (template '(defthm <name>-<<=-lemma-<i>
                    (b* (((svassocs <input-var-svassocs>
                                    <input-unbound-svassocs>)
                          <env>)
                         ((svassocs <input-var-svassocs-other>
                                    <input-unbound-svassocs-other>)
                          <env-other>)
                         (run-other (svtv-run (<svtv-other>)
                                              <env-other>))
                         ((svassocs <outputs-other>) run-other))
                      (implies (and <input-binding-hyp>
                                    (svex-env-keys-no-1s-p
                                     (svar-override-triplelist->testvars (<triples>)) <env>))
                               (b* ((run (svtv-run (<svtv>) <env>))
                                    ((svassocs <override-svassocs>) run)
                                    (lemma-run (svtv-run (<svtv>)
                                                         <fixed-env>
                                                         #|(append <input-bindings>
                                                         <input-vars>
                                                         <override-tests>
                                                         <override-vals>)|#)))
                                 (svex-env-<<= lemma-run run))))
                    :hints (("goal" :use ((:instance <svtv>-overrides-correct
                                                     (spec-env <env>)
                                                     (lemma-env
                                                      (b* ((?run (svtv-run (<svtv>) <env>))
                                                           ((svassocs <override-svassocs>) run)
                                                           ((svassocs <input-unbound-svassocs>) <env>)
                                                           ((svassocs <input-var-svassocs-other>
                                                                      <input-unbound-svassocs-other>)
                                                            <env-other>)
                                                           (run-other (svtv-run (<svtv-other>)
                                                                                <env-other>))
                                                           ((svassocs <outputs-other>) run-other))
                                                        <fixed-env>
                                                        #|(append <input-bindings>
                                                        <input-vars>
                                                        <override-tests>
                                                        <override-vals>)|#))))
                             :in-theory '((:CONGRUENCE CONS-4VEC-EQUIV-CONGRUENCE-ON-V-UNDER-SVEX-ENV-EQUIV)
                                          (:CONGRUENCE SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENV-<<=-1)
                                          (:DEFINITION 4VEC-EQUIV$INLINE)
                                          (:DEFINITION DOUBLE-REWRITE)
                                          (:DEFINITION NOT)
                                          (:DEFINITION SYNP)
                                          (2VEC-P$INLINE)
                                          (4VEC-FIX$INLINE)
                                          (ALIST-KEYS)
                                          (ATOM)
                                          (BINARY-APPEND)
                                          (<svtv>-NON-TRIPLE-OVERRIDE-TESTS)
                                          (CAR)
                                          (CDR)
                                          (CONS)
                                          (CONSP)
                                          (EQUAL)
                                          (HONS-DUPS-P)
                                          (NOT)
                                          (SVAR-FIX$INLINE)
                                          (SVAR-P)
                                          (SVARLIST-FILTER)
                                          (TRUE-LIST-FIX)
                                          (:META HONS-INTERSECTION-FORCE-EXECUTE)
                                          (:META HONS-SET-DIFF-FORCE-EXECUTE)
                                          (:REWRITE 4VEC-<<=-2VEC)
                                          (:REWRITE 4VEC-FIX-OF-4VEC)
                                          (:REWRITE 4VEC-FIX-UNDER-4VEC-EQUIV)
                                          (:REWRITE 4VEC-P-OF-SVEX-ENV-LOOKUP)
                                          (:REWRITE ACL2::ALIST-KEYS-OF-CONS)
                                          (:REWRITE ACL2::APPEND-OF-CONS)
                                          (:REWRITE ACL2::APPEND-OF-NIL)
                                          (:REWRITE ACL2::APPEND-WHEN-NOT-CONSP)
                                          (:REWRITE CAR-CONS)
                                          (:REWRITE CDR-CONS)
                                          (:REWRITE ACL2::LIST-FIX-OF-CONS)
                                          (:REWRITE SVARLIST-FIX-WHEN-SVARLIST-P)
                                          (:REWRITE SVARLIST-P-OF-SVAR-OVERRIDE-TRIPLELIST->VALVARS)
                                          (:REWRITE SVARLIST-P-OF-SVAR-OVERRIDE-TRIPLELIST-OVERRIDE-VARS)
                                          (:REWRITE SVEX-ENV-<<=-EACH-OF-CONS)
                                          (:REWRITE SVEX-ENV-<<=-EACH-OF-NIL)
                                          (:REWRITE SVEX-ENV-<<=-IS-SVEX-ENV-<<=-EACH-WHEN-NO-DUPLICATE-KEYS)
                                          (:REWRITE SVEX-ENV-<<=-NECC)
                                          (:REWRITE SVEX-ENV-<<=-REFL)
                                          (:REWRITE SVEX-ENV-EXTRACT-OF-CONS)
                                          (:REWRITE SVEX-ENV-EXTRACT-OF-NIL)
                                          (:REWRITE SVEX-ENV-EXTRACT-OF-VARIABLE-FREE-TERM)
                                          (:REWRITE SVEX-ENV-LOOKUP-OF-CONS)
                                          (:REWRITE SVEX-ENV-REMOVEKEYS-OF-VARIABLE-FREE-TERM)
                                          (:REWRITE SVEX-ENVS-AGREE-OF-NIL)
                                          (:TYPE-PRESCRIPTION SVEX-ENV-<<=)
                                          (:TYPE-PRESCRIPTION SVEX-ENV-LOOKUP)
                                          (svar-override-triple->refvar)
                                          svex-env-fix-when-svex-env-p
                                          acl2::svex-env-p-of-svtv-run
                                          alist-keys-of-svtv-run
                                          <svtv>-refvars-subset-of-output-vars
                                          lookup-of-svar-override-triplelist-map-refs-to-values
                                          svar-override-triplelist-lookup-valvar-force-execute))))))
    (acl2::template-subst
     template
     :atom-alist
     (if (equal i 1)
         `((<fixed-env>
            . ,(svtv-equiv-thm-normalize-fixed-env
                `(append
                  ;; <input-bindings-1>
                  (list ,@(svtv-genthm-input-var-bindings-alist-termlist x.input-var-bindings-1)
                        ,@(svtv-genthm-input-var-bindings-alist-termlist x.override-var-bindings-1))
                  ;; <input-vars-1>
                  (list . ,(svtv-equiv-thm-input-vars-to-alist x.input-vars-1 x.pkg-sym 1))
                  ;; <override-tests-1>
                  ',(svtv-equiv-thm-override-test-alist
                     (append x.override-vars-1 (strip-cars x.override-var-bindings-1))
                     x.triples-val-1 x.triples-name-1)
                  ;; <override-vals-1>
                  (list . ,(svtv-equiv-thm-input-vars-to-alist x.override-vars-1 x.pkg-sym 1)))))

           (<env> . env-1)
           (<env-other> . env-2)
           (<svtv> . ,x.svtv-1)
           (<svtv-other> . ,x.svtv-2)
           (<outputs-list-other> . ,x.output-vars-2)
           (<triples> . ,x.triples-name-1)
           ;; (<input-bindings> . (list ,@(svtv-genthm-input-var-bindings-alist-termlist x.input-var-bindings-1)
           ;;                           ,@(svtv-genthm-input-var-bindings-alist-termlist x.override-var-bindings-1)))
           ;; (<input-vars> . (list . ,(svtv-equiv-thm-input-vars-to-alist  x.input-vars-1 x.pkg-sym 1)))
           ;; (<override-tests> . ',(svtv-equiv-thm-override-test-alist
           ;;                        (append x.override-vars-1 (strip-cars x.override-var-bindings-1))
           ;;                        x.triples-val-1 x.triples-name-1))
           ;; (<override-vals> . (list . ,(svtv-equiv-thm-input-vars-to-alist x.override-vars-1 x.pkg-sym 1)))
           )
       `((<fixed-env>
          . ,(svtv-equiv-thm-normalize-fixed-env
              `(append
                ;; <input-bindings-2>
                (list ,@(svtv-genthm-input-var-bindings-alist-termlist x.input-var-bindings-2)
                      ,@(svtv-genthm-input-var-bindings-alist-termlist x.override-var-bindings-2))
                ;; <input-vars-2>
                (list . ,(svtv-equiv-thm-input-vars-to-alist x.input-vars-2 x.pkg-sym 2))
                ;; <override-tests-2>
                ',(svtv-equiv-thm-override-test-alist
                   (append x.override-vars-2 (strip-cars x.override-var-bindings-2))
                   x.triples-val-2 x.triples-name-2)
                ;; <override-vals-2>
                (list . ,(svtv-equiv-thm-input-vars-to-alist x.override-vars-2 x.pkg-sym 2)))))
         (<env> . env-2)
         (<env-other> . env-1)
         (<svtv> . ,x.svtv-2)
         (<svtv-other> . ,x.svtv-1)
         (<outputs-list-other> . ,x.output-vars-1)
         (<triples> . ,x.triples-name-2)

         ;; (<input-bindings> . (list ,@(svtv-genthm-input-var-bindings-alist-termlist x.input-var-bindings-2)
         ;;                           ,@(svtv-genthm-input-var-bindings-alist-termlist x.override-var-bindings-2)))
         ;; (<input-vars> . (list . ,(svtv-equiv-thm-input-vars-to-alist x.input-vars-2 x.pkg-sym 2)))
         ;; (<override-tests> . ',(svtv-equiv-thm-override-test-alist
         ;;                        (append x.override-vars-2 (strip-cars x.override-var-bindings-2))
         ;;                        x.triples-val-2 x.triples-name-2))
         ;; (<override-vals> . (list . ,(svtv-equiv-thm-input-vars-to-alist x.override-vars-2 x.pkg-sym 2)))
         ))
     :splice-alist
     (if (equal i 1)
         `((<input-var-svassocs> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs
                                     (append (strip-cars x.input-var-bindings-1)
                                             (strip-cars x.override-var-bindings-1))
                                     x.pkg-sym 1))
           (<input-var-svassocs-other> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs
                                           (append (strip-cars x.input-var-bindings-2)
                                                   (strip-cars x.override-var-bindings-2))
                                           x.pkg-sym 2))
           (<input-unbound-svassocs> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs
                                         x.input-vars-1 x.pkg-sym 1))
           (<input-unbound-svassocs-other> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs
                                               x.input-vars-2 x.pkg-sym 2))

           (<outputs-other> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs
                                (append x.output-vars-2 x.override-vars-2)
                                x.pkg-sym 2))

           (<input-binding-hyp> .  ,(svtv-equiv-thm-input-binding-hyp-termlist
                                     (append x.input-var-bindings-1 x.override-var-bindings-1)
                                     x.pkg-sym 1))
           (<override-svassocs> . ,(svtv-equiv-thm-override-svassocs x.override-vars-1 x.triples-val-1 x.triples-name-1 x.pkg-sym 1)))
       `((<input-var-svassocs> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs
                                   (append (strip-cars x.input-var-bindings-2)
                                           (strip-cars x.override-var-bindings-2))
                                   x.pkg-sym 2))
         (<input-var-svassocs-other> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs
                                         (append (strip-cars x.input-var-bindings-1)
                                                 (strip-cars x.override-var-bindings-1))
                                         x.pkg-sym 1))
         (<outputs-other> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs
                              (append x.output-vars-1 x.override-vars-1)
                              x.pkg-sym 1))
         (<input-unbound-svassocs> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs
                                       x.input-vars-2 x.pkg-sym 2))
         (<input-unbound-svassocs-other> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs
                                             x.input-vars-1 x.pkg-sym 1))
         (<input-binding-hyp> .  ,(svtv-equiv-thm-input-binding-hyp-termlist
                                   (append x.input-var-bindings-2 x.override-var-bindings-2)
                                   x.pkg-sym 2))
         (<override-svassocs> . ,(svtv-equiv-thm-override-svassocs x.override-vars-2 x.triples-val-2 x.triples-name-2 x.pkg-sym 2))))
     :str-alist `(("<I>" . ,(str::int-to-dec-string i))
                  ("<NAME>" . ,(symbol-name x.name))
                  ("<SVTV>" . ,(symbol-name (if (equal i 1) x.svtv-1 x.svtv-2))))
     :pkg-sym x.pkg-sym)))

(defun svtv-equiv-thm-input-var-instantiation (input-vars pkg-sym index)
  (if (atom input-vars)
      nil
    (cons `(,(svtv-equiv-thm-suffix-index-to-var (car input-vars) pkg-sym index)
            (svex-env-lookup ',(car input-vars)
                             ,(if (equal index 1) 'env-1 'env-2)))
          (svtv-equiv-thm-input-var-instantiation (cdr input-vars) pkg-sym index))))

(defun svtv-equiv-thm-override-var-instantiation (override-vars svtv pkg-sym index)
  (if (atom override-vars)
      nil
    (cons `(,(svtv-equiv-thm-suffix-index-to-var (car override-vars) pkg-sym index)
            (svex-env-lookup ',(car override-vars) (svtv-run (,svtv) ,(if (equal index 1) 'env-1 'env-2))))
          (svtv-equiv-thm-override-var-instantiation (cdr override-vars) svtv pkg-sym index))))

(defun svtv-equiv-thm-final-thm (x)
  (b* (((svtv-equiv-thm-data x))
       (template `(defthm <name>
                    (b* ((:@ :free-env-var-1
                             ((svassocs <input-var-svassocs-1>) env-1)
                             (run-1 (svtv-run (<svtv-1>) env-1))
                             ((svassocs <override-svassocs-1> <outputs-1>) run-1))
                         (:@ (not :free-env-var-1)
                             (run-1 (svtv-run (<svtv-1>)
                                              <env-1>
                                              #|(append <input-bindings-1>
                                              <input-vars-1> ; ;
                                              <override-tests-1> ; ;
                                              <override-vals-1>)|#
                                              ;; :include '<outputs-list-1>
                                              ))
                             ((svassocs <outputs-1>) run-1))
                         (:@ :free-env-var-2
                             ((svassocs <input-var-svassocs-2>) env-2)
                             (run-2 (svtv-run (<svtv-2>) env-2))
                             ((svassocs <override-svassocs-2> <outputs-2>) run-2))
                         (:@ (not :free-env-var-2)
                             (run-2 (svtv-run (<svtv-2>)
                                              <env-2>
                                              #|(append <input-bindings-2>
                                              <input-vars-2> ; ;
                                              <override-tests-2> ; ;
                                              <override-vals-2>)|#
                                              ;; :include '<outputs-list-2>
                                              ))
                             ((svassocs <outputs-2>) run-2)))
                      (implies (and ;;<integerp-concls>
                                    <hyp>
                                    <input-binding-hyp>
                                    (:@ :free-env-var-1
                                        (sv::svtv-override-triplemaplist-envs-match
                                         (<triples-1>) sv::env-1 nil))
                                    (:@ :free-env-var-2
                                        (sv::svtv-override-triplemaplist-envs-match
                                         (<triples-2>) sv::env-2 nil)))
                               <concl>))
                    :hints (:@ :no-lemmas <hints>)
                    (:@ (not :no-lemmas)
                        (("goal"
                          :in-theory (e/d** ((:ruleset sv::svtv-generalized-thm-rules)
                                             svarlist-p-of-<svtv-1>-input-vars
                                             svarlist-p-of-<svtv-2>-input-vars
                                             (BINARY-APPEND)
                                             (CONS)
                                             (INTEGERP)
                                             (MEMBER-EQUAL)
                                             (SVAR-FIX$INLINE)
                                             (TRUE-LIST-FIX)
                                             (:REWRITE ACL2::APPEND-OF-CONS)
                                             (:REWRITE ACL2::APPEND-OF-NIL)
                                             (:REWRITE ACL2::APPEND-WHEN-NOT-CONSP)
                                             (:REWRITE ACL2::LIST-FIX-OF-CONS)
                                             (:REWRITE SVEX-ENV-LOOKUP-IN-SVTV-RUN-WITH-INCLUDE)
                                             (:REWRITE SVEX-ENV-LOOKUP-WHEN-INTEGERP-AND-<<=)
                                             (:TYPE-PRESCRIPTION SVEX-ENV-<<=)
                                             (:TYPE-PRESCRIPTION SVEX-ENV-LOOKUP)
                                             <enable>))
                          :use ((:instance <name>-equiv-lemma
                                           (:@ :free-env-var-1
                                               <override-var-instantiation-1>
                                               <input-var-instantiation-1>)
                                           (:@ :free-env-var-2
                                               <override-var-instantiation-2>
                                               <input-var-instantiation-2>))
                                (:@ :free-env-var-1
                                    (:instance <svtv-1>-refines-<svtv-1>
                                               (spec-pipe-env env-1)
                                               (pipe-env (b* (((svassocs <input-var-svassocs-1>) env-1)
                                                              (run-1 (svtv-run (<svtv-1>) env-1))
                                                              ((svassocs <override-svassocs-1> <outputs-1>) run-1))
                                                           <env-1>))))
                                (:@ :free-env-var-2
                                    (:instance <svtv-2>-refines-<svtv-2>
                                               (spec-pipe-env env-2)
                                               (pipe-env
                                                (b* ((:@ :free-env-var-1
                                                         ((svassocs <input-var-svassocs-1>) env-1)
                                                         (run-1 (svtv-run (<svtv-1>) env-1))
                                                         ((svassocs <override-svassocs-1> <outputs-1>) run-1))
                                                     (:@ (not :free-env-var-1)
                                                         (run-1 (svtv-run (<svtv-1>)
                                                                          <env-1>
                                                                          #|(append <input-bindings-1>
                                                                          <input-vars-1> ; ; ;
                                                                          <override-tests-1> ; ; ;
                                                                          <override-vals-1>)|#
                                                                          ;; :include '<outputs-list-1>
                                                                          ))
                                                         ((svassocs <outputs-1>) run-1))
                                                     ((svassocs <input-var-svassocs-2>) env-2)
                                                     (run-2 (svtv-run (<svtv-2>) env-2))
                                                     ((svassocs <override-svassocs-2> <outputs-2>) run-2))
                                                  <env-2>)))))))
                        ))))
    (acl2::template-subst
     template
     :atom-alist
     `((<hyp> . ,x.hyp)
       (<concl> . ,x.concl)
       (<svtv-1> . ,x.svtv-1)
       (<svtv-2> . ,x.svtv-2)
       (<triples-1> . ,x.triples-name-1)
       (<triples-2> . ,x.triples-name-2)
       (<hints> . ,x.hints)

       (<env-1>
        . ,(svtv-equiv-thm-normalize-fixed-env
            `(append
              ;; <input-bindings-1>
              (list ,@(svtv-genthm-input-var-bindings-alist-termlist x.input-var-bindings-1)
                    ,@(svtv-genthm-input-var-bindings-alist-termlist x.override-var-bindings-1))
              ;; <input-vars-1>
              (list . ,(svtv-equiv-thm-input-vars-to-alist x.input-vars-1 x.pkg-sym 1))
              ;; <override-tests-1>
              ',(svtv-equiv-thm-override-test-alist
                 (append x.override-vars-1 (strip-cars x.override-var-bindings-1))
                 x.triples-val-1 x.triples-name-1)
              ;; <override-vals-1>
              (list . ,(svtv-equiv-thm-input-vars-to-alist x.override-vars-1 x.pkg-sym 1)))))
       (<env-2>
        . ,(svtv-equiv-thm-normalize-fixed-env
            `(append
              ;; <input-bindings-2>
              (list ,@(svtv-genthm-input-var-bindings-alist-termlist x.input-var-bindings-2)
                    ,@(svtv-genthm-input-var-bindings-alist-termlist x.override-var-bindings-2))
              ;; <input-vars-2>
              (list . ,(svtv-equiv-thm-input-vars-to-alist x.input-vars-2 x.pkg-sym 2))
              ;; <override-tests-2>
              ',(svtv-equiv-thm-override-test-alist
                 (append x.override-vars-2 (strip-cars x.override-var-bindings-2))
                 x.triples-val-2 x.triples-name-2)
              ;; <override-vals-2>
              (list . ,(svtv-equiv-thm-input-vars-to-alist x.override-vars-2 x.pkg-sym 2)))))

       ;; (<outputs-list-2> . ,x.output-vars-2)
       ;; (<input-bindings-2>
       ;;  . (list ,@(svtv-genthm-input-var-bindings-alist-termlist x.input-var-bindings-2)
       ;;          ,@(svtv-genthm-input-var-bindings-alist-termlist x.override-var-bindings-2)))
       ;; (<input-vars-2> . (list . ,(svtv-equiv-thm-input-vars-to-alist x.input-vars-2 x.pkg-sym 2)))
       ;; (<override-tests-2> . ',(svtv-equiv-thm-override-test-alist
       ;;                          (append x.override-vars-2 (strip-cars x.override-var-bindings-2))
       ;;                          x.triples-val-2 x.triples-name-2))
       ;; (<override-vals-2> . (list . ,(svtv-equiv-thm-input-vars-to-alist x.override-vars-2 x.pkg-sym 2)))

       ;; (<outputs-list-1> . ,x.output-vars-1)
       ;; (<input-bindings-1>
       ;;  . (list ,@(svtv-genthm-input-var-bindings-alist-termlist x.input-var-bindings-1)
       ;;          ,@(svtv-genthm-input-var-bindings-alist-termlist x.override-var-bindings-1)))
       ;; (<input-vars-1> . (list . ,(svtv-equiv-thm-input-vars-to-alist x.input-vars-1 x.pkg-sym 1)))
       ;; (<override-tests-1> . ',(svtv-equiv-thm-override-test-alist
       ;;                          (append x.override-vars-1 (strip-cars x.override-var-bindings-1))
       ;;                          x.triples-val-1 x.triples-name-1))
       ;; (<override-vals-1> . (list . ,(svtv-equiv-thm-input-vars-to-alist x.override-vars-1 x.pkg-sym 1)))
       )
     :splice-alist
     `((<input-var-svassocs-1> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs
                                   (append x.input-vars-1 (strip-cars x.input-var-bindings-1))
                                   x.pkg-sym
                                   1))
       (<input-var-svassocs-2> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs
                                   (append x.input-vars-2 (strip-cars x.input-var-bindings-2))
                                   x.pkg-sym
                                   2))

       (<override-svassocs-1> . ,(svtv-equiv-thm-override-svassocs
                                  (append x.override-vars-1 (strip-cars x.override-var-bindings-1))
                                  x.triples-val-1 x.triples-name-1 x.pkg-sym 1))
       (<override-svassocs-2> . ,(svtv-equiv-thm-override-svassocs
                                  (append x.override-vars-2 (strip-cars x.override-var-bindings-2))
                                  x.triples-val-2 x.triples-name-2 x.pkg-sym 2))

       (<input-binding-hyp> .  ,(append
                                 (and x.free-env-var-1
                                      (svtv-equiv-thm-input-binding-hyp-termlist x.input-var-bindings-1 x.pkg-sym 1))
                                 (and x.free-env-var-1
                                      (svtv-equiv-thm-input-binding-hyp-termlist x.override-var-bindings-1 x.pkg-sym 1))
                                 (and x.free-env-var-2
                                      (svtv-equiv-thm-input-binding-hyp-termlist x.input-var-bindings-2 x.pkg-sym 2))
                                 (and x.free-env-var-2
                                      (svtv-equiv-thm-input-binding-hyp-termlist x.override-var-bindings-2 x.pkg-sym 2))))

       (<input-var-instantiation-1> . ,(svtv-equiv-thm-input-var-instantiation x.input-vars-1 x.pkg-sym 1))
       (<input-var-instantiation-2> . ,(svtv-equiv-thm-input-var-instantiation x.input-vars-2 x.pkg-sym 2))

       (<override-var-instantiation-1> . ,(svtv-equiv-thm-override-var-instantiation x.override-vars-1 x.svtv-1 x.pkg-sym 1))
       (<override-var-instantiation-2> . ,(svtv-equiv-thm-override-var-instantiation x.override-vars-2 x.svtv-2 x.pkg-sym 2))

       (<outputs-1> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs x.output-vars-1 x.pkg-sym 1))
       (<outputs-2> . ,(svtv-equiv-thm-suffix-index-to-vars-for-svassocs x.output-vars-2 x.pkg-sym 2))
       (<enable> . ,x.enable)
       #|(<integerp-concl-hyps>
        . ,(and (equal x.no-integerp :in-hyps)
                (svtv-genthm-integerp-conclusions-aux (append
                                                       (svtv-equiv-thm-suffix-index-to-vars
                                                        x.output-vars-1 x.pkg-sym 1)
                                                       (svtv-equiv-thm-suffix-index-to-vars
                                                        x.output-vars-2 x.pkg-sym 2)))))|#

       )
     :str-alist `(("<NAME>" . ,(symbol-name x.name))
                  ("<SVTV-1>" . ,(symbol-name x.svtv-1))
                  ("<SVTV-2>" . ,(symbol-name x.svtv-2)))
     :features (append (and x.no-lemmas '(:no-lemmas))
                       (and x.free-env-var-2 '(:free-env-var-2))
                       (and x.free-env-var-1 '(:free-env-var-1)))
     :pkg-sym x.pkg-sym)))

(defun svtv-equiv-thm-precheck-for-errors (x state)
  (declare (xargs :stobjs (state)))
  (b* (((svtv-equiv-thm-data x))
       ;; since all-vars test is performed on concl and hyp, better translate them first.
       ((acl2::er x.concl)
        (acl2::translate x.concl t t nil 'svtv-equiv-thm-precheck-for-errors (w state) state))
       ((acl2::er x.hyp)
        (acl2::translate x.hyp t t nil 'svtv-equiv-thm-precheck-for-errors (w state) state))
       )
    (value
     (or (and x.override-var-bindings-1
              x.free-env-var-1
              (msg "Setting override-var-bindings-1 when free-env-var-1 is enabled is not supported (yet)."))
         (and x.override-var-bindings-2
              x.free-env-var-2
              (msg "Setting override-var-bindings-2 when free-env-var-2 is enabled is not supported (yet)."))
         (svtv-genthm-check-variable-list "Override-vars-1" x.override-vars-1)
         (svtv-genthm-check-variable-list "Override-vars-2" x.override-vars-2)
         (svtv-genthm-check-variable-list "Input-vars-1" x.input-vars-1)
         (svtv-genthm-check-variable-list "Input-vars-2" x.input-vars-2)
         (svtv-genthm-check-variable-list "Output-vars-1" x.output-vars-1)
         (svtv-genthm-check-variable-list "Output-vars-2" x.output-vars-2)
         (and (not (acl2::doublet-listp x.input-var-bindings-1))
              (msg "Input-var-bindings-1 must be a list of two-element lists"))
         (and (not (acl2::doublet-listp x.input-var-bindings-2))
              (msg "Input-var-bindings-2 must be a list of two-element lists"))
         (and (not (acl2::doublet-listp x.override-var-bindings-1))
              (msg "Override-var-bindings-1 must be a list of two-element lists"))
         (and (not (acl2::doublet-listp x.override-var-bindings-2))
              (msg "Override-var-bindings-2 must be a list of two-element lists"))
         (svtv-genthm-check-variable-list "Keys of input-var-bindings-1"
                                          (strip-cars x.input-var-bindings-1))
         (svtv-genthm-check-variable-list "Keys of input-var-bindings-2"
                                          (strip-cars x.input-var-bindings-2))
         (svtv-genthm-check-variable-list "Keys of override-var-bindings-1"
                                          (strip-cars x.override-var-bindings-1))
         (svtv-genthm-check-variable-list "Keys of override-var-bindings-2"
                                          (strip-cars x.override-var-bindings-2))
         (let ((dup-tail (acl2::hons-dups-p (append x.input-vars-1
                                                    x.override-vars-1
                                                    (strip-cars x.input-var-bindings-1)
                                                    (strip-cars x.override-var-bindings-1)
                                                    x.output-vars-1))))
           (and dup-tail
                (msg "Input, override, and output variables should not ~
                     intersect, but ~x0 is present in more than one for svtv-1"
                     (car dup-tail))))
         (let ((dup-tail (acl2::hons-dups-p (append x.input-vars-2
                                                    x.override-vars-2
                                                    (strip-cars x.input-var-bindings-2)
                                                    (strip-cars x.override-var-bindings-2)
                                                    x.output-vars-2))))
           (and dup-tail
                (msg "Input, override, and output variables should not ~
                     intersect, but ~x0 is present in more than one for svtv-2"
                     (car dup-tail))))
         (let ((dup-tail (acl2::hons-dups-p (append x.input-vars-1
                                                    (strip-cars x.input-var-bindings-1)
                                                    (strip-cars x.override-var-bindings-1)
                                                    x.output-vars-1
                                                    x.override-vars-1
                                                    (acl2::all-vars x.concl)))))
           (and dup-tail
                (msg "Concl should not include a variable with the same name as ~
                     inputs, outputs, and overrides. Instead of using ~x0, use ~x0-1 instead."
                     (car dup-tail))))
         (let ((dup-tail (acl2::hons-dups-p (append x.input-vars-2
                                                    (strip-cars x.input-var-bindings-2)
                                                    (strip-cars x.override-var-bindings-2)
                                                    x.output-vars-2
                                                    x.override-vars-2
                                                    (acl2::all-vars x.concl)))))
           (and dup-tail
                (msg "Concl should not include a variable with the same name as ~
                     inputs, outputs, and overrides. Instead of using ~x0, use ~x0-2 instead."
                     (car dup-tail))))
         (let ((dup-tail (acl2::hons-dups-p (append x.input-vars-1
                                                    (strip-cars x.input-var-bindings-1)
                                                    (strip-cars x.override-var-bindings-1)
                                                    x.output-vars-1
                                                    x.override-vars-1
                                                    (acl2::all-vars x.hyp)))))
           (and dup-tail
                (msg "Hyp should not include a variable with the same name as ~
                     inputs, outputs, and overrides. Instead of using ~x0, use ~x0-1 instead."
                     (car dup-tail))))
         (let ((dup-tail (acl2::hons-dups-p (append x.input-vars-2
                                                    (strip-cars x.input-var-bindings-2)
                                                    (strip-cars x.override-var-bindings-2)
                                                    x.output-vars-2
                                                    x.override-vars-2
                                                    (acl2::all-vars x.hyp)))))
           (and dup-tail
                (msg "Hyp should not include a variable with the same name as ~
                     inputs, outputs, and overrides. Instead of using ~x0, use ~x0-2 instead."
                     (car dup-tail))))))))

(defun svtv-equiv-thm-events (x state)
  (declare (xargs :stobjs (state)))
  (b* (((svtv-equiv-thm-data x))
       ((acl2::er err) (svtv-equiv-thm-precheck-for-errors x state))
       ((when err) (value (er hard? `(def-svtv-equiv-thm ,x.name) "Error: ~@0" err))))
    (value
     `(defsection ,x.name
        ,@(and (not x.no-lemmas)
               `((local ,(svtv-equiv-thm-initial-override-lemma x))
                 ;; ,@(and x.free-env-var-1 `((local ,(svtv-equiv-mono-lemma x 1))))
                 ;; ,@(and x.free-env-var-2 `((local ,(svtv-equiv-mono-lemma x 2))))
                 ))
        ,(svtv-equiv-thm-final-thm x)))))

(defun svtv-equiv-thm-fn (name args state)
  (declare (xargs :stobjs state))
  (b* ((defaults (table-alist 'svtv-equiv-thm-defaults (w state)))
       (ctx `(def-svtv-equiv-thm ,name))
       ((std::extract-keyword-args
         :defaults defaults
         :ctx ctx
         svtv-1
         svtv-2
         override-vars-1
         override-vars-2
         input-vars-1
         input-vars-2
         output-vars-1
         output-vars-2
         input-var-bindings-1
         input-var-bindings-2
         override-var-bindings-1
         override-var-bindings-2
         enable
         unsigned-byte-hyps
         no-integerp
         (hyp 't)
         concl
         (lemma-defthm 'fgl::def-fgl-thm)
         lemma-args
         no-lemmas
         hints
         (free-env-var-1 't)
         (free-env-var-2 't)
         (pkg-sym name))
        args)

       (triples-1 (acl2::template-subst
                   '<svtv>-triplemaplist
                   :str-alist `(("<SVTV>" . ,(symbol-name svtv-1)))
                   :pkg-sym pkg-sym))
       ((mv err triplemaps-val-1) (magic-ev-fncall triples-1 nil state t t))
       ;; if triples for the second svtv doesn't exist for the (not free-env-var-1) case,
       ;; then we don't need it anyway so don't throw an error.
       ((when (and free-env-var-1 err)) (er soft ctx "Couldn't evaluate ~x0" (list triples-1)))
       (triples-val-1 (if err nil
                        (svtv-override-triplelist-val-alist
                         (svtv-override-triplemaplist-to-triplelist triplemaps-val-1))))
       (triples-2 (acl2::template-subst
                   '<svtv>-triplemaplist
                   :str-alist `(("<SVTV>" . ,(symbol-name svtv-2)))
                   :pkg-sym pkg-sym))
       ((mv err triplemaps-val-2) (magic-ev-fncall triples-2 nil state t t))
       ;; if triples for the second svtv doesn't exist for the (not free-env-var-2) case,
       ;; then we don't need it anyway so don't throw an error.
       ((when (and free-env-var-2 err)) (er soft ctx "Couldn't evaluate ~x0" (list triples-2)))
       (triples-val-2 (if err nil
                        (svtv-override-triplelist-val-alist
                         (svtv-override-triplemaplist-to-triplelist triplemaps-val-2))))

       ((mv err svtv-val-1) (magic-ev-fncall svtv-1 nil state t t))
       ((when err) (er soft ctx "Couldn't evaluate ~x0" (list svtv-1)))
       ((mv err svtv-val-2) (magic-ev-fncall svtv-2 nil state t t))
       ((when err) (er soft ctx "Couldn't evaluate ~x0" (list svtv-2)))
       (hyp (if unsigned-byte-hyps
                (b* ((inmasks-1 (svtv->inmasks svtv-val-1))
                     (inmasks-2 (svtv->inmasks svtv-val-2))
                     (inputs-1 (append override-vars-1 input-vars-1))
                     (inputs-2 (append override-vars-2 input-vars-2))
                     (masks-1 (acl2::fal-extract inputs-1 inmasks-1))
                     (masks-2 (acl2::fal-extract inputs-2 inmasks-2))
                     )
                  `(and ,@(svtv-equiv-thm-suffix-index-to-hyps (svtv-unsigned-byte-hyps masks-1) pkg-sym 1)
                        ,@(svtv-equiv-thm-suffix-index-to-hyps (svtv-unsigned-byte-hyps masks-2) pkg-sym 2)
                        ,hyp))
              hyp))

       (input-vars-1 (if (equal input-vars-1 :all)
                         (b* ((all-ins (svtv->ins svtv-val-1))
                              (triplelist (svtv-override-triplemaplist-to-triplelist triplemaps-val-1))
                              (conditional-triples (svtv-override-triplelist-keep-conditional triplelist))
                              (ovr-controls (svexlist-collect-vars (svtv-override-triplelist->tests conditional-triples)))
                              (conditional-ovr-signals (svexlist-collect-vars (svtv-override-triplelist->vals conditional-triples)))
                              ;; Conditional overrides/override tests should not be treated as input vars.
                              ;; Unconditional overrides should be treated as inputs UNLESS they're explicitly listed in the override-vars/override-var-bindings.
                              (ovr-signals (append override-vars-1
                                                   (alist-keys override-var-bindings-1)
                                                   conditional-ovr-signals))
                              (all-ins (acl2::hons-set-diff all-ins
                                                            (append ovr-controls ovr-signals
                                                                    (alist-keys input-var-bindings-1))))
                              (all-ins (remove-duplicates-equal all-ins)))
                           all-ins)
                       input-vars-1))

       (input-vars-2 (if (equal input-vars-2 :all)
                         (b* ((all-ins (svtv->ins svtv-val-2))
                              (triplelist (svtv-override-triplemaplist-to-triplelist triplemaps-val-2))
                              (conditional-triples (svtv-override-triplelist-keep-conditional triplelist))
                              (ovr-controls (svexlist-collect-vars (svtv-override-triplelist->tests conditional-triples)))
                              (conditional-ovr-signals (svexlist-collect-vars (svtv-override-triplelist->vals conditional-triples)))
                              ;; Conditional overrides/override tests should not be treated as input vars.
                              ;; Unconditional overrides should be treated as inputs UNLESS they're explicitly listed in the override-vars/override-var-bindings.
                              (ovr-signals (append override-vars-2
                                                   (alist-keys override-var-bindings-2)
                                                   conditional-ovr-signals))
                              (all-ins (acl2::hons-set-diff all-ins
                                                            (append ovr-controls ovr-signals
                                                                    (alist-keys input-var-bindings-2))))
                              (all-ins (remove-duplicates-equal all-ins)))
                           all-ins)
                       input-vars-2))

       )
    (svtv-equiv-thm-events
     (make-svtv-equiv-thm-data
      :name name
      :override-vars-1 override-vars-1
      :override-vars-2 override-vars-2
      :input-vars-1 input-vars-1
      :input-vars-2 input-vars-2
      :output-vars-1 output-vars-1
      :output-vars-2 output-vars-2
      :input-var-bindings-1 input-var-bindings-1
      :input-var-bindings-2 input-var-bindings-2
      :override-var-bindings-1 override-var-bindings-1
      :override-var-bindings-2 override-var-bindings-2
      :enable enable
      :hyp hyp
      :concl concl
      :svtv-1 svtv-1
      :svtv-2 svtv-2
      :lemma-defthm lemma-defthm
      :lemma-args lemma-args
      :triples-name-1 triples-1
      :triples-val-1 triples-val-1
      :triples-name-2 triples-2
      :triples-val-2 triples-val-2
      :hints hints
      :free-env-var-1 free-env-var-1
      :free-env-var-2 free-env-var-2
      :no-lemmas no-lemmas
      :no-integerp no-integerp
      :pkg-sym pkg-sym)
     state)))

(defmacro def-svtv-equiv-thm (name &rest args)
  `(make-event (svtv-equiv-thm-fn ',name ',args state)))

(logic)
